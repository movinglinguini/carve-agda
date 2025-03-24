open import Data.Vec
open import Data.Nat
open import Data.Product

module CARVe.Context 
  (Proposition : Set)
  (Tag : Set)
  (_∙_⇒_ : Tag → Tag → Tag → Set)
  where

  private
    variable
      n m : ℕ
      t t₁ t₂ : Tag
      A B : Proposition

  TaggedProposition = Proposition × Tag

  -- A context is a vector of propositions
  Context : ∀ ( n : ℕ ) → Set
  Context n = Vec (Proposition × Tag) n

  private
    variable
      Δ Δ₁ Δ₂ Δ' : Context n

  {- Definition of merging contexts -}
  data merge : Context n → Context n → Context n → Set where
    merge/z : merge [] [] []
    merge/s : merge Δ₁ Δ₂ Δ → t₁ ∙ t₂ ⇒ t
      → merge ((A , t₁) ∷ Δ₁) ((A , t₂) ∷ Δ₂) ((A , t) ∷ Δ) 
  
  {- Definition of updating contexts -}
  data update : Context n → TaggedProposition → TaggedProposition → Context n → Set where
    update/z : update ((A , t₁) ∷ Δ) (A , t₁) (A , t₂) ((A , t₂) ∷ Δ')
    update/s : update Δ (A , t₁) (A , t₂) Δ'
      → update ((B , t) ∷ Δ) (A , t₁) (A , t₂) ((B , t) ∷ Δ')
      

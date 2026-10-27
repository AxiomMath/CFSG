module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FieldKit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy)

@[expose] def NoSevenCent (J : Type) [Group J] [Finite J] : Prop :=
  ∀ X R : Subgroup J, IsSylowOf 3 X ⊤ → IsElemAbelian 3 X → Nat.card X = 9 →
    IsPGroup 7 R → R ≠ ⊥ → R ≤ centralizer (X : Set J) → False

@[expose] def HasFieldRP (J : Type) [Group J] [Finite J] (Q : ℕ) (B : ℕ → ℕ) : Prop :=
  ∀ W : Subgroup (MulAut J), Nat.card W = 7 → ¬ 7 ∣ Nat.card J →
    ∃ g φ : MulAut J, orderOf φ = 7 ∧
      W = (Subgroup.zpowers φ).map (MulAut.conj g).toMonoidHom ∧ FieldRigid φ ∧ FieldPair φ ∧
      ∃ k : ℕ, k ^ 7 = Q ∧ Nat.card (fixedBy (Subgroup.zpowers φ)) ≤ B k

@[expose] def TorusBig (J : Type) [Group J] [Finite J] (L : ℕ) : Prop :=
  ∀ Z : Subgroup J, IsSylowOf 3 Z ⊤ → Nat.card Z = 9 → L ≤ Nat.card (normalizer (Z : Set J))

@[expose] def sltBound (n k : ℕ) : ℕ := k ^ (n ^ 2 - 1)

@[expose] def torusLow (n q : ℕ) : ℕ := if n = 4 then (q - 1) ^ 3 / 4 else (q ^ 2 - 1) ^ 2 / 5

@[expose] def spBound (k : ℕ) : ℕ := k ^ 10

@[expose] def spTorusLow (q : ℕ) : ℕ := (q - 1) ^ 2 / 2

theorem hasField_of_rp_torus {J : Type} [Group J] [Finite J] {Q L : ℕ} {B : ℕ → ℕ}
    (hrp : HasFieldRP J Q B) (htor : TorusBig J L) (harith : ∀ k : ℕ, k ^ 7 = Q → B k < L) :
    HasField J := by
  intro W hW h7
  obtain ⟨g, φ, hφ, hWφ, hrig, hpair, k, hk, hB⟩ := hrp W hW h7
  exact ⟨g, φ, hφ, hWφ, hrig, hpair, fun Z hZ hZ9 _ =>
    lt_of_le_of_lt hB ((harith k hk).trans_le (htor Z hZ hZ9))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

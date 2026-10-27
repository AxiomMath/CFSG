module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

section ListData

variable {Y : Type} [Group Y]

@[expose] def GammaInv189 (Γ : Subgroup (MulAut Y)) (T : Subgroup Y) : Prop :=
  ∀ γ ∈ Γ, ∀ t ∈ T, γ t ∈ T

structure ListData189 (X Q : Subgroup Y) (Γ : Subgroup (MulAut Y)) (x : Y) : Prop where
  normal : X.Normal
  simple : IsSimpleGroup X
  sup_eq : X ⊔ Q = ⊤
  centralizer_eq : Subgroup.centralizer (X : Set Y) = ⊥
  isPGroup : IsPGroup 2 Q
  ne_bot : Q ≠ ⊥
  inv : GammaInv189 Γ Q
  maximal : ∀ T : Subgroup Y, IsPGroup 2 T → Q ≤ T → GammaInv189 Γ T → T = Q
  comm : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ
  pow_three : ∀ γ ∈ Γ, γ ^ 3 = 1
  mem : x ∈ X
  orderOf_eq : orderOf x = 3
  conj_mem : MulAut.conj x ∈ Γ

@[expose] def AbsInnerFree189 (X Q : Subgroup Y) : Prop :=
  Q ⊓ (X ⊔ Subgroup.centralizer (X : Set Y)) ≤ Subgroup.centralizer (X : Set Y)

noncomputable abbrev absOutOrder189 (X : Subgroup Y) : ℕ :=
  (X ⊔ Subgroup.centralizer (X : Set Y)).index

@[expose] def AbsI189 (Q : Subgroup Y) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 2 Q ⊤

@[expose] def AbsIII189 (X Q : Subgroup Y) : Prop :=
  ∃ n e m : ℕ, 1 ≤ e ∧ Odd m ∧ n = 2 ^ e * m ∧ AbsInnerFree189 X Q ∧
    ((Nonempty (↥X ≃* projSL 2 (GaloisField 2 n)) ∧ absOutOrder189 X = 2 ^ e) ∨
      (Nonempty (↥X ≃* projSU 3 2 n) ∧ absOutOrder189 X = 2 ^ (e + 1)))

@[expose] def AbsIV189 (X Q : Subgroup Y) : Prop :=
  (∃ n : ℕ, Odd n ∧ Nonempty (↥X ≃* projSL 3 (GaloisField 2 n))) ∧
    ∃ K₁ : Subgroup Y, K₁ ≤ X ∧ IsMaxParabolicRankTwo (K₁.subgroupOf X) ∧
      Q = CFSG.Open.pCoreOf 2 K₁

@[expose] def AbsV189 (X Q : Subgroup Y) : Prop :=
  (∃ n : ℕ, Odd n ∧ Nonempty (↥X ≃* projSL 3 (GaloisField 2 n))) ∧
    Nat.card Q = 2 ∧ Q ⊓ (X ⊔ Subgroup.centralizer (X : Set Y)) = ⊥

@[expose] def AbsVI189 (X : Subgroup Y) : Prop :=
  (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 9 < p ^ f ∧
      Nonempty (↥X ≃* projSL 2 (GaloisField p f))) ∨
  (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      ((p % 3 = 2 ∧ Nonempty (↥X ≃* projSL 3 (GaloisField p 1))) ∨
        (p % 3 = 1 ∧ Nonempty (↥X ≃* projSU 3 p 1))))

@[expose] def AbsList189 (X Q : Subgroup Y) : Prop :=
  AbsI189 Q ∨ AbsIII189 X Q ∨ AbsIV189 X Q ∨ AbsV189 X Q ∨ AbsVI189 X

end ListData

section Families

@[expose] def List189L2Even : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (Γ : Subgroup (MulAut Y)) (x : Y) (n : ℕ),
    ListData189 X Q Γ x → 2 ≤ n → Nonempty (↥X ≃* projSL 2 (GaloisField 2 n)) → AbsList189 X Q

@[expose] def List189L3Even : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (Γ : Subgroup (MulAut Y)) (x : Y) (n : ℕ),
    ListData189 X Q Γ x → Odd n → Nonempty (↥X ≃* projSL 3 (GaloisField 2 n)) → AbsList189 X Q

@[expose] def List189U3Even : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (Γ : Subgroup (MulAut Y)) (x : Y) (n : ℕ),
    ListData189 X Q Γ x → Even n → 2 ≤ n → Nonempty (↥X ≃* projSU 3 2 n) → AbsList189 X Q

@[expose] def List189L2Odd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (Γ : Subgroup (MulAut Y)) (x : Y)
    (p f : ℕ) [Fact p.Prime],
    ListData189 X Q Γ x → p ≠ 2 → p ≠ 3 → 1 ≤ f →
      Nonempty (↥X ≃* projSL 2 (GaloisField p f)) → AbsList189 X Q

@[expose] def List189J1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X Q : Subgroup Y) (Γ : Subgroup (MulAut Y)) (x : Y),
    ListData189 X Q Γ x → Nonempty (↥X ≃* CFSG.Blueprint.NativeSporadic.J1) → AbsList189 X Q

end Families

end CFSG.RankThree.PartTwo.Sec18

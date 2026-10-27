module

public import CFSG.Foundations.Basic
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.GH74.GLS.Bg.TwoGroups

namespace Tim79

variable {G : Type} [Group G]

@[expose] def IsL3Type (n : ℕ) (D : Subgroup G) : Prop :=
  Nonempty (↥D ≃* UT3 (GaloisField 2 n))

@[expose] def IsCentralProductOf (P : Subgroup G → Prop) (Q Z : Subgroup G) (k : ℕ) : Prop :=
  0 < k ∧ ∃ D : Fin k → Subgroup G,
    (∀ i, D i ≤ Q) ∧ (∀ i, P (D i)) ∧
    (∀ i, (Subgroup.center ↥(D i)).map (D i).subtype = Z) ∧
    (∀ i j, i ≠ j → ∀ x ∈ D i, ∀ y ∈ D j, x * y = y * x) ∧
    ⨆ i, D i = Q

@[expose] def IsCentralProductOfL3 (Q Z : Subgroup G) (n k : ℕ) : Prop :=
  IsCentralProductOf (IsL3Type n) Q Z k

structure Hyp79 (M V Q : Subgroup G) : Prop where
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) V
  sq_eq_one : ∀ x ∈ V, x ^ 2 = 1
  ti : IsTI V
  q4 : 4 ≤ Nat.card V
  hQ : Q = inSubgroup (pCore 2) M
  gen : Q = ⨆ (g : G) (_ : conjSubgroup g V ≤ Q), conjSubgroup g V
  ne : Q ≠ V

theorem ut3_mem_center_iff {R : Type*} [CommRing R] (x : UT3 R) :
    x ∈ Subgroup.center (UT3 R) ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h1 := congrArg UT3.c (h ⟨1, 0, 0⟩)
    have h2 := congrArg UT3.c (h ⟨0, 1, 0⟩)
    simp only [UT3.mul_def] at h1 h2
    constructor
    · linear_combination -h2
    · linear_combination h1
  · rintro ⟨ha, hb⟩ z
    ext <;> simp only [UT3.mul_def, ha, hb] <;> ring

end Tim79

@[expose] def Tim79Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q : Subgroup G), Tim79.Hyp79 M V Q →
    ∃ n k : ℕ, Nat.card V = 2 ^ n ∧ Tim79.IsCentralProductOfL3 Q V n k

end CFSG.RankThree.GF2n

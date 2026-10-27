module

public import CFSG.RankThree.PartTwo.Sec11.Item116TwoStarKF
public import CFSG.RankThree.PartTwo.Sec11.Item116TwoStarTransport
public import CFSG.RankThree.PartTwo.Sec11.Item116TwoStar

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def ResidueR1 (G : Type) [Group G] (A : Subgroup G) (c a d : G) : Prop :=
  Even (Nat.card (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))) ∧
    (∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c)) ∧
    ∃ n ∈ Subgroup.normalizer (A : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers d ∧
      n * d * n⁻¹ ∈ Subgroup.zpowers c ∧ n * a * n⁻¹ = a⁻¹

@[expose] def ResidueR2 (G : Type) [Group G] (A : Subgroup G) (c d : G) : Prop :=
  ∃ w ∈ Subgroup.normalizer (A : Set G),
    (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
    (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))

@[expose] def IsL2EvenAt {G : Type} [Group G] (L : Subgroup G) (m : ℕ) : Prop :=
  Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 2 (3 * m)))

@[expose] def IsL3MinusPiEven {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * m)

@[expose] def IsL2OddChar {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * e)))

@[expose] def IsList1016Even {G : Type} [Group G] (L : Subgroup G) : Prop :=
  (∃ m : ℕ, 1 < m ∧ IsL2EvenAt L m) ∨ IsL3MinusPiEven L

theorem isList1016_cases {G : Type} [Group G] {L : Subgroup G}
    (h : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)) :
    IsL2OddChar L ∨ IsList1016Even L := by
  rcases h with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

section Defs

@[expose] def TwoStarAtC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ∀ m : ℕ, 1 < m → IsL2EvenAt L m → TwoStarConditionAt A c

@[expose] def ResidueOddChar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      IsL2OddChar L → False

end Defs

section Glue

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem mem_partTwoT_of_R1 (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : ResidueConfig G A c L a R Y d) (hT : A ∉ partTwoT G) (hR1 : ResidueR1 G A c a d)
    (hc : TwoStarConditionAt A c) (hcd : TwoStarConditionAt A (c * d))
    (ha : TwoStarConditionAt A a) (hKF : KFAt L a) : A ∈ partTwoT G := by
  have hs := h.toSec11Std hT
  obtain ⟨-, hD8, n, hnW, hnc, hnd, hna⟩ := hR1
  have hd := TwoStarTransport.twoStar_at_d_of_conj hs h.inf_eq_zpowers hnW hnc hc
  have hcdi := TwoStarTransport.twoStar_at_cd_inv hs h.inf_eq_zpowers h.normalizer_le
    h.isIrreducibleOn h.not_mem_zpowers hcd (Or.inl rfl)
  have hstar := TwoStarTransport.twoStar_of_points hs h.inf_eq_zpowers h.normalizer_le
    h.isIrreducibleOn h.not_mem_zpowers hc hd hcd hcdi ha
  exact mem_partTwoT_of_twoStar h hstar
    (betaNontrivial_of_kf hP2b hP2c h45 hs h.inf_eq_zpowers h.normalizer_le h.isIrreducibleOn
      h.isSylowOf_top h.not_mem_zpowers hD8 hnW hnc hnd hna hstar hKF)

end Glue

end CFSG.RankThree.PartTwo.Sec11

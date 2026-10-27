module

public import CFSG.RankThree.PartOne.S12.InputsEleven
public import CFSG.RankThree.PartOne.S12.InputsTable
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

@[expose] def KF123Classify : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F → ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ r ≠ 11 ∧ RowModel p L r

@[expose] def KF123Row (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F → RowModel p L r → RowData p L F r

@[expose] def KF123Row11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123SU5 p L A₀ F → RowData p L F 11

theorem kf123_of_rows (hc : KF123Classify)
    (hrow : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF123Row r) (h11 : KF123Row11) : KF123 := by
  intro G _ _ p L A₀ F
  refine ⟨fun h => ?_, fun h => h11 G p L A₀ F h⟩
  obtain ⟨r, hr1, hr2, hr3, hmodel⟩ := hc G p L A₀ F h
  exact ⟨r, hr1, hr2, hr3, hrow r hr1 hr2 hr3 G p L A₀ F h hmodel⟩

@[expose] def KF123NTRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123Generic p L A₀ F → RowModel p L r →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → ∀ hy : y ∈ Subgroup.normalizer (F : Set G),
      ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hy⟩)

@[expose] def KF123NTRow11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L A₀ F : Subgroup G),
    Table123SU5 p L A₀ F →
    ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → ∀ hy : y ∈ Subgroup.normalizer (F : Set G),
      ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hy⟩)

theorem kf123NoTransvection_of_rows (hc : KF123Classify)
    (hrow : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF123NTRow r) (h11 : KF123NTRow11) :
    KF123NoTransvection := by
  intro G _ _ p L A₀ F h y hy hyF
  rcases h with h | h
  · obtain ⟨r, hr1, hr2, hr3, hmodel⟩ := hc G p L A₀ F h
    exact hrow r hr1 hr2 hr3 G p L A₀ F h hmodel y hy hyF
  · exact h11 G p L A₀ F h y hy hyF

@[expose] def KF122Tag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ∀ L : Subgroup G,
    CFSG.IsQuasisimple L →
    (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n 2 f) →
    ¬ p ∣ Nat.card (Subgroup.center L) → localRank p L = 2 → evenRank ↥L ≤ 3 →
    (∃ A₀ : Subgroup G, A₀ ≤ L ∧ IsElementaryAbelian p A₀ ∧ Nat.card A₀ = p ^ 2 ∧
      ∃ S : Subgroup G, S ≤ L ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
        A₀ ≤ Subgroup.normalizer (S : Set G) ∧ S = ⁅S, A₀⁆) →
    ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) → x ^ p = 1 →
      x ∉ L ⊔ Subgroup.centralizer (L : Set G) → 3 ≤ localRank p ↥(L ⊔ Subgroup.zpowers x)

theorem kf122_of_tags (h : ∀ t : StatedLieTag, KF122Tag t) : KF122 := by
  intro G _ _ p hp hp5 L hL hLie hZ hrk hev hplane x hx hxp hxL
  obtain ⟨t, n, f, hadm, hm⟩ := hLie
  exact h t G p hp hp5 L hL ⟨n, f, hadm, hm⟩ hZ hrk hev hplane x hx hxp hxL

@[expose] def KF128Tag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (J E : Subgroup G) (a d : G),
    p.Prime → 5 ≤ p → CFSG.IsQuasisimple J →
    (∃ n f : ℕ, StatedLieAdmissible t n 2 f ∧
      CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) t n 2 f) →
    evenRank ↥J ≤ 3 → ¬ p ∣ Nat.card (Subgroup.center J) → IsElementaryAbelian p E →
    E ≤ Subgroup.normalizer (J : Set G) → a ∈ E → d ∈ E → d ∈ J → d ≠ 1 →
    InducesFieldAut p a J →
    (∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      a ∈ Subgroup.normalizer (S : Set G) ∧ d ∈ Subgroup.normalizer (S : Set G)) →
    ∃ y ∈ J, (∃ k : ℕ, orderOf y = p ^ k) ∧ y * d * y⁻¹ = d ∧ y * a * y⁻¹ ≠ a ∧
      ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers d

theorem kf128_of_tags (h : ∀ t : StatedLieTag, KF128Tag t) : KF128 := by
  intro G _ _ p J E a d hp hp5 hJ hLie hev hZ hE hEN haE hdE hdJ hd1 hind hS
  obtain ⟨t, n, f, hadm, hm⟩ := hLie
  exact h t G p J E a d hp hp5 hJ ⟨n, f, hadm, hm⟩ hev hZ hE hEN haE hdE hdJ hd1 hind hS

end CFSG.RankThree.PartOne

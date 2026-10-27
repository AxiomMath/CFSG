module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3Census

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma commutator_subgroupOf_eq_of_commutator_eq {G : Type} [Group G] {X K : Subgroup G}
    (hKX : K ≤ X) (hK : ⁅K, K⁆ = K) :
    ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
  refine Subgroup.map_subtype_inj.mp ?_
  simp only [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKX, hK]

private lemma isL2_bar2_subgroupOf {G : Type} [Group G] {X K : Subgroup G} (hKX : K ≤ X)
    {m : ℕ} (h : IsL2 (Bar2 K) m) : IsL2 (Bar2 (K.subgroupOf X)) m := by
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.nonempty_bar2_equiv_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKX)
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm h

private lemma centralizer_subgroupOf_le {G : Type} [Group G] {X D : Subgroup G} (hDX : D ≤ X) :
    centralizer ((D.subgroupOf X : Subgroup X) : Set X) ≤
      (centralizer (D : Set G)).subgroupOf X := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  rw [Subgroup.mem_centralizer_iff] at hx
  intro d hd
  have h := hx ⟨d, hDX hd⟩ (Subgroup.mem_subgroupOf.mpr hd)
  simpa using congrArg Subtype.val h

private lemma centralizer_subgroupOf_le_normalizer {G : Type} [Group G] {X K D : Subgroup G}
    (hKX : K ≤ X) (hDX : D ≤ X)
    (hcent : X ⊓ centralizer (D : Set G) ≤ normalizer (K : Set G)) :
    centralizer ((D.subgroupOf X : Subgroup X) : Set X) ≤
      normalizer ((K.subgroupOf X : Subgroup X) : Set X) := by
  calc
    centralizer ((D.subgroupOf X : Subgroup X) : Set X)
        ≤ (centralizer (D : Set G)).subgroupOf X := centralizer_subgroupOf_le hDX
    _ = (X ⊓ centralizer (D : Set G)).subgroupOf X := by
        rw [Subgroup.inf_subgroupOf_left]
    _ ≤ (normalizer (K : Set G)).subgroupOf X := Subgroup.subgroupOf_mono X hcent
    _ = normalizer ((K.subgroupOf X : Subgroup X) : Set X) :=
        Subgroup.subgroupOf_normalizer_eq hKX

private lemma subgroupOf_ne_top_of_ne {G : Type} [Group G] {X K : Subgroup G} (hKX : K ≤ X)
    (hne : X ≠ K) : K.subgroupOf X ≠ ⊤ := by
  intro htop
  exact hne (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hKX)

theorem kU3CensusHyp_subgroupOf {Y : Type} [Group Y] {X K D₀ : Subgroup Y} {n p : ℕ}
    (hKX : K ≤ X) (hK : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) (2 * n)) (hn : 2 ≤ n)
    (hnEven : Even n) (hp : p.Prime) (hpdiv : p ∣ 2 ^ n + 1) (hD₀K : D₀ ≤ K)
    (hD₀p : Nat.card D₀ = p) (hcent : X ⊓ centralizer (D₀ : Set Y) ≤ normalizer (K : Set Y))
    (hXK : X ≠ K) : KU3CensusHyp (K.subgroupOf X) (D₀.subgroupOf X) n p := by
  have hD₀X : D₀ ≤ X := hD₀K.trans hKX
  have hD₀'p : Nat.card (D₀.subgroupOf X) = p := by
    rw [← hD₀p]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀X).toEquiv
  exact ⟨commutator_subgroupOf_eq_of_commutator_eq hKX hK, isL2_bar2_subgroupOf hKX hL2,
    hn, hnEven, hp, hpdiv, Subgroup.subgroupOf_mono X hD₀K, hD₀'p,
    centralizer_subgroupOf_le_normalizer hKX hD₀X hcent, subgroupOf_ne_top_of_ne hKX hXK⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

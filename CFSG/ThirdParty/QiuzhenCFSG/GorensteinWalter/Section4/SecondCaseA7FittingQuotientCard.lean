module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7K0QuotientCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The fitting-intersection quotient-card transfer

This is the small finite core behind the source's `F/B` argument.  If the
fixed part `F` is cyclic while `F(U) ∩ M` is noncyclic, then the quotient image
of `F(U) ∩ M` cannot be trivial once the inverted part `K₀` is disjoint from
the odd core.  Combined with an odd-order upper bound of three, the image
therefore has cardinality exactly three.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A cyclic fixed part and a noncyclic fitting intersection force the exact
order-three quotient image needed by the `K₀` transfer. -/
public theorem secondCase_a7_fitting_quotient_card_eq_three_of_cyclic_fixed_part
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (O : Subgroup M) [O.Normal]
    (Y K0 F : Subgroup G)
    (hYleM : Y ≤ M)
    (hjoin : K0 ⊔ F = Y)
    (hK0infO : K0 ⊓ O.map M.subtype = ⊥)
    (hFcyc : IsCyclic F)
    (hYnotcyc : ¬ IsCyclic Y)
    (hYodd : Odd (Nat.card Y))
    (hYcardle3 : Nat.card ((Y.subgroupOf M).map
      (QuotientGroup.mk' O)) ≤ 3) :
    Nat.card ((Y.subgroupOf M).map (QuotientGroup.mk' O)) = 3 := by
  classical
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Ybar : Subgroup (M ⧸ O) := (Y.subgroupOf M).map q
  have hYsubcard : Nat.card (Y.subgroupOf M) = Nat.card Y := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleM).toEquiv
  have hYsubodd : Odd (Nat.card (Y.subgroupOf M)) := by
    rw [hYsubcard]
    exact hYodd
  have hYbarodd : Odd (Nat.card Ybar) := by
    exact Odd.of_dvd_nat hYsubodd (Subgroup.card_map_dvd (Y.subgroupOf M) q)
  have hYbarne : Ybar ≠ ⊥ := by
    intro hbot
    have hYleO : Y ≤ O.map M.subtype := by
      intro x hxY
      let xM : M := ⟨x, hYleM hxY⟩
      have hxbar : q xM ∈ Ybar := by
        exact Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hxY, rfl⟩
      rw [hbot] at hxbar
      have hqone : q xM = 1 := Subgroup.mem_bot.mp hxbar
      have hxO : xM ∈ O :=
        (QuotientGroup.eq_one_iff (N := O) xM).mp hqone
      exact Subgroup.mem_map.mpr ⟨xM, hxO, rfl⟩
    have hK0leO : K0 ≤ O.map M.subtype := by
      intro x hxK0
      have hxY : x ∈ Y := by
        rw [← hjoin]
        exact (le_sup_left : K0 ≤ K0 ⊔ F) hxK0
      exact hYleO hxY
    have hK0bot : K0 = ⊥ := by
      apply le_bot_iff.mp
      intro x hxK0
      have hxinf : x ∈ K0 ⊓ O.map M.subtype :=
        Subgroup.mem_inf.mpr ⟨hxK0, hK0leO hxK0⟩
      rw [hK0infO] at hxinf
      exact Subgroup.mem_bot.mp hxinf
    apply hYnotcyc
    have hYeF : Y = F := by
      rw [← hjoin, hK0bot, bot_sup_eq]
    rw [hYeF]
    exact hFcyc
  have hYbarpos : 0 < Nat.card Ybar := Nat.card_pos
  have hYbarle : Nat.card Ybar ≤ 3 := by
    simpa [Ybar, q] using hYcardle3
  rcases hYbarodd with ⟨n, hn⟩
  have hcard : Nat.card Ybar = 1 ∨ Nat.card Ybar = 3 := by
    omega
  rcases hcard with h1 | h3
  · exfalso
    apply hYbarne
    exact (Subgroup.eq_bot_iff_card (H := Ybar)).mpr h1
  · simpa [Ybar, q] using h3

end CFSG.GorensteinWalter

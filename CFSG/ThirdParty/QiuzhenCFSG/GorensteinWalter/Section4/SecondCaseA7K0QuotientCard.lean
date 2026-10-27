module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingOddCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: quotient image of the inverted fitting part

Equation (3) writes `F(U) ∩ M` as `K₀ ⊔ F`.  If `F` is contained in the odd
core of `M`, its image in `M/O₂′(M)` is trivial, so the quotient image of
`K₀` has the same cardinality as the image of `F(U) ∩ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The exact quotient-cardinality transfer from equation (3). -/
public theorem secondCase_a7_k0_quotient_card_eq_three
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (O : Subgroup M) [O.Normal]
    (Y K0 F : Subgroup G)
    (hYleM : Y ≤ M)
    (hjoin : K0 ⊔ F = Y)
    (hFleO : F ≤ O.map M.subtype)
    (hYcard : Nat.card ((Y.subgroupOf M).map (QuotientGroup.mk' O)) = 3) :
    Nat.card ((K0.subgroupOf M).map (QuotientGroup.mk' O)) = 3 := by
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  have hK0leM : K0 ≤ M := by
    intro x hx
    apply hYleM
    rw [← hjoin]
    exact (le_sup_left : K0 ≤ K0 ⊔ F) hx
  have hFleM : F ≤ M := by
    intro x hx
    apply hYleM
    rw [← hjoin]
    exact (le_sup_right : F ≤ K0 ⊔ F) hx
  have hsub : Y.subgroupOf M = K0.subgroupOf M ⊔ F.subgroupOf M := by
    rw [← hjoin, Subgroup.subgroupOf_sup hK0leM hFleM]
  have hFsubO : F.subgroupOf M ≤ O := by
    intro x hx
    have hxF : (x : G) ∈ F := Subgroup.mem_subgroupOf.mp hx
    have hxO : (x : G) ∈ O.map M.subtype := hFleO hxF
    rcases Subgroup.mem_map.mp hxO with ⟨y, hy, hxy⟩
    have hxy' : y = x := by
      apply Subtype.ext
      exact hxy
    simpa [hxy'] using hy
  have hFmap : (F.subgroupOf M).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (F.subgroupOf M)).2
    intro x hx
    rw [show q.ker = O by simpa [q] using QuotientGroup.ker_mk' O]
    exact hFsubO hx
  have hmap : (Y.subgroupOf M).map q =
      (K0.subgroupOf M).map q ⊔ (F.subgroupOf M).map q := by
    rw [hsub, Subgroup.map_sup]
  have hcardEq : Nat.card ((K0.subgroupOf M).map q) =
      Nat.card ((Y.subgroupOf M).map q) := by
    rw [hmap, hFmap, sup_bot_eq]
  exact hcardEq.trans hYcard

end CFSG.GorensteinWalter

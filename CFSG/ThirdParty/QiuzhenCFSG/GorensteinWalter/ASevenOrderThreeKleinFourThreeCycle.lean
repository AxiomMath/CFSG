module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Order-three elements centralized by a Klein four in `A7` -/

noncomputable section

namespace CFSG.GorensteinWalter

private abbrev A7TC := alternatingGroup (Fin 7)
private abbrev S7TC := Equiv.Perm (Fin 7)

/-- An order-three element of `A7` centralized by a Klein four is a single
three-cycle, rather than a product of two disjoint three-cycles. -/
public theorem aSeven_isThreeCycle_of_order_three_and_kleinFour_centralizer
    (u : alternatingGroup (Fin 7)) (huOrder : orderOf u = 3)
    (V : Subgroup (alternatingGroup (Fin 7))) (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer
      ({u} : Set (alternatingGroup (Fin 7)))) :
    Equiv.Perm.IsThreeCycle (u : Equiv.Perm (Fin 7)) := by
  let up : S7TC := u
  have huPowA : u ^ 3 = 1 := by
    simpa [huOrder] using pow_orderOf_eq_one u
  have huPow : up ^ 3 = 1 := by
    simpa [up] using congrArg Subtype.val huPowA
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one huPow
  let n := up.cycleType.card
  have hctn : up.cycleType = Multiset.replicate n 3 := by
    simpa [n] using hct
  have hsum : up.cycleType.sum = n * 3 := by
    rw [hct]
    simp [n]
  have hsumle : up.cycleType.sum ≤ 7 := by
    simpa using Equiv.Perm.sum_cycleType_le up
  have hupne : up ≠ 1 := by
    intro hup
    have huone : u = 1 := Subtype.ext hup
    rw [huone, orderOf_one] at huOrder
    norm_num at huOrder
  have hnpos : 0 < n := Equiv.Perm.card_cycleType_pos.mpr hupne
  have hnle : n ≤ 2 := by omega
  interval_cases n
  · have hct1 : up.cycleType = {3} := by simpa using hctn
    exact hct1
  · have hct2 : up.cycleType = {3, 3} := by simpa using hctn
    let C : Subgroup S7TC := Subgroup.centralizer ({up} : Set S7TC)
    have hCcard : Nat.card C = 18 := by
      dsimp [C]
      rw [Equiv.Perm.nat_card_centralizer, hct2]
      norm_num
    let Vp : Subgroup S7TC := V.map A7TC.subtype
    have hVpcard : Nat.card Vp = 4 := by
      rw [Subgroup.card_map_of_injective A7TC.subtype_injective,
        hVK.card_four]
    have hVpleC : Vp ≤ C := by
      intro v hv
      rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hVcent hv0)
      exact congrArg Subtype.val hc
    have hdiv : 4 ∣ 18 := by
      rw [← hVpcard, ← hCcard]
      exact Subgroup.card_dvd_of_le hVpleC
    norm_num at hdiv

end CFSG.GorensteinWalter

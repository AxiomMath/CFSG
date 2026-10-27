module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONHeis
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
public import CFSG.RankThree.Native.ONSevenKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier CFSG.RankThree.Native
open scoped commutatorElement

theorem on_isHeisCenter7_on7W_zero :
    IsHeisCenter7 (on7W 0) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc : IsHeisCenter7 ⁅onSevenA, onSevenB⁆ :=
    isHeisCenter7_of_commutator onSevenA_pow_seven onSevenB_pow_seven
      onSeven_commutator_ne_one onSeven_commute_commutator_A onSeven_commute_commutator_B
  have haF : onSevenA ∈ on7F 0 :=
    Subgroup.mem_subgroupOf.2 (onSevenQ_le_F0 onSevenA_mem_Q)
  have hbF : onSevenB ∈ on7F 0 :=
    Subgroup.mem_subgroupOf.2 (onSevenQ_le_F0 onSevenB_mem_Q)
  have hclosure : Subgroup.closure ({onSevenA, onSevenB} : Set Pv) = on7F 0 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · refine (Subgroup.closure_le (on7F 0)).2 ?_
      rintro x (rfl | rfl)
      · exact haF
      · exact hbF
    · rw [card_closure_onSevenAB, (on7_sevenLine 0).card_eq]
  have hcommF : ⁅onSevenA, onSevenB⁆ ∈ on7F 0 :=
    Subgroup.commutator_le_self (on7F 0)
      (Subgroup.commutator_mem_commutator haF hbF)
  have hcentral : on7F 0 ≤ Subgroup.centralizer ({⁅onSevenA, onSevenB⁆} : Set Pv) := by
    rw [← hclosure]
    refine (Subgroup.closure_le (Subgroup.centralizer ({⁅onSevenA, onSevenB⁆} : Set Pv))).2 ?_
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 onSeven_commute_commutator_A.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 onSeven_commute_commutator_B.symm
  have hcz : ⁅onSevenA, onSevenB⁆ ∈ Subgroup.zpowers (on7W 0) :=
    (on7_sevenLine 0).center_le hcommF fun q hq =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hcentral hq)).symm
  have hc7 : ⁅onSevenA, onSevenB⁆ ^ 7 = 1 :=
    hc.elim fun _ hx => hx.elim fun _ h => h.1.zp
  have hordc : orderOf ⁅onSevenA, onSevenB⁆ = 7 :=
    orderOf_eq_prime hc7 onSeven_commutator_ne_one
  have hfin : IsOfFinOrder ⁅onSevenA, onSevenB⁆ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨7, by norm_num, hc7⟩
  obtain ⟨k, hk⟩ :=
    (Submonoid.mem_powers_iff _ _).1
      (hfin.mem_powers_iff_mem_zpowers.2 (mem_zpowers_symm hordc (orderOf_on7W 0) hcz))
  have hk7 : ¬ 7 ∣ k := by
    intro hdvd
    obtain ⟨m, rfl⟩ := hdvd
    exact on7W_ne_one 0 (by rw [← hk, pow_mul, hc7, one_pow])
  simpa [hk] using hc.pow hk7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

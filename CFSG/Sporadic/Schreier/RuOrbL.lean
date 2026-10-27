
module

public import CFSG.Sporadic.Schreier.RuOrbLBase

public import CFSG.Sporadic.Schreier.RuCheckOrbLA
public import CFSG.Sporadic.Schreier.RuCheckOrbLB
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.Sporadic.Schreier.RuCheckLInputs
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.RuOrbLFacts
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Certificate2254Base

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem ruZL_comm
    {i : ℕ} (hi : i < 3)
    {l : Equiv.Perm (Fin 4060)} (hl : l ∈ ruL) : ruZL i * l = l * ruZL i :=
  (Subgroup.mem_centralizer_iff.1 (ruOrbLA_check.1 i hi) l hl).symm

theorem ruOrb_disjoint
    {k k' : ℕ} (hk : k < 19)
    (hk' : k' < 19) (h : k ≠ k') : Disjoint (ruOrb k) (ruOrb k') :=
  ruOrbLA_check.2 k hk k' hk' h

theorem card_ruL_centralizer_rep
    {k : ℕ} (hk : k < 19) :
    Nat.card (ruL ⊓ Subgroup.centralizer {ruRepZ k} : Subgroup _) = ruCentCounts.getD k 0 := by
  rw [card_inf_centralizer_eq, ruL_card_of_count (p := fun l => ruCommTest l (ruRepZA k))
    fun t g ht => ruCommTest_iff ht (rep_ruRepZ k), ← ruOrbLB_check.1, getD_map_range 0 hk]
  rfl

theorem ncard_ruOrb
    {k : ℕ} (hk : k < 19) :
    (ruOrb k).ncard = 116480 / ruCentCounts.getD k 0 := by
  have h := ncard_conjSet_mul_card ruL (ruRepZ k)
  rw [card_ruL_centralizer_rep hk, card_ruL] at h
  have hpos : 0 < ruCentCounts.getD k 0 := by interval_cases k <;> decide
  rw [← h, Nat.mul_div_cancel _ hpos]

theorem ruZP_eq_iUnion :
    ruZP = ⋃ k ∈ Finset.range 19, ruOrb k := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro t ht
    simp only [Set.mem_iUnion, Finset.mem_range] at ht
    obtain ⟨k, -, ht⟩ := ht
    exact ruOrb_sub k ht
  · have hdisj : (↑(Finset.range 19) : Set ℕ).PairwiseDisjoint ruOrb := by
      intro i hi j hj hij
      exact ruOrb_disjoint (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij
    have hU := (Finset.finite_toSet (Finset.range 19)).ncard_biUnion
      (fun _ _ => Set.toFinite _) hdisj
    rw [finsum_mem_coe_finset] at hU
    have hU' : (⋃ k ∈ Finset.range 19, ruOrb k).ncard = 593775 := by
      rw [show (⋃ k ∈ Finset.range 19, ruOrb k) = ⋃ k ∈ (↑(Finset.range 19) : Set ℕ), ruOrb k
        from by simp only [Finset.mem_coe], hU, Finset.sum_congr rfl fun k hk =>
          ncard_ruOrb (Finset.mem_range.1 hk)]
      decide
    rw [hU', ncard_ruZP]
  · exact Set.toFinite _

theorem ruRep_ord14
    {k : ℕ} (hk : k < 19) :
    orderOf (ruA0 * ruRepZ k) = 14 ↔ k ∈ ruSpecial := by
  rw [← ruOrd14_iff (rep_compA rep_ruA0 (rep_ruRepZ k))]
  have h := congrArg (fun l => l.getD k false) ruOrbLB_check.2.1
  simp only [getD_map_range false hk] at h
  rw [h]
  interval_cases k <;> decide

theorem ruOrb_ord14
    {k : ℕ} (hk : k < 19) {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruOrb k) :
    orderOf (ruA0 * t) = 14 ↔ k ∈ ruSpecial := by
  rw [orderOf_mul_of_mem_ruOrb ht, ruRep_ord14 hk]

end CFSG.Sporadic.RuSchreier

module

public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1

public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Sporadic.Co2Schreier.Enum
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem locU_fix
    {j : ℕ} (hj : j < 12) : locU (bpt j) = bpt j := by
  apply Fin.ext
  rw [rep_apply_bpt rep_u (j := j) (by omega), bpt_val (j := j) (by omega)]
  have := allLt_iff.1 thirdFacts.u_fix j hj
  simpa using this

theorem card_cosetH_thirteen
    (p : Equiv.Perm (Fin 2300)) : (cosetH 13 p).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  rw [mem_cosetH, stabB_thirteen, Subgroup.mem_bot] at ha hb
  rw [← mul_right_inj p⁻¹, ha.2, hb.2]

theorem cover_cosetH
    {j : ℕ} (hj : j < 13) {p h : Equiv.Perm (Fin 2300)} (hh : h ∈ cosetH j p) :
    ∃ k < tsz j, h ∈ cosetH (j + 1) (p * thT j k) ∧
      (j < 12 → locU ((p * thT j k) (bpt j)) = (p * thT j k) (bpt j)) := by
  rw [mem_cosetH] at hh
  obtain ⟨k, hk, hs⟩ := exists_thT_inv_mul_mem hj hh.2
  refine ⟨k, hk, ?_, fun hj' => ?_⟩
  · rw [mem_cosetH, mul_inv_rev, mul_assoc]
    exact ⟨hh.1, hs⟩
  · have he : h = p * thT j k * ((thT j k)⁻¹ * (p⁻¹ * h)) := by group
    have hb : ((thT j k)⁻¹ * (p⁻¹ * h)) (bpt j) = bpt j := hs.2 j (by omega)
    have hhb : h (bpt j) = (p * thT j k) (bpt j) := by
      conv_lhs => rw [he]
      rw [Equiv.Perm.mul_apply, hb]
    exact fix_of_comm (mem_locH3.1 hh.1).2 (locU_fix hj') hhb

theorem card_cosetH_le :
    ∀ (f j : ℕ), j + f = 13 → ∀ (p : Equiv.Perm (Fin 2300)) (pA : Array ℕ),
    Rep 2300 pA p → (cosetH j p).card ≤ dfsCnt thL thB uArr 12 f j pA
  | 0, j, hj, p, _, _ => by
    rw [show j = 13 by omega, dfsCnt]
    exact card_cosetH_thirteen p
  | f + 1, j, hj, p, pA, hp => by
    have hj13 : j < 13 := by omega
    rw [dfsCnt]
    split_ifs with h1 h2 h3
    ·
      have hsub : cosetH j p ⊆ (Finset.range (tsz j)).biUnion
          fun k => cosetH (j + 1) (p * thT j k) := by
        intro h hh
        obtain ⟨k, hk, hk', -⟩ := cover_cosetH hj13 hh
        exact Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, hk'⟩
      have hle := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      refine hle.trans ?_
      have h13 : j + 1 = 13 := by omega
      calc ∑ k ∈ Finset.range (tsz j), (cosetH (j + 1) (p * thT j k)).card
          ≤ ∑ _k ∈ Finset.range (tsz j), 1 := Finset.sum_le_sum fun k _ => by
            rw [h13]
            exact card_cosetH_thirteen _
        _ = tsz j := by simp
    ·
      have hz : cosetH j p = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun h hh => ?_
        obtain ⟨k, hk, -, htest⟩ := cover_cosetH hj13 hh
        have hk0 : k = 0 := by
          change k < thL[j]!.tr.size at hk
          omega
        subst hk0
        simp only [thT_zero hj13, mul_one] at htest
        apply h3.2
        rw [← rep_apply_bpt hp hj13, rep_apply rep_u]
        exact congrArg Fin.val (htest h3.1)
      rw [hz, Finset.card_empty]
    ·
      have hsub : cosetH j p ⊆ cosetH (j + 1) p := by
        intro h hh
        obtain ⟨k, hk, hk', -⟩ := cover_cosetH hj13 hh
        have hk0 : k = 0 := by
          change k < thL[j]!.tr.size at hk
          omega
        subst hk0
        rwa [thT_zero hj13, mul_one] at hk'
      exact (Finset.card_le_card hsub).trans
        (card_cosetH_le f (j + 1) (by omega) p pA hp)
    ·
      rw [foldl_cond_sum]
      have hsub : cosetH j p ⊆ ((Finset.range thL[j]!.tr.size).filter fun k =>
          ¬ (j < 12 ∧ uArr[pA[(thL[j]!.tr[k]!)[thB[j]!]!]!]! ≠
            pA[(thL[j]!.tr[k]!)[thB[j]!]!]!)).biUnion
          fun k => cosetH (j + 1) (p * thT j k) := by
        intro h hh
        obtain ⟨k, hk, hk', htest⟩ := cover_cosetH hj13 hh
        refine Finset.mem_biUnion.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ?_⟩, hk'⟩
        rintro ⟨hj12, hne⟩
        apply hne
        have hx : pA[(thL[j]!.tr[k]!)[thB[j]!]!]! = ((p * thT j k) (bpt j) : ℕ) := by
          rw [Equiv.Perm.mul_apply, ← rep_apply hp, ← rep_apply_bpt (rep_thT hj13 hk) hj13]
        rw [hx, rep_apply rep_u]
        exact congrArg Fin.val (htest hj12)
      refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [ite_not]
      split_ifs
      · exact le_rfl
      · exact card_cosetH_le f (j + 1) (by omega) _ _
          (rep_compA hp (rep_thT hj13 (Finset.mem_range.1 hk)))

open scoped Classical in
theorem card_locH3_le :
    Nat.card locH3 ≤ 1474560 := by
  have h := card_cosetH_le 13 0 rfl 1 (idA 2300) rep_idA
  rw [beq_iff_eq.1 thirdFacts.dfs] at h
  have he : cosetH 0 1 = Finset.univ.filter fun g => g ∈ locH3 := by
    ext g
    rw [mem_cosetH, inv_one, one_mul, stabB_zero, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.1 h).1⟩⟩
  rw [he] at h
  rw [show Nat.card locH3 = Nat.card (Finset.univ.filter fun g => g ∈ locH3) from
    Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp), Nat.card_eq_finsetCard]
  exact h

end CFSG.Sporadic.Co2Schreier

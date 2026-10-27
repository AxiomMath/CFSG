module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private lemma w1369_coprime_sum_ordCompl (n : ℕ) (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors, ordCompl[p] n).Coprime n := by
  refine Nat.coprime_of_dvd ?_
  intro q hq hqS hqn
  have hqmem : q ∈ n.primeFactors := hq.mem_primeFactors hqn hn
  have hqT : q ∣ ∑ p ∈ n.primeFactors.erase q, ordCompl[p] n := by
    refine Finset.dvd_sum fun p hp => ?_
    obtain ⟨hpq, hps⟩ := Finset.mem_erase.1 hp
    refine Nat.dvd_ordCompl_of_dvd_not_dvd hqn ?_
    intro hpqd
    exact hpq ((hq.dvd_iff_eq (Nat.prime_of_mem_primeFactors hps).ne_one).1 hpqd).symm
  have hqfq : q ∣ ordCompl[q] n := by
    have hsum := Finset.add_sum_erase n.primeFactors (fun p => ordCompl[p] n) hqmem
    have hqsum : q ∣ ordCompl[q] n + ∑ p ∈ n.primeFactors.erase q, ordCompl[p] n := by
      rw [hsum]
      exact hqS
    exact (Nat.dvd_add_iff_right hqT).mpr (by rwa [add_comm] at hqsum)
  exact (Nat.not_dvd_ordCompl hq hn) hqfq

theorem center_cent_t {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    (c : Ctx136 Y t L) {z : MulAut W} (hz : z ∈ L) (hzc : ∀ l ∈ L, l * z = z * l) :
    t * z = z * t := by
  classical
  set n := orderOf z with hn_def
  have hn : n ≠ 0 := (isOfFinOrder_of_finite z).orderOf_pos.ne'
  set S := ∑ p ∈ n.primeFactors, ordCompl[p] n with hS_def
  have hS : S.Coprime n := by
    rw [hS_def]
    exact w1369_coprime_sum_ordCompl n hn
  have hsubL : IsSubnormal L Y := c.comp.2.1
  have hcomm : ∀ p ∈ n.primeFactors, Commute t (z ^ ordCompl[p] n) := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd_n : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    set w := z ^ ordCompl[p] n with hw
    have hwL : w ∈ L := pow_mem hz _
    have hwC : ∀ l ∈ L, l * w = w * l := by
      intro l hl
      exact ((show Commute l z from hzc l hl).pow_right _).eq
    have hnormal : ((Subgroup.zpowers w).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.zpowers_le.mpr hwL)]
      intro h k hh hk
      rw [Subgroup.mem_zpowers_iff] at hh ⊢
      obtain ⟨i, rfl⟩ := hh
      use i
      have hk_comm : Commute k w := hwC k hk
      rw [(hk_comm.zpow_right i).eq, mul_assoc, mul_inv_cancel, mul_one]
    have hsubw : IsSubnormal (Subgroup.zpowers w) Y :=
      IsSubnormal.step (Subgroup.zpowers_le.mpr hwL) hnormal hsubL
    have horder : orderOf w = p ^ n.factorization p := by
      rw [hw, orderOf_pow_of_dvd (Nat.ordCompl_pos p hn).ne' (Nat.ordCompl_dvd n p)]
      rw [← hn_def]
      exact Nat.div_eq_of_eq_mul_left (Nat.ordCompl_pos p hn)
        (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    have hpgroup : IsPGroup p (Subgroup.zpowers w) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, horder])
    have hcore : Subgroup.zpowers w ≤ pCoreOf p Y :=
      CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf p hsubw hpgroup
    have hwcore : w ∈ pCoreOf p Y := hcore (Subgroup.mem_zpowers w)
    have hle_cent :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (c.hF p hp_prime)
    have hwcent : w ∈ Subgroup.centralizer (Subgroup.zpowers t : Set (MulAut W)) :=
      hle_cent hwcore
    exact (Subgroup.mem_centralizer_iff.1 hwcent) t (Subgroup.mem_zpowers t)
  have hcommS : Commute t (z ^ S) := by
    rw [hS_def]
    have hmain : ∀ s ⊆ n.primeFactors, Commute t (z ^ ∑ p ∈ s, ordCompl[p] n) := by
      intro s
      refine Finset.induction_on s ?h0 ?h1
      · intro _
        simp
      · intro a s ha ih hsub
        rw [Finset.sum_insert ha, pow_add]
        exact (hcomm a (hsub (Finset.mem_insert_self a s))).mul_right
          (ih fun p hp => hsub (Finset.mem_insert_of_mem hp))
    exact hmain n.primeFactors fun _ hp => hp
  have hS' : S.Coprime (orderOf z) := by rwa [← hn_def]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := z) (n := S) hS'
  rw [← hm]
  exact hcommS.pow_right m

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

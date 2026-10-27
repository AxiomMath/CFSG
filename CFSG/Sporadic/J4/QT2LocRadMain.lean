
module

public import CFSG.Sporadic.J4.QT2LocRadMainBase

public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.J4.QT2LocFiveProof
public import CFSG.Sporadic.J4.QT2LocCntMain
public import CFSG.Sporadic.J4.QT2ARad

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem radical_eta_1131 :
    ∃ N : Subgroup J, Radical (eta uJ 11 1131) N := by
  have hM := j4Facts.mat
  have hC : Nat.card QT2A.Cz = 21799895040 := card_centralizer_eta_1131
  obtain ⟨N, hQN, hNC, hnorm, hp, hself⟩ :=
    QT2A.exists_normal_two_group_selfcentralizing_ge hM hC
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hy5C, hy5⟩ := QT2A.y_prime_facts hM (QT2A.Mx_y5J hM) QT2A.chkYr5_true
  refine ⟨N, hp, hQN QT2A.zJ_mem_Qz, hNC, hnorm, hself, ?_⟩
  intro g hg hg5
  exact lt_relIndex_of_sylow QT2A.Cz N hnorm (card_Cz_factorization_five hC) hy5C hy5
    (lt_relIndex_inf_of_le hQN _ (QT2A.lt_relIndex_centralizer_y5J hM)) hg hg5

theorem j4_involution_radical
    (y : J) (hy : y * y = 1) (hne : y ≠ 1) :
    ∃ N : Subgroup J, IsPGroup 2 ↥N ∧ y ∈ N ∧ N ≤ Subgroup.centralizer ({y} : Set J) ∧
      (∀ q ∈ Subgroup.centralizer ({y} : Set J), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧
      (∀ q ∈ Subgroup.centralizer ({y} : Set J), (∀ e ∈ N, q * e = e * q) → q ∈ N) ∧
      ∀ g ∈ Subgroup.centralizer ({y} : Set J), orderOf g = 5 →
        16 < (N ⊓ Subgroup.centralizer ({g} : Set J)).relIndex N := by
  rcases inv_conj_root j4Facts hy hne with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hr := (radical_eta_T j4Facts one_mem_tMasks).conj c
    rw [hc] at hr
    exact ⟨conjSub c (Eg uJ 11), hr⟩
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨g, -, hg⟩ := exists_conj_eta_three_of_mem_zMasks mem_zMasks_1131
    obtain ⟨N, hN⟩ := radical_eta_1131
    have hr := hN.conj (c * g⁻¹)
    have e : (c * g⁻¹) * eta uJ 11 1131 * (c * g⁻¹)⁻¹ = y := by
      rw [← hg, ← hc]
      group
    rw [e] at hr
    exact ⟨conjSub (c * g⁻¹) N, hr⟩

end CFSG.Sporadic.J4.QT2

module

public import CFSG.GH74.Generic.GKFCover
public import CFSG.Sporadic.Recognition.Fi22MultiplierRho
public import CFSG.Sporadic.Recognition.YCoverPerfect
public import Certificates.Certificate291380

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.YGroups (YGroup yGen ngen closure_yGen evalWord_yGen_332_eq_iff
  evalWord_yGen_332_eq_one_iff card_y332)
open CFSG.Sporadic.Recognition.Fi22Multiplier
open CFSG.RankThree.PerfectCover CFSG.Blueprint

private theorem evalWord_yGen_append (u v : List ℕ) :
    evalWord (yGen 3 3 2) (u ++ v) = evalWord (yGen 3 3 2) u * evalWord (yGen 3 3 2) v := by
  simp [evalWord]

theorem F332_comm_gen
    {c : ℕ} (hc : c < 9) :
    F332 * yGen 3 3 2 c = yGen 3 3 2 c * F332 := by
  have h := (evalWord_yGen_332_eq_iff (f332Word ++ [c]) ([c] ++ f332Word)).2
    (Certificates.certificate291380.1 c hc)
  rw [evalWord_yGen_append, evalWord_yGen_append, ← F332_eq] at h
  simpa [evalWord] using h

theorem F332_sq_eq_one :
    F332 * F332 = 1 := by
  have h := (evalWord_yGen_332_eq_one_iff (f332Word ++ f332Word)).2
    Certificates.certificate291380.2
  rwa [evalWord_yGen_append, ← F332_eq] at h

theorem F332_mem_center :
    F332 ∈ Subgroup.center (YGroup 3 3 2) := by
  have hle : Subgroup.closure (yGen 3 3 2 '' Set.Iio (ngen 3 3 2)) ≤
      Subgroup.centralizer {F332} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro h rfl
    exact F332_comm_gen (by simpa [ngen] using hc)
  rw [closure_yGen] at hle
  exact Subgroup.mem_center_iff.2 fun g =>
    (Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top g)) F332 rfl).symm

theorem card_normalClosure_F332 :
    Nat.card (Subgroup.normalClosure ({F332} : Set (YGroup 3 3 2))) = 2 := by
  have hz : Subgroup.zpowers F332 ≤ Subgroup.center (YGroup 3 3 2) :=
    Subgroup.zpowers_le.2 F332_mem_center
  have : (Subgroup.zpowers F332).Normal := Subgroup.normal_of_le_center hz
  have hN : Subgroup.normalClosure ({F332} : Set (YGroup 3 3 2)) = Subgroup.zpowers F332 :=
    le_antisymm (Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.2
      (Subgroup.mem_zpowers _))) (Subgroup.zpowers_le.2 (Subgroup.subset_normalClosure rfl))
  rw [hN, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact F332_sq_eq_one) F332_ne_one]

theorem card_R332 :
    Finite R332 ∧ Nat.card R332 = 2 * 64561751654400 := by
  have hfin : Finite (YGroup 3 3 2) := Nat.finite_of_card_ne_zero (by rw [card_y332]; norm_num)
  have h := (Subgroup.normalClosure ({F332} : Set (YGroup 3 3 2))).card_eq_card_quotient_mul_card_subgroup
  rw [card_y332, card_normalClosure_F332] at h
  refine ⟨inferInstance, ?_⟩
  change Nat.card (YGroup 3 3 2 ⧸ Subgroup.normalClosure ({F332} : Set (YGroup 3 3 2))) = _
  omega

theorem isPerfect_R332 : Group.IsPerfect R332 :=
  CFSG.Sporadic.Recognition.YCover.isPerfect_quotY flagData332 (F := F332) rfl

theorem card_ker_rhoFi22 :
    Nat.card rhoFi22.ker = 2 := by
  have h := Subgroup.card_ker_mul_card_of_surjective rhoFi22_surjective
  rw [card_R332.2, CFSG.Sporadic.Fi22.card_Fi22] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem ker_rhoFi22_le_center :
    rhoFi22.ker ≤ Subgroup.center R332 := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases h1 : k = 1
  · simp [h1]
  · obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : rhoFi22.ker)).1 card_ker_rhoFi22
    have hk' : (⟨k, hk⟩ : rhoFi22.ker) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    have hc : (⟨g * k * g⁻¹, Subgroup.Normal.conj_mem inferInstance k hk g⟩ : rhoFi22.ker) ≠ 1 :=
      fun h => h1 (by simpa using congrArg Subtype.val h)
    have h2 := congrArg Subtype.val ((huniq _ hk').trans (huniq _ hc).symm)
    exact (eq_mul_inv_iff_mul_eq.1 h2).symm

theorem two_dvd_card_hopfMultiplier_Fi22 :
    2 ∣ Nat.card (hopfMultiplier (NativeSporadic.Carrier .Fi22)) := by
  have := card_R332.1
  have h := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier isPerfect_R332 rhoFi22
    rhoFi22_surjective ker_rhoFi22_le_center
  rwa [card_ker_rhoFi22] at h

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local45
public import Certificates.Certificate919242
import CFSG.GroupTheory.InvolutionPair
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu

theorem v2_ne_one :
    v2J ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -⟩ := local45
  intro h
  have h1 : eqA 315 v2Arr (idA 315) = true := (eqA_iff rep_v2 rep_one).2 (by rw [h])
  rw [h1] at h8
  exact Bool.noConfusion h8

theorem v1_ne_v2 :
    v1J ≠ v2J := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := local45
  intro h
  have h1 : eqA 315 v1Arr v2Arr = true := (eqA_iff rep_v1 rep_v2).2 (by rw [h])
  rw [h1] at h9
  exact Bool.noConfusion h9

private theorem VJ_eq_closure :
    VJ = Subgroup.closure ({v1J, v2J} : Set GJ) := by
  apply le_antisymm
  · intro x hx
    rcases mem_kleinSub.1 hx with h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact subset_closure (by simp)
    · rw [h]; exact subset_closure (by simp)
    · rw [h]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact v1_mem_V
    · rw [hx]; exact v2_mem_V

theorem card_V :
    Nat.card VJ = 4 := by
  rw [VJ_eq_closure]
  exact CFSG.GroupTheory.card_closure_pair_eq_four v1_sq v2_sq v12_comm v1_ne_one v2_ne_one
    v1_ne_v2

theorem mem_E0_of_commute
    {g : GJ} (hz : g ∈ centralizer ({zJ} : Set GJ))
    (hx : g * xJ = xJ * g) : g ∈ E0 := by
  rw [centralizer_z] at hz
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 hz
  have hck := allLt_spec chkE0_spec.2 hk
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hck
  have hcx : commA cCz.pts[k]! xArr = true := commA_of_commute hr rep_x hx
  rcases hck with h | h
  · rw [hcx] at h
    exact absurd h Bool.noConfusion
  · exact mem_Ej_of_inE hr h

theorem VJ_inf_centralizer_z :
    VJ ⊓ centralizer ({zJ} : Set GJ) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro g hg
  obtain ⟨hgV, hgz⟩ := Subgroup.mem_inf.mp hg
  have hgx : g * xJ = xJ * g := mem_centralizer_singleton_iff.1 (V_le_C hgV)
  have hgE : g ∈ E0 := mem_E0_of_commute hgz hgx
  have h2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact mul_self_of_mem_kleinSub hgV
  have h3 : g ^ 3 = 1 := cube_of_mem_P3 (E0_le_P3 hgE)
  have hg1 : g = 1 := by
    calc g = (g ^ 2)⁻¹ * g ^ 3 := by group
      _ = 1 := by rw [h2, h3, inv_one, one_mul]
  exact Subgroup.mem_bot.2 hg1

theorem zJ_mem_normalizer_VJ :
    zJ ∈ normalizer (VJ : Set GJ) := by
  refine mem_normalizer_of_conj_mem fun v hv => ?_
  have hz : zJ ∈ centralizer ({xJ} : Set GJ) := by
    rw [mem_centralizer_singleton_iff, z_eq]
    exact z_comm_x.eq
  exact conj_mem_V ((centralizer_le_normalizer_zpowers' xJ) hz) hv

theorem card_sup_VJ_zpowers_z :
    Nat.card (VJ ⊔ zpowers zJ : Subgroup GJ) = 12 := by
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := zpowers zJ) (K := VJ) (zpowers_le.2 zJ_mem_normalizer_VJ)
  have hinf : VJ ⊓ zpowers zJ = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro g hg
    obtain ⟨hgV, hgz⟩ := Subgroup.mem_inf.mp hg
    have hgz' : g ∈ centralizer ({zJ} : Set GJ) :=
      zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl) hgz
    have hmem : g ∈ VJ ⊓ centralizer ({zJ} : Set GJ) := ⟨hgV, hgz'⟩
    rw [VJ_inf_centralizer_z] at hmem
    exact hmem
  rw [sup_comm, inf_comm, hinf, Subgroup.card_bot, card_zpowers_z, card_V, mul_one] at h
  simpa using h

theorem eq_mul_of_mem_VJ
    {u v w : GJ} (hu : u ∈ VJ) (hv : v ∈ VJ) (hw : w ∈ VJ) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    w = v * u := by
  rcases mem_kleinSub.1 hu with rfl | rfl | rfl | rfl
  · exact (hu1 rfl).elim
  · rcases mem_kleinSub.1 hv with rfl | rfl | rfl | rfl
    · exact (hv1 rfl).elim
    · exact (huv rfl).elim
    · rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
      · exact (hw1 rfl).elim
      · exact (huw rfl).elim
      · exact (hvw rfl).elim
      · rw [v12_comm]
    · rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
      · exact (hw1 rfl).elim
      · exact (huw rfl).elim
      · rw [mul_assoc, ← v12_comm, ← mul_assoc, v1_sq, one_mul]
      · exact (hvw rfl).elim
  · rcases mem_kleinSub.1 hv with rfl | rfl | rfl | rfl
    · exact (hv1 rfl).elim
    · rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
      · exact (hw1 rfl).elim
      · exact (hvw rfl).elim
      · exact (huw rfl).elim
      · rfl
    · exact (huv rfl).elim
    · rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
      · exact (hw1 rfl).elim
      · rw [mul_assoc, v2_sq, mul_one]
      · exact (huw rfl).elim
      · exact (hvw rfl).elim
  · rcases mem_kleinSub.1 hv with rfl | rfl | rfl | rfl
    · exact (hv1 rfl).elim
    · rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
      · exact (hw1 rfl).elim
      · exact (hvw rfl).elim
      · rw [← mul_assoc, v1_sq, one_mul]
      · exact (huw rfl).elim
    · rcases mem_kleinSub.1 hw with rfl | rfl | rfl | rfl
      · exact (hw1 rfl).elim
      · rw [v12_comm, ← mul_assoc, v2_sq, one_mul]
      · exact (hvw rfl).elim
      · exact (huw rfl).elim
    · exact (huv rfl).elim

theorem mem_centralizer_VJ_of_inv
    {t : GJ} (htz : t ∈ centralizer ({zJ} : Set GJ))
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (h5 : (xJ * t) ^ 5 = 1) :
    t ∈ centralizer (VJ : Set GJ) := by
  rw [centralizer_z] at htz
  obtain ⟨k, hk, hr⟩ := exists_rep_subOf (by decide) enum_spec.2.2.1 htz
  set s := cCz.pts[k]! with hs
  have hrs : Rep 315 s t.1 := by rw [hs]; exact hr
  have h2A : eqA 315 (compA 315 s s) (idA 315) = true :=
    (eqA_iff (rep_mul hrs hrs) rep_one).2 (by rw [ht2])
  have h1A : eqA 315 s (idA 315) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact ht1 (eq_of_rep hrs rep_one h)
  have hInv : isInvolA s = true := by
    simp only [isInvolA, h2A, h1A, Bool.not_false, Bool.and_true]
  have h5A : eqA 315 (powArr 315 (compA 315 xArr s) 5) (idA 315) = true :=
    (eqA_iff (rep_pow (rep_mul rep_x hrs) 5) rep_one).2 (by rw [h5])
  have hchk : (!(isInvolA s && eqA 315 (powArr 315 (compA 315 xArr s) 5) (idA 315)) ||
      (commA s v1Arr && commA s v2Arr)) = true := by
    simpa [ks166InvCheck, hs] using
      allLt_spec Certificates.certificate919242 hk
  rw [hInv, h5A, Bool.and_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hchk
  obtain ⟨hc1, hc2⟩ := hchk
  have hcomm1 : Commute t v1J := commute_of_commA hrs rep_v1 hc1
  have hcomm2 : Commute t v2J := commute_of_commA hrs rep_v2 hc2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases mem_kleinSub.1 hv with h | h | h | h
  · rw [h, one_mul, mul_one]
  · rw [h]
    exact hcomm1.symm.eq
  · rw [h]
    exact hcomm2.symm.eq
  · rw [h]
    exact (hcomm1.mul_right hcomm2).symm.eq

end CFSG.RankThree.PartTwo.KFacts.KS166

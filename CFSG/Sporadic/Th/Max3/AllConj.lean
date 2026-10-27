
module

public import CFSG.Sporadic.Th.Max3.AllConjBase1

public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10088
import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersBasic

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

namespace AllConj

theorem a_mul_self : a * a = 1 := by
  rw [← z_eq_a]
  exact z_mul_self

theorem a_inv : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right a_mul_self

theorem abProd_invLetter
    (i : ℕ) : abProd (invLetter i) = (abLetter i)⁻¹ := by
  by_cases h : i = 1
  · subst h
    rw [invLetter, ite_eq_left rfl, abProd_cons, abProd_nil, mul_one, abLetter_one, a_inv]
  · rw [invLetter, ite_eq_right h, abProd_cons, abProd_cons, abProd_nil, mul_one,
      abLetter_of_ne (by decide : (2 : ℕ) ≠ 1), abLetter_of_ne h, b_inv]

theorem abProd_invWord
    (w : List ℕ) : abProd (invWord w) = (abProd w)⁻¹ := by
  induction w with
  | nil => rw [invWord, List.reverse_nil, List.flatMap_nil, abProd_nil, inv_one]
  | cons i w ih =>
    have e : invWord (i :: w) = invWord w ++ invLetter i := by
      rw [invWord, invWord, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    rw [e, abProd_append, ih, abProd_invLetter, abProd_cons, mul_inv_rev]

end AllConj

namespace AllConj

theorem isRows_abProd_inv
    (w : List ℕ) : IsRows (abRows (invWord w)) (abProd w)⁻¹ := by
  rw [← abProd_invWord]
  exact isRows_abProd _

theorem isRows_fusionConjQ0 :
    IsRows rowsFusionQ0 fusionConjQ0 :=
  isRows_fusionConj (isRows_abProd _) (isRows_abProd_inv _) (isRows_q 0)

theorem isRows_fusionConjX :
    IsRows rowsFusionX fusionConjX :=
  isRows_fusionConj (isRows_abProd _) (isRows_abProd_inv _) isRows_x

private theorem native_fusion_facts :
    eqRows (mulRows rowsFusionQ0 (rowsQ 0)) (mulRows rowsA rowsFusionQ0) = true ∧
    eqRows (mulRows rowsFusionX rowsX) (mulRows rowsA rowsFusionX) = true :=
  Certificates.certificate10088

end AllConj

theorem fusionConjQ0_conj :
    fusionConjQ0 * q 0 * fusionConjQ0⁻¹ = a := by
  obtain ⟨h, -⟩ := AllConj.native_fusion_facts
  have e : fusionConjQ0 * q 0 = a * fusionConjQ0 :=
    (AllConj.isRows_fusionConjQ0.mul (isRows_q 0)).eq_of_eqRows
      (isRows_a.mul AllConj.isRows_fusionConjQ0) h
  rw [e, mul_inv_cancel_right]

theorem fusionConjX_conj :
    fusionConjX * x * fusionConjX⁻¹ = a := by
  obtain ⟨-, h⟩ := AllConj.native_fusion_facts
  have e : fusionConjX * x = a * fusionConjX :=
    (AllConj.isRows_fusionConjX.mul isRows_x).eq_of_eqRows
      (isRows_a.mul AllConj.isRows_fusionConjX) h
  rw [e, mul_inv_cancel_right]

theorem q0_conj_a :
    IsConj a (q 0) :=
  IsConj.symm (isConj_iff.mpr ⟨_, fusionConjQ0_conj⟩)

theorem x_conj_a :
    IsConj a x :=
  IsConj.symm (isConj_iff.mpr ⟨_, fusionConjX_conj⟩)

theorem isConj_a_of_mem_M
    {m : J} (hm : m ∈ M) (h2 : orderOf m = 2) : IsConj a m := by
  obtain ⟨k, -, h⟩ := max3_involution_representatives m hm h2
  have hmr : IsConj m (k * m * k⁻¹) := isConj_iff.mpr ⟨k, rfl⟩
  have har : IsConj a (k * m * k⁻¹) := by
    rcases h with h | h | h
    · rw [h, z_eq_a]
    · rw [h]
      exact q0_conj_a
    · rw [h]
      exact x_conj_a
  exact har.trans hmr.symm

theorem all_involutions_conjugate_of_card
    (hJ : Nat.card J = 90745943887872000) :
    ∀ u : J, orderOf u = 2 → IsConj a u := by
  intro u hu
  have hidx : ¬ 2 ∣ M.index := by
    have h := Subgroup.card_mul_index M
    rw [card_M, hJ] at h
    have h' : M.index = 976841775 := by omega
    rw [h']
    omega
  have hz : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨g, hg⟩ :=
    ShultStronglyClosedTI.OddPrimeInverters.exists_conj_mem_of_not_dvd_index M hidx hz
  have hord : orderOf (g * u * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu
  have hum : IsConj u (g * u * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  exact (isConj_a_of_mem_M hg hord).trans hum.symm

theorem involutions_isConj_of_card
    (hJ : Nat.card J = 90745943887872000) {u v : J}
    (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v :=
  (all_involutions_conjugate_of_card hJ u hu).symm.trans
    (all_involutions_conjugate_of_card hJ v hv)

theorem th_involutions_conjugate_of_card
    (hTh : Nat.card Blueprint.NativeSporadic.Th = 90745943887872000) :
    ∀ u : Blueprint.NativeSporadic.Th, orderOf u = 2 → IsConj (thEquivJ.symm a) u := by
  intro u hu
  have hJ : Nat.card J = 90745943887872000 := by
    rw [← hTh]
    exact (Nat.card_congr thEquivJ.toEquiv).symm
  have h := all_involutions_conjugate_of_card hJ (thEquivJ u)
    (by rw [MulEquiv.orderOf_eq]; exact hu)
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨thEquivJ.symm c, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hc, MulEquiv.symm_apply_apply]

theorem th_involutions_isConj_of_card
    (hTh : Nat.card Blueprint.NativeSporadic.Th = 90745943887872000)
    {u v : Blueprint.NativeSporadic.Th} (hu : orderOf u = 2) (hv : orderOf v = 2) : IsConj u v :=
  (th_involutions_conjugate_of_card hTh u hu).symm.trans
    (th_involutions_conjugate_of_card hTh v hv)

end CFSG.Sporadic.Th.Max3

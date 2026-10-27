module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import Certificates.Data.ParrottPSp43
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import Certificates.Certificate946005
public import Certificates.Certificate946016

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

local notation "P45" => Equiv.Perm (Fin 45)

theorem t_mem_Q : t ∈ QP45.originalSubgroup := by
  rw [QP45_closure]
  exact Subgroup.subset_closure (by simp [t])

theorem t_mem_A : t ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp [t])

theorem u_mem_Q : u ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok u).2 Certificates.certificate946005.u_mem_Q

theorem sigma1_mem_Q : sigma1 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok sigma1).2 Certificates.certificate946005.sigma1_mem_Q

theorem sigma2_mem_Q : sigma2 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok sigma2).2 Certificates.certificate946005.sigma2_mem_Q

theorem alpha1_mem_Q : alpha1 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok alpha1).2 Certificates.certificate946005.alpha1_mem_Q

theorem beta1_mem_Q : beta1 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok beta1).2 Certificates.certificate946005.beta1_mem_Q

theorem alpha2_mem_Q : alpha2 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok alpha2).2 Certificates.certificate946005.alpha2_mem_Q

theorem beta2_mem_Q : beta2 ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok beta2).2 Certificates.certificate946005.beta2_mem_Q

theorem beta_mem_Q : beta ∈ QP45.originalSubgroup :=
  (mem_iff_sift QP45 QP45_ok beta).2 Certificates.certificate946005.beta_mem_Q

theorem u_mem_A : u ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok u).2 Certificates.certificate946005.u_mem_A

theorem v_mem_A : v ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok v).2 Certificates.certificate946005.v_mem_A

theorem sigma1_mem_A : sigma1 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok sigma1).2 Certificates.certificate946005.sigma1_mem_A

theorem sigma2_mem_A : sigma2 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok sigma2).2 Certificates.certificate946005.sigma2_mem_A

theorem alpha1_mem_A : alpha1 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok alpha1).2 Certificates.certificate946005.alpha1_mem_A

theorem beta1_mem_A : beta1 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok beta1).2 Certificates.certificate946005.beta1_mem_A

theorem alpha2_mem_A : alpha2 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok alpha2).2 Certificates.certificate946005.alpha2_mem_A

theorem beta2_mem_A : beta2 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok beta2).2 Certificates.certificate946005.beta2_mem_A

theorem beta_mem_A : beta ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok beta).2 Certificates.certificate946005.beta_mem_A

theorem v_not_mem_Q : v ∉ QP45.originalSubgroup := by
  rw [mem_iff_sift QP45 QP45_ok v]
  exact Certificates.certificate946005.v_not_mem_Q

theorem t_sq : t * t = 1 := Certificates.certificate946005.t_sq

theorem t_ne_one : t ≠ 1 := Certificates.certificate946005.t_ne_one

theorem u_sq : u * u = 1 := Certificates.certificate946005.u_sq

theorem u_ne_one : u ≠ 1 := Certificates.certificate946005.u_ne_one

theorem v_sq : v * v = 1 := Certificates.certificate946005.v_sq

theorem v_ne_one : v ≠ 1 := Certificates.certificate946005.v_ne_one

theorem sigma1_cube : sigma1 ^ 3 = 1 := Certificates.certificate946005.sigma1_cube

theorem sigma1_ne_one : sigma1 ≠ 1 := Certificates.certificate946005.sigma1_ne_one

theorem sigma2_cube : sigma2 ^ 3 = 1 := Certificates.certificate946005.sigma2_cube

theorem sigma2_ne_one : sigma2 ≠ 1 := Certificates.certificate946005.sigma2_ne_one

theorem alpha1_sq : alpha1 * alpha1 = t := Certificates.certificate946005.alpha1_sq

theorem alpha2_sq : alpha2 * alpha2 = t := Certificates.certificate946005.alpha2_sq

theorem alpha2_pow_four : alpha2 ^ 4 = 1 := Certificates.certificate946005.alpha2_pow_four

theorem alpha2_sq_ne_one : alpha2 * alpha2 ≠ 1 := Certificates.certificate946005.alpha2_sq_ne_one

theorem beta2_sq : beta2 * beta2 = t := Certificates.certificate946005.beta2_sq

theorem beta_sq : beta * beta = u * t := Certificates.certificate946005.beta_sq

theorem beta_sq_ne_one : beta * beta ≠ 1 := Certificates.certificate946005.beta_sq_ne_one

theorem sigma1_conj_u : u * sigma1 * u⁻¹ = sigma2 := Certificates.certificate946005.sigma1_conj_u

theorem sigma1_mul_u : sigma1 * u = u * sigma2 := Certificates.certificate946005.sigma1_mul_u

theorem sigma1_conj_v : v * sigma1 * v⁻¹ = sigma1⁻¹ := Certificates.certificate946005.sigma1_conj_v

theorem sigma2_conj_v : v * sigma2 * v⁻¹ = sigma2⁻¹ := Certificates.certificate946005.sigma2_conj_v

theorem u_commute_v : u * v = v * u := Certificates.certificate946005.u_commute_v

theorem t_commute_u : t * u = u * t := Certificates.certificate946005.t_commute_u

theorem t_commute_v : t * v = v * t := Certificates.certificate946005.t_commute_v

theorem t_commute_sigma1 : t * sigma1 = sigma1 * t := Certificates.certificate946005.t_commute_sigma1

theorem t_commute_sigma2 : t * sigma2 = sigma2 * t := Certificates.certificate946005.t_commute_sigma2

theorem t_commute_alpha1 : t * alpha1 = alpha1 * t := Certificates.certificate946005.t_commute_alpha1

theorem t_commute_beta1 : t * beta1 = beta1 * t := Certificates.certificate946005.t_commute_beta1

theorem t_commute_alpha2 : t * alpha2 = alpha2 * t := Certificates.certificate946005.t_commute_alpha2

theorem t_commute_beta2 : t * beta2 = beta2 * t := Certificates.certificate946005.t_commute_beta2

theorem sigma1_commute_sigma2 : sigma1 * sigma2 = sigma2 * sigma1 := Certificates.certificate946005.sigma1_commute_sigma2

theorem alpha1_commute_alpha2 : alpha1 * alpha2 = alpha2 * alpha1 := Certificates.certificate946005.alpha1_commute_alpha2

theorem beta1_commute_beta2 : beta1 * beta2 = beta2 * beta1 := Certificates.certificate946005.beta1_commute_beta2

theorem alpha2_beta2_alpha2 : alpha2 * beta2 * alpha2 = beta2 := Certificates.certificate946005.alpha2_beta2_alpha2

theorem beta_mul_u : beta * u = t * beta := Certificates.certificate946005.beta_mul_u

theorem beta_mul_u_mul_beta : beta * u * beta = u := Certificates.certificate946005.beta_mul_u_mul_beta

section O3Certificate

@[expose] def O3sub : Subgroup P45 where
  carrier := {x | x ∈ O3 ()}
  mul_mem' := by
    intro x y hx hy
    have hxall : (O3 ()).all (fun z => decide (x * z ∈ O3 ())) = true :=
      List.all_eq_true.1 Certificates.certificate946016.o3_mul_closed x hx
    exact of_decide_eq_true (List.all_eq_true.1 hxall y hy)
  one_mem' := Certificates.certificate946016.o3_one_mem
  inv_mem' := by
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.1 Certificates.certificate946016.o3_inv_closed x hx)

@[expose] def s1sub : ↥O3sub := ⟨sigma1, Certificates.certificate946016.sigma1_mem_O3⟩

theorem card_O3sub : Nat.card O3sub = 27 := by
  let e : O3sub ≃ {x // x ∈ (O3 ()).toFinset} :=
    { toFun := fun x => (⟨x.1, List.mem_toFinset.mpr x.2⟩ : {x // x ∈ (O3 ()).toFinset})
      invFun := fun x => (⟨x.1, List.mem_toFinset.mp x.2⟩ : ↥O3sub)
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  calc
    Nat.card O3sub = Nat.card {x // x ∈ (O3 ()).toFinset} := Nat.card_congr e
    _ = ((O3 ()).toFinset).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = (O3 ()).length := by rw [List.toFinset_card_of_nodup Certificates.certificate946016.o3_nodup]
    _ = 27 := Certificates.certificate946016.o3_length

theorem sigma1_mem_center_O3sub : s1sub ∈ Subgroup.center O3sub := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hs1 : (s1sub : P45) = sigma1 := rfl
  apply Subtype.ext
  have hz : decide ((y : P45) * sigma1 = sigma1 * (y : P45)) = true :=
    List.all_eq_true.1 Certificates.certificate946016.O3_le_centralizer_sigma1 (y : P45) y.2
  have hy : (y : P45) * sigma1 = sigma1 * (y : P45) := of_decide_eq_true hz
  simpa only [Subgroup.coe_mul, hs1] using hy

theorem center_O3sub : Subgroup.center O3sub = Subgroup.zpowers s1sub := by
  apply le_antisymm
  · intro x hx
    have hs1 : (s1sub : P45) = sigma1 := rfl
    have hxall : (O3 ()).all (fun y => decide ((x : P45) * y = y * (x : P45))) = true := by
      apply List.all_eq_true.2
      intro y hy
      have hcomm : (x : ↥O3sub) * (⟨y, hy⟩ : ↥O3sub) = (⟨y, hy⟩ : ↥O3sub) * (x : ↥O3sub) := by
        rw [Subgroup.mem_center_iff] at hx
        exact (hx ⟨y, hy⟩).symm
      exact decide_eq_true (congrArg Subtype.val hcomm)
    have hxmem : (x : P45) ∈
        (O3 ()).filter (fun z => (O3 ()).all (fun y => decide (z * y = y * z))) :=
      List.mem_filter.2 ⟨x.2, hxall⟩
    have hxfin : (x : P45) ∈ ({1, sigma1, sigma1 * sigma1} : Finset P45) := by
      rw [← Certificates.certificate946016.center_O3]
      exact List.mem_toFinset.2 hxmem
    rw [Subgroup.mem_zpowers_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxfin
    rcases hxfin with h1 | h2 | h3
    · refine ⟨0, Subtype.ext ?_⟩
      simpa [hs1] using h1.symm
    · refine ⟨1, Subtype.ext ?_⟩
      simpa [hs1] using h2.symm
    · refine ⟨2, Subtype.ext ?_⟩
      simpa [hs1, pow_two] using h3.symm
  · rw [Subgroup.zpowers_le]
    exact sigma1_mem_center_O3sub

end O3Certificate

end CFSG.RankThree.GF2n.Parrott

module

public import CFSG.Quasithin.H13.NQCatParabolicSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.Quasithin.H13.NQCat.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (unitri isUnitriangular_unitri inv_unitri)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def xA (t : K) : StatedSp 2 K :=
  pairRootElt (a := Sum.inl 0) (b := Sum.inl 1) (by simp) t
@[expose] def xB (t : K) : StatedSp 2 K :=
  pairRootElt (a := Sum.inl 1) (b := Sum.inr 1) (by simp) t
@[expose] def xAB (t : K) : StatedSp 2 K :=
  pairRootElt (a := Sum.inl 0) (b := Sum.inr 1) (by simp) t
@[expose] def xC (t : K) : StatedSp 2 K :=
  pairRootElt (a := Sum.inl 0) (b := Sum.inr 0) (by simp) t

theorem spMat_xA (t : K) : spMat (xA t) =
    1 + t • single (Sum.inl 0) (Sum.inl 1) 1 - t • single (Sum.inr 1) (Sum.inr 0) 1 :=
  pairRootMat_inl_inl t

theorem spMat_xB (t : K) : spMat (xB t) = 1 + t • single (Sum.inl 1) (Sum.inr 1) 1 :=
  pairRootMat_inl_inr_self 1 t

theorem spMat_xAB (t : K) : spMat (xAB t) =
    1 + t • (single (Sum.inl 0) (Sum.inr 1) 1 + single (Sum.inl 1) (Sum.inr 0) 1) :=
  pairRootMat_inl_inr (by decide) t

theorem spMat_xC (t : K) : spMat (xC t) = 1 + t • single (Sum.inl 0) (Sum.inr 0) 1 :=
  pairRootMat_inl_inr_self 0 t

theorem comm_xA_xB [CharP K 2] (t u : K) : ⁅xA t, xB u⁆ = xAB (t * u) * xC (t ^ 2 * u) := by
  have hiA : (xA t)⁻¹ = xA (-t) := (root_matrix_data (r := 2) (K := K)).1 _ _ _ 0 t |>.2.2.1
  have hiB : (xB u)⁻¹ = xB (-u) := (root_matrix_data (r := 2) (K := K)).1 _ _ _ 0 u |>.2.2.1
  rw [commutatorElement_def, hiA, hiB]
  apply statedSp_ext
  change spMat (xA t) * spMat (xB u) * spMat (xA (-t)) * spMat (xB (-u)) =
    spMat (xAB (t * u)) * spMat (xC (t ^ 2 * u))
  rw [spMat_xA, spMat_xB, spMat_xA, spMat_xB, spMat_xAB, spMat_xC]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply,
      Matrix.one_apply, CharTwo.neg_eq] <;> ring_nf <;> simp [h2]

theorem spLevi_one_up2 (t : K) : spLevi 1 (up2 t) = xA t := by
  apply statedSp_ext
  change spMat (spLevi 1 (up2 t)) = spMat (xA t)
  have hi : (up2 t)⁻¹ = up2 (-t) := by
    rw [inv_eq_iff_mul_eq_one]
    apply Subtype.ext
    show !![(1 : K), t; 0, 1] * !![1, -t; 0, 1] = 1
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [spMat_leviSp_one, hi, spMat_xA]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [up2]

theorem spLevi_zero_up2 (t : K) : spLevi 0 (up2 t) = xB t := by
  apply statedSp_ext
  change spMat (spLevi 0 (up2 t)) = spMat (xB t)
  rw [spMat_lam, spMat_xB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [up2, pairMat, Matrix.one_apply]

@[expose] def dS (j : Fin 2) (s : Kˣ) : Fin 2 ⊕ Fin 2 → K :=
  if j = 0 then Sum.elim ![1, (s : K)] ![1, ((s⁻¹ : Kˣ) : K)]
  else Sum.elim ![(s : K), ((s⁻¹ : Kˣ) : K)] ![((s⁻¹ : Kˣ) : K), (s : K)]

theorem spMat_spLevi_dg2 (j : Fin 2) (s : Kˣ) :
    spMat (spLevi j (dg2 s)) = diagonal (dS j s) := by
  rcases fin_two_cases j with rfl | rfl
  · rw [spMat_lam]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [dg2, pairMat, dS]
  · rw [spMat_leviSp_one, dg2_inv]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [dg2, dS]

theorem spMat_spLevi_dg2_inv (j : Fin 2) (s : Kˣ) :
    spMat (spLevi j (dg2 s))⁻¹ = diagonal (dS j s⁻¹) := by
  rw [← map_inv, dg2_inv, spMat_spLevi_dg2]

theorem xA_mul (s t : K) : xA s * xA t = xA (s + t) :=
  ((root_matrix_data (r := 2) (K := K)).1 _ _ (by simp) s t).2.1
theorem xB_mul (s t : K) : xB s * xB t = xB (s + t) :=
  ((root_matrix_data (r := 2) (K := K)).1 _ _ (by simp) s t).2.1
theorem xAB_mul (s t : K) : xAB s * xAB t = xAB (s + t) :=
  ((root_matrix_data (r := 2) (K := K)).1 _ _ (by simp) s t).2.1
theorem xC_mul (s t : K) : xC s * xC t = xC (s + t) :=
  ((root_matrix_data (r := 2) (K := K)).1 _ _ (by simp) s t).2.1

theorem conj_one_xB (s : Kˣ) (t : K) :
    spLevi 1 (dg2 s) * xB t * (spLevi 1 (dg2 s))⁻¹ = xB (((s⁻¹ : Kˣ) : K) ^ 2 * t) := by
  apply statedSp_ext
  change spMat (spLevi 1 (dg2 s)) * spMat (xB t) * spMat (spLevi 1 (dg2 s))⁻¹ =
    spMat (xB _)
  rw [spMat_spLevi_dg2, spMat_spLevi_dg2_inv, spMat_xB, spMat_xB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b
  all_goals simp [dS]
  all_goals ring

theorem conj_one_xC (s : Kˣ) (t : K) :
    spLevi 1 (dg2 s) * xC t * (spLevi 1 (dg2 s))⁻¹ = xC ((s : K) ^ 2 * t) := by
  apply statedSp_ext
  change spMat (spLevi 1 (dg2 s)) * spMat (xC t) * spMat (spLevi 1 (dg2 s))⁻¹ =
    spMat (xC _)
  rw [spMat_spLevi_dg2, spMat_spLevi_dg2_inv, spMat_xC, spMat_xC]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b
  all_goals simp [dS]
  all_goals ring

theorem conj_zero_xA (s : Kˣ) (t : K) :
    spLevi 0 (dg2 s) * xA t * (spLevi 0 (dg2 s))⁻¹ = xA (((s⁻¹ : Kˣ) : K) * t) := by
  apply statedSp_ext
  change spMat (spLevi 0 (dg2 s)) * spMat (xA t) * spMat (spLevi 0 (dg2 s))⁻¹ =
    spMat (xA _)
  rw [spMat_spLevi_dg2, spMat_spLevi_dg2_inv, spMat_xA, spMat_xA]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b
  all_goals simp [dS]
  all_goals ring

theorem conj_zero_xAB (s : Kˣ) (t : K) :
    spLevi 0 (dg2 s) * xAB t * (spLevi 0 (dg2 s))⁻¹ = xAB ((s : K) * t) := by
  apply statedSp_ext
  change spMat (spLevi 0 (dg2 s)) * spMat (xAB t) * spMat (spLevi 0 (dg2 s))⁻¹ =
    spMat (xAB _)
  rw [spMat_spLevi_dg2, spMat_spLevi_dg2_inv, spMat_xAB, spMat_xAB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b
  all_goals simp [dS]
  all_goals ring

theorem mem_unipotent_of (x c₀ c₁ c₂ : K) {g : StatedSp 2 K}
    (h : spMat g = blockMat (unitri x) !![c₀, c₁; c₁, c₂]) : g ∈ unipotent 2 K := by
  refine ⟨unitri x, !![c₀, c₁; c₁, c₂], isUnitriangular_unitri x, ?_, h⟩
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem xA_mem (t : K) : xA t ∈ unipotent 2 K := by
  refine mem_unipotent_of t 0 0 0 ?_
  rw [spMat_xA, blockMat, inv_unitri]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [unitri]

theorem xB_mem (t : K) : xB t ∈ unipotent 2 K := by
  refine mem_unipotent_of 0 0 0 t ?_
  rw [spMat_xB, blockMat, inv_unitri]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [unitri]

theorem xAB_mem (t : K) : xAB t ∈ unipotent 2 K := by
  refine mem_unipotent_of 0 0 t 0 ?_
  rw [spMat_xAB, blockMat, inv_unitri]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [unitri]

theorem xC_mem (t : K) : xC t ∈ unipotent 2 K := by
  refine mem_unipotent_of 0 t 0 0 ?_
  rw [spMat_xC, blockMat, inv_unitri]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> simp [unitri]

theorem exists_eq_prod_of_mem_unipotent {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K) :
    ∃ x c₀ c₁ c₂ : K, u = xA x * xC c₀ * xAB c₁ * xB c₂ := by
  obtain ⟨A, C, hA, hC, hu⟩ := hu
  refine ⟨A 0 1, C 0 0, C 0 1, C 1 1, ?_⟩
  have hA' : A = unitri (A 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hA.2 0
    · rfl
    · exact hA.1 (show (0 : Fin 2) < 1 by decide)
    · exact hA.2 1
  have hC' : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    rwa [transpose_apply] at this
  apply statedSp_ext
  change spMat u = spMat (xA _) * spMat (xC _) * spMat (xAB _) * spMat (xB _)
  rw [show spMat u = blockMat A C from hu, blockMat, hA', inv_unitri, spMat_xA, spMat_xC,
    spMat_xAB, spMat_xB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [unitri, single_apply, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type, hC',
      Matrix.vecMul, dotProduct] <;> ring

theorem unipotent_le_perfectCore [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    unipotent 2 K ≤ perfectCore (Q2 K j) := by
  obtain ⟨s, hs1⟩ := exists_unit_ne_one hK4
  have hsi1 := units_inv_ne_one hs1
  have hsq : ∀ x : K, x ≠ 1 → x ^ 2 ≠ 1 := fun x hx h =>
    hx (CharTwo.sq_injective (h.trans (one_pow 2).symm))
  set H := unipotent 2 K ⊔ (spLevi (K := K) j).range with hH
  have hUH : unipotent 2 K ≤ H := le_sup_left
  have hLH : (spLevi (K := K) j).range ≤ H := le_sup_right
  have hL : (spLevi (K := K) j).range ≤ ⁅H, H⁆ := by
    rw [← spLevi_range_perfect hK4 j]
    exact Subgroup.commutator_mono hLH hLH
  have hdH : spLevi j (dg2 s) ∈ H := hLH ⟨_, rfl⟩
  have hcomm : ∀ c : K, ⁅xA (1 : K), xB c⁆ ∈ ⁅H, H⁆ := fun c =>
    Subgroup.commutator_mem_commutator (hUH (xA_mem 1)) (hUH (xB_mem c))
  have hrel : ∀ c : K, ⁅xA (1 : K), xB c⁆ = xAB c * xC c := fun c => by
    rw [comm_xA_xB, one_mul, one_pow, one_mul]
  have hU : unipotent 2 K ≤ ⁅H, H⁆ := by
    intro u hu
    obtain ⟨x, c₀, c₁, c₂, rfl⟩ := exists_eq_prod_of_mem_unipotent hu
    rcases fin_two_cases j with rfl | rfl
    · have hA : ∀ t, xA t ∈ ⁅H, H⁆ := root_mem_commutator xA xA_mul _ _ hsi1
        (conj_zero_xA s) hdH (fun t => hUH (xA_mem t))
      have hAB : ∀ t, xAB t ∈ ⁅H, H⁆ := root_mem_commutator xAB xAB_mul _ _ hs1
        (conj_zero_xAB s) hdH (fun t => hUH (xAB_mem t))
      have hC : xC c₀ ∈ ⁅H, H⁆ := by
        have e : xC c₀ = (xAB c₀)⁻¹ * ⁅xA (1 : K), xB c₀⁆ := by rw [hrel, inv_mul_cancel_left]
        rw [e]
        exact mul_mem (inv_mem (hAB c₀)) (hcomm c₀)
      have hB : xB c₂ ∈ ⁅H, H⁆ := by
        rw [← spLevi_zero_up2]
        exact hL ⟨_, rfl⟩
      exact mul_mem (mul_mem (mul_mem (hA x) hC) (hAB c₁)) hB
    · have hB : ∀ t, xB t ∈ ⁅H, H⁆ := root_mem_commutator xB xB_mul _ _ (hsq _ hsi1)
        (conj_one_xB s) hdH (fun t => hUH (xB_mem t))
      have hC : ∀ t, xC t ∈ ⁅H, H⁆ := root_mem_commutator xC xC_mul _ _ (hsq _ hs1)
        (conj_one_xC s) hdH (fun t => hUH (xC_mem t))
      have hAB : xAB c₁ ∈ ⁅H, H⁆ := by
        have e : xAB c₁ = ⁅xA (1 : K), xB c₁⁆ * (xC c₁)⁻¹ := by rw [hrel, mul_inv_cancel_right]
        rw [e]
        exact mul_mem (hcomm c₁) (inv_mem (hC c₁))
      have hA : xA x ∈ ⁅H, H⁆ := by
        rw [← spLevi_one_up2]
        exact hL ⟨_, rfl⟩
      exact mul_mem (mul_mem (mul_mem hA (hC c₀)) hAB) (hB c₂)
  have hperf : ⁅H, H⁆ = H :=
    le_antisymm (CFSG.Quasithin.A3.commutator_self_le H) (sup_le hU hL)
  have hHQ : H ≤ Q2 K j := sup_le (unipotent_le_borelSubgroup.trans (borelSubgroup_le_Q2 j))
    (by rintro _ ⟨A, rfl⟩; exact spLevi_mem j A)
  exact hUH.trans (le_perfectCore_of_perfect hHQ hperf)

theorem not_isSolvable_perfectCore [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (j : Fin 2) : ¬ Group.IsSolvable (perfectCore (Q2 K j)) := by
  intro h
  have := sl2_isSimple hK4
  obtain ⟨a, b, hab⟩ := sl2_nonabelian hK4
  have hs : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_surjective (blkN_surjective hK4 j)
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem perfectCore_sup_eq_top [Finite K] [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) : perfectCore (Q2 K 0) ⊔ perfectCore (Q2 K 1) = ⊤ := by
  by_contra hne
  have hU : unipotent 2 K ≤ perfectCore (Q2 K 0) ⊔ perfectCore (Q2 K 1) :=
    (unipotent_le_perfectCore hK4 0).trans le_sup_left
  have hB := isSolvable_borelSubgroup (r := 2) (K := K) hK
  have hinf : Q2 K 0 ⊓ Q2 K 1 = borelSubgroup 2 K :=
    CFSG.QuasithinUnique.Setup.X6.inf_eq_of_covBy (covBy_Q2 0) (covBy_Q2 1) Q2_ne
  have key : ∀ j : Fin 2, perfectCore (Q2 K j) ≤ borelSubgroup 2 K → False := fun j hj =>
    not_isSolvable_perfectCore hK4 j
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hj)
        (Subgroup.inclusion_injective hj))
  rcases contained_in_Q2 hU hne with h | h
  · exact key 1 (hinf ▸ le_inf (le_sup_right.trans h) (CFSG.Quasithin.perfectCore_le _))
  · exact key 0 (hinf ▸ le_inf (CFSG.Quasithin.perfectCore_le _) (le_sup_left.trans h))

theorem le_borelSubgroup_of_isSolvable [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) {A : Subgroup (StatedSp 2 K)} (hU : unipotent 2 K ≤ A)
    (hA : Group.IsSolvable A) : A ≤ borelSubgroup 2 K := by
  have hle :=
    ((symplectic_unitriangular_overgroup_subflag_containment (r := 2) (K := K)).1 A hU).1
  have hr : ∀ k : Fin 2, weylRep K k ∉ A := by
    intro k hk
    have hH : H2 K (Fin.rev k) ≤ A := by
      change spWeylGroup K (Fin.rev (Fin.rev k)) ≤ A
      rw [Fin.rev_rev]
      exact sup_le hU ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr hk))
    have hpc : perfectCore (Q2 K (Fin.rev k)) ≤ A :=
      ((perfectCore_le_commutator _).trans (commutator_Q2_le _)).trans hH
    exact not_isSolvable_perfectCore hK4 _
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hpc)
        (Subgroup.inclusion_injective hpc))
  have hcuts : borelCuts K A = {1, 2} := by
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, rfl, -⟩
      have := k.isLt
      omega
    · intro hi
      rcases hi with rfl | rfl
      · exact (succ_mem_borelCuts_iff A 0).mpr (hr 0)
      · exact (succ_mem_borelCuts_iff A 1).mpr (hr 1)
  rw [borelSubgroup_eq_flagStabilizer, ← hcuts]
  exact hle

end CFSG.Quasithin.H13.NQCat.Sp4

module

public import CFSG.Quasithin.Vol2.Ch11SecBK9F
public import CFSG.Quasithin.Vol2.Ch11SecBK7D
public import CFSG.Quasithin.Vol2.Ch11SecBK7B

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] [CharP K 2]

theorem exists_smul_of_tr_perp [Finite K] (hK : Nat.card K = 4) {y u : Fin 2 ⊕ Fin 2 → K}
    (hy : y ≠ 0) (h : ∀ x, spB K x y = 0 → tr (spB K u x) = 0) : ∃ μ : K, u = μ • y := by
  obtain ⟨x₀, hx₀⟩ := K7.exists_bil_eq_one hy
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  have h0 : ∀ x, spB K x y = 0 → spB K u x = 0 := by
    intro x hx
    by_contra hne
    have h1 := h ((ω / spB K u x) • x) (by rw [K7.bil_smul_left, hx, mul_zero])
    rw [K7.bil_smul_right, div_mul_cancel₀ _ hne, tr_omega hω] at h1
    exact one_ne_zero h1
  refine ⟨spB K u x₀, ?_⟩
  rw [← sub_eq_zero]
  apply KGNat.toBilin'_spJ_nondegenerate.1
  intro x
  have hperp : spB K (x - spB K x y • x₀) y = 0 := by
    rw [sub_eq_add_neg, K7.bil_add_left, ← neg_smul, K7.bil_smul_left, hx₀]
    ring
  have h1 := h0 _ hperp
  rw [sub_eq_add_neg, K7.bil_add_right, ← neg_smul, K7.bil_smul_right] at h1
  rw [sub_eq_add_neg, K7.bil_add_left, ← neg_smul, K7.bil_smul_left, K7.bil_comm y x]
  linear_combination h1

namespace CovData

variable {W : Type*} [CommGroup W] (C : CovData K W)

abbrev pi' (γ : ↥(StatedSp 2 K)) : MulAut W := ((C.π γ : ↥C.H) : MulAut W)

theorem f_pi (γ : ↥(StatedSp 2 K)) (w : W) : C.f (C.pi' γ w) = mat 2 K γ *ᵥ C.f w :=
  C.coord.act4 γ w

theorem pi'_mul (γ δ : ↥(StatedSp 2 K)) : C.pi' (γ * δ) = C.pi' γ * C.pi' δ := by
  simp only [pi', map_mul, Subgroup.coe_mul]

theorem pi'_inv (γ : ↥(StatedSp 2 K)) : C.pi' γ⁻¹ = (C.pi' γ)⁻¹ := by
  simp only [pi', map_inv, Subgroup.coe_inv]

theorem f_pi_symm (γ : ↥(StatedSp 2 K)) (w : W) :
    C.f ((C.pi' γ).symm w) = mat 2 K γ⁻¹ *ᵥ C.f w := by
  rw [← C.f_pi, C.pi'_inv]
  rfl

theorem index_map (γ : ↥(StatedSp 2 K)) (U : Subgroup W) :
    (U.map (C.pi' γ).toMonoidHom).index = U.index :=
  Subgroup.index_map_equiv U (C.pi' γ)

theorem z_not_mem_map (γ : ↥(StatedSp 2 K)) {U : Subgroup W} (hz : C.z ∉ U) :
    C.z ∉ U.map (C.pi' γ).toMonoidHom := by
  rw [Subgroup.mem_map_equiv]
  intro h
  apply hz
  have h1 : (C.pi' γ).symm C.z = C.z := by
    rw [MulEquiv.symm_apply_eq]
    exact (C.pi_z γ).symm
  rwa [h1] at h

theorem compl_zero : C.compl 0 = C.U₀ := by
  ext w
  rw [mem_compl, chi, map_zero, LinearMap.zero_apply, tr_zero, add_zero, ind_eq_zero_iff]

variable [Finite K]

@[expose] noncomputable def kappa (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) :
    Fin 2 ⊕ Fin 2 → K :=
  (C.exists_eq_compl hK (by rw [C.index_map]; exact C.index₀)
    (C.z_not_mem_map γ C.z_not_mem₀)).choose

theorem map_U₀ (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) :
    C.U₀.map (C.pi' γ).toMonoidHom = C.compl (C.kappa hK γ) :=
  (C.exists_eq_compl hK (by rw [C.index_map]; exact C.index₀)
    (C.z_not_mem_map γ C.z_not_mem₀)).choose_spec

theorem ind_symm (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) (w : W) :
    ind (K := K) C.U₀ ((C.pi' γ).symm w) = C.chi (C.kappa hK γ) w := by
  have h : (C.pi' γ).symm w ∈ C.U₀ ↔ w ∈ C.compl (C.kappa hK γ) := by
    rw [← C.map_U₀ hK γ, Subgroup.mem_map_equiv]
  rw [mem_compl] at h
  rcases ind_cases (K := K) C.U₀ ((C.pi' γ).symm w) with h1 | h1 <;>
    rcases C.chi_cases hK (C.kappa hK γ) w with h2 | h2 <;> rw [h1, h2]
  · exact absurd (h.mp (ind_eq_zero_iff.mp h1)) (by rw [h2]; exact one_ne_zero)
  · exact absurd (h.mpr h2) (by rw [← ind_eq_zero_iff (K := K), h1]; exact one_ne_zero)

theorem map_compl (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) (a : Fin 2 ⊕ Fin 2 → K) :
    (C.compl a).map (C.pi' γ).toMonoidHom = C.compl (mat 2 K γ *ᵥ a + C.kappa hK γ) := by
  ext w
  have hB : spB K a (mat 2 K γ⁻¹ *ᵥ C.f w) = spB K (mat 2 K γ *ᵥ a) (C.f w) := by
    rw [← KGNat.spB_mat γ a, KGNat.mat_mulVec_inv]
  rw [Subgroup.mem_map_equiv, mem_compl, mem_compl, chi, C.ind_symm hK γ, C.f_pi_symm, chi, chi,
    spB_add_left, tr_add, hB]
  constructor <;> intro h <;> linear_combination h

theorem map_pi'_mul (γ δ : ↥(StatedSp 2 K)) (U : Subgroup W) :
    U.map (C.pi' (γ * δ)).toMonoidHom =
      (U.map (C.pi' δ).toMonoidHom).map (C.pi' γ).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext w
  simp only [C.pi'_mul, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
    MulAut.mul_apply]

theorem kappa_mul (hK : Nat.card K = 4) (γ δ : ↥(StatedSp 2 K)) :
    C.kappa hK (γ * δ) = C.kappa hK γ + mat 2 K γ *ᵥ C.kappa hK δ := by
  apply C.compl_injective hK
  rw [← C.map_U₀, C.map_pi'_mul, C.map_U₀, C.map_compl, add_comm]

theorem exists_kappa_trv (hK : Nat.card K = 4) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (t : K) :
    ∃ μ : K, C.kappa hK (K7.trv y t) = μ • y := by
  apply exists_smul_of_tr_perp hK hy
  intro x hx
  obtain ⟨w, rfl⟩ := C.coord.surj x
  have hfix : C.pi' (K7.trv y t) w = w := K7.trv_fix C.coord C.fixZ hy t hx
  have hsymm : (C.pi' (K7.trv y t)).symm w = w := by
    rw [MulEquiv.symm_apply_eq]
    exact hfix.symm
  have h1 := C.ind_symm hK (K7.trv y t) w
  rw [hsymm, chi] at h1
  linear_combination -h1

end CovData

end CFSG.Quasithin.Vol2.Ch11.SecB.K9

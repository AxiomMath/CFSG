module

public import CFSG.Quasithin.Vol2.Ch11SecBK7A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace K7

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

@[expose] def acomm (π : ↥(StatedSp 2 K) →* ↥H) (y : Fin 2 ⊕ Fin 2 → K) : Subgroup W :=
  Subgroup.closure {a | ∃ (c : K) (w : W), ((π (trv y c) : ↥H) : MulAut W) w * w⁻¹ = a}

theorem gen_mem_acomm (π : ↥(StatedSp 2 K) →* ↥H) (y : Fin 2 ⊕ Fin 2 → K) (c : K) (w : W) :
    ((π (trv y c) : ↥H) : MulAut W) w * w⁻¹ ∈ acomm π y :=
  Subgroup.subset_closure ⟨c, w, rfl⟩

theorem f_gen (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (y : Fin 2 ⊕ Fin 2 → K)
    (c : K) (w : W) : f (((π (trv y c) : ↥H) : MulAut W) w * w⁻¹) =
      (c * Matrix.toBilin' (spJ K) (f w) y) • y := by
  rw [hf.map_mul_inv, hf.act4, trv_mulVec, add_sub_cancel_left]

theorem exists_smul_of_mem_acomm (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {y : Fin 2 ⊕ Fin 2 → K} {a : W} (ha : a ∈ acomm π y) : ∃ d : K, f a = d • y := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, rfl⟩ := hx
    exact ⟨_, f_gen hf y c w⟩
  | one => exact ⟨0, by rw [hf.map_one, zero_smul]⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hx'
    exact ⟨d + d', by rw [hf.map_mul, hd, hd', add_smul]⟩
  | inv x _ hx =>
    obtain ⟨d, hd⟩ := hx
    exact ⟨-d, by rw [hf.map_inv, hd, neg_smul]⟩

theorem exists_bil_eq_one {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) :
    ∃ x, Matrix.toBilin' (spJ K) x y = 1 := by
  by_contra h
  push Not at h
  have h0 : ∀ x, Matrix.toBilin' (spJ K) x y = 0 := by
    intro x
    by_contra hx
    apply h ((Matrix.toBilin' (spJ K) x y)⁻¹ • x)
    rw [bil_smul_left, inv_mul_cancel₀ hx]
  exact hy (toBilin'_spJ_nondegenerate.2 y h0)

theorem exists_mem_acomm (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (d : K) : ∃ a ∈ acomm π y, f a = d • y := by
  obtain ⟨x, hx⟩ := exists_bil_eq_one hy
  obtain ⟨w, hw⟩ := hf.surj x
  exact ⟨_, gen_mem_acomm π y d w, by rw [f_gen hf, hw, hx, mul_one]⟩

theorem map_mem_acomm (γ : ↥(StatedSp 2 K)) {y : Fin 2 ⊕ Fin 2 → K} {a : W}
    (ha : a ∈ acomm π y) : ((π γ : ↥H) : MulAut W) a ∈ acomm π (mat 2 K γ *ᵥ y) := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, w, rfl⟩ := hx
    have e : γ * trv y c = trv (mat 2 K γ *ᵥ y) c * γ := by
      rw [← trv_conj, inv_mul_cancel_right]
    have h1 : ((π γ : ↥H) : MulAut W) (((π (trv y c) : ↥H) : MulAut W) w * w⁻¹) =
        ((π (trv (mat 2 K γ *ᵥ y) c) : ↥H) : MulAut W) (((π γ : ↥H) : MulAut W) w) *
          (((π γ : ↥H) : MulAut W) w)⁻¹ := by
      rw [map_mul, map_inv, ← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, e, map_mul,
        Subgroup.coe_mul, MulAut.mul_apply]
    rw [h1]
    exact gen_mem_acomm π _ c _
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x x' _ _ hx hx' => rw [map_mul]; exact Subgroup.mul_mem _ hx hx'
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem acomm_smul_le (y : Fin 2 ⊕ Fin 2 → K) (a : K) :
    acomm π (a • y) ≤ acomm (W := W) π y := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨c, w, rfl⟩
  rw [trv_smul]
  exact gen_mem_acomm π y _ w

theorem acomm_smul {y : Fin 2 ⊕ Fin 2 → K} {a : K} (ha : a ≠ 0) :
    acomm π (a • y) = acomm (W := W) π y := by
  refine le_antisymm (acomm_smul_le y a) ?_
  have h := acomm_smul_le (W := W) (π := π) (a • y) a⁻¹
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h

theorem acomm_inf_le (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {y y' : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    (hy' : y' ≠ 0) : acomm π y ⊓ Z ≤ acomm π y' := by
  obtain ⟨γ, hγ⟩ := exists_sp4_lin_eq y y' hy hy'
  rw [linModelNat_lin] at hγ
  change mat 2 K γ *ᵥ y = y' at hγ
  rintro z ⟨hz, hzZ⟩
  have h1 := map_mem_acomm (π := π) γ hz
  change ((π γ : ↥H) : MulAut W) z ∈ acomm π (mat 2 K γ *ᵥ y) at h1
  rw [hZ _ (π γ).2 z hzZ, hγ] at h1
  exact h1

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB

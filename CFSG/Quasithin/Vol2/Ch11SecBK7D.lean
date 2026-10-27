module

public import CFSG.Quasithin.Vol2.Ch11SecBK7A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp nSp)

namespace K7

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem zeta_inv (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {y : Fin 2 ⊕ Fin 2 → K} (c : K)
    {γ : ↥(StatedSp 2 K)} (hγ : mat 2 K γ *ᵥ y = y) {w : W}
    (hw : ((π (trv y c) : ↥H) : MulAut W) w * w⁻¹ ∈ Z) :
    ((π (trv y c) : ↥H) : MulAut W) (((π γ : ↥H) : MulAut W) w) *
        (((π γ : ↥H) : MulAut W) w)⁻¹ = ((π (trv y c) : ↥H) : MulAut W) w * w⁻¹ := by
  have hc : ((π (trv y c) : ↥H) : MulAut W) (((π γ : ↥H) : MulAut W) w) =
      ((π γ : ↥H) : MulAut W) (((π (trv y c) : ↥H) : MulAut W) w) := by
    rw [← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, ← comm_trv hγ c, map_mul,
      Subgroup.coe_mul, MulAut.mul_apply]
  rw [hc, ← map_inv, ← map_mul, hZ _ (π γ).2 _ hw]

theorem zeta_kill (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {y : Fin 2 ⊕ Fin 2 → K} (c : K) {γ : ↥(StatedSp 2 K)}
    (hγ : mat 2 K γ *ᵥ y = y) {v v' : Fin 2 ⊕ Fin 2 → K} (hv : mat 2 K γ *ᵥ v = v + v')
    (hζ : ∀ w, f w = v → ((π (trv y c) : ↥H) : MulAut W) w * w⁻¹ ∈ Z) {w' : W}
    (hw' : f w' = v') : ((π (trv y c) : ↥H) : MulAut W) w' * w'⁻¹ = 1 := by
  set x := ((π (trv y c) : ↥H) : MulAut W) with hx
  obtain ⟨w, hw⟩ := hf.surj v
  have h1 : f (((π γ : ↥H) : MulAut W) w) = f (w * w') := by
    rw [hf.act4, hw, hv, hf.map_mul, hw, hw']
  obtain ⟨z, hz, hzw⟩ : ∃ z ∈ Z, ((π γ : ↥H) : MulAut W) w = w * w' * z :=
    ⟨_, (hf.eq_iff _ _).mp h1, by rw [mul_comm (((π γ : ↥H) : MulAut W) w), mul_inv_cancel_left]⟩
  have h2 := zeta_inv hZ c hγ (hζ w hw)
  rw [hzw] at h2
  have hxz : x z = z := hZ _ (π _).2 z hz
  rw [map_mul, map_mul, hxz] at h2
  have e : x w * x w' * z * (w * w' * z)⁻¹ = (x w * w⁻¹) * (x w' * w'⁻¹) := by
    rw [mul_inv, mul_inv]
    calc x w * x w' * z * (w⁻¹ * w'⁻¹ * z⁻¹) = (x w * w⁻¹) * (x w' * w'⁻¹) * (z * z⁻¹) := by
          ac_rfl
      _ = _ := by rw [mul_inv_cancel, mul_one]
  rw [e] at h2
  exact mul_eq_left.mp h2

theorem trv_e0_fix [CharP K 2] (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (c : K) {w : W} (hw : f w (.inr 0) = 0) :
    ((π (trv (vec4 1 0 0 0) c) : ↥H) : MulAut W) w = w := by
  set e₀ : Fin 2 ⊕ Fin 2 → K := vec4 1 0 0 0 with he₀
  set x := ((π (trv e₀ c) : ↥H) : MulAut W) with hx
  have hζ : ∀ u : W, f u (.inr 0) = 0 → x u * u⁻¹ ∈ Z := by
    intro u hu
    apply (hf.eq_iff _ _).mp
    rw [hx, hf.act4, trv_mulVec, bil_comm, spB_e0, hu, mul_zero, zero_smul, add_zero]
  have hζv : ∀ v : Fin 2 ⊕ Fin 2 → K, v (.inr 0) = 0 → ∀ u : W, f u = v → x u * u⁻¹ ∈ Z :=
    fun v hv u hu => hζ u (by rw [hu]; exact hv)
  have hq : ∀ t : K, mat 2 K (qSp 0 0 t) *ᵥ e₀ = e₀ := fun t => by
    rw [qSp_mulVec]
    exact vec4_eq (by simp [he₀, vec4]) (by simp [he₀, vec4]) (by simp [he₀, vec4])
      (by simp [he₀, vec4])
  have hn : ∀ t : K, mat 2 K (nSp t) *ᵥ e₀ = e₀ := fun t => by
    rw [nSp_mulVec]
    exact vec4_eq (by simp [he₀, vec4]) (by simp [he₀, vec4]) (by simp [he₀, vec4])
      (by simp [he₀, vec4])
  let lo : K → Matrix.SpecialLinearGroup (Fin 2) K := fun t =>
    ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩
  have hl : ∀ t : K, mat 2 K (spLevi 0 (lo t)) *ᵥ e₀ = e₀ := fun t => by
    rw [KA.spLevi0_mulVec]
    exact vec4_eq (by simp [he₀, vec4]) (by simp [he₀, vec4, lo]) (by simp [he₀, vec4])
      (by simp [he₀, vec4, lo])
  have k1 : ∀ t : K, ∀ u : W, f u = vec4 0 t 0 0 → x u * u⁻¹ = 1 := fun t u hu =>
    zeta_kill hf hZ c (hq t) (v := vec4 0 0 0 1) (by
      rw [qSp_mulVec]
      exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4]))
      (hζv _ rfl) hu
  have k3 : ∀ t : K, ∀ u : W, f u = vec4 0 0 0 t → x u * u⁻¹ = 1 := fun t u hu =>
    zeta_kill hf hZ c (hl t) (v := vec4 0 1 0 0) (by
      rw [KA.spLevi0_mulVec]
      exact vec4_eq (by simp [vec4]) (by simp [vec4, lo]) (by simp [vec4]) (by simp [vec4, lo]))
      (hζv _ rfl) hu
  have k0 : ∀ t : K, ∀ u : W, f u = vec4 t 0 0 0 → x u * u⁻¹ = 1 := fun t u hu =>
    zeta_kill hf hZ c (hn t) (v := vec4 0 1 0 0) (by
      rw [nSp_mulVec]
      exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4]))
      (hζv _ rfl) hu
  obtain ⟨u₀, hu₀⟩ := hf.surj (vec4 (f w (.inl 0)) 0 0 0)
  obtain ⟨u₁, hu₁⟩ := hf.surj (vec4 0 (f w (.inl 1)) 0 0)
  obtain ⟨u₃, hu₃⟩ := hf.surj (vec4 0 0 0 (f w (.inr 1)))
  have hfw : f w = f (u₀ * u₁ * u₃) := by
    rw [hf.map_mul, hf.map_mul, hu₀, hu₁, hu₃]
    exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4, hw]) (by simp [vec4])
  obtain ⟨z, hz, hzw⟩ : ∃ z ∈ Z, w = u₀ * u₁ * u₃ * z :=
    ⟨_, (hf.eq_iff _ _).mp hfw, by rw [mul_comm w, mul_inv_cancel_left]⟩
  have hxz : x z = z := hZ _ (π _).2 z hz
  have h0 := k0 _ u₀ hu₀
  have h1 := k1 _ u₁ hu₁
  have h3 := k3 _ u₃ hu₃
  rw [mul_inv_eq_one] at h0 h1 h3
  rw [hzw, map_mul, map_mul, map_mul, h0, h1, h3, hxz]

theorem trv_fix [CharP K 2] (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (c : K) {w : W}
    (hw : Matrix.toBilin' (spJ K) (f w) y = 0) :
    ((π (trv y c) : ↥H) : MulAut W) w = w := by
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨γ, hγ⟩ := exists_sp4_lin_eq _ y he0 hy
  rw [linModelNat_lin] at hγ
  change mat 2 K γ *ᵥ vec4 1 0 0 0 = y at hγ
  have htr : trv y c = γ * trv (vec4 1 0 0 0) c * γ⁻¹ := by rw [trv_conj, hγ]
  set w' := ((π γ⁻¹ : ↥H) : MulAut W) w with hw'
  have hw'0 : f w' (.inr 0) = 0 := by
    rw [hw', hf.act4, ← spB_e0 (mat 2 K γ⁻¹ *ᵥ f w), ← spB_mat γ (vec4 1 0 0 0),
      mat_mulVec_inv, hγ, bil_comm, hw]
  have h1 := trv_e0_fix hf hZ c hw'0
  rw [htr, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply,
    MulAut.mul_apply]
  rw [← hw', h1, hw', ← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel,
    map_one, Subgroup.coe_one, MulAut.one_apply]

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB

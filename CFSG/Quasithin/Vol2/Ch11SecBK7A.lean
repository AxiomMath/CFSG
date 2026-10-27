module

public import CFSG.Quasithin.Vol2.Ch11SecAKA8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

namespace K7

variable {K : Type} [Field K]

theorem bil_self (x : Fin 2 ⊕ Fin 2 → K) : Matrix.toBilin' (spJ K) x x = 0 := by
  rw [toBilin'_spJ_apply]
  simp [mul_comm]

theorem bil_comm [CharP K 2] (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) x y = Matrix.toBilin' (spJ K) y x := by
  rw [toBilin'_spJ_apply, toBilin'_spJ_apply]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Fin.sum_univ_two]
  linear_combination (x (.inl 0) * y (.inr 0) - x (.inr 0) * y (.inl 0) +
    x (.inl 1) * y (.inr 1) - x (.inr 1) * y (.inl 1)) * h2

theorem bil_add_left (x x' y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) (x + x') y =
      Matrix.toBilin' (spJ K) x y + Matrix.toBilin' (spJ K) x' y := by
  rw [map_add, LinearMap.add_apply]

theorem bil_smul_left (a : K) (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) (a • x) y = a * Matrix.toBilin' (spJ K) x y := by
  rw [LinearMap.map_smul₂, smul_eq_mul]

theorem bil_add_right (x y y' : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) x (y + y') =
      Matrix.toBilin' (spJ K) x y + Matrix.toBilin' (spJ K) x y' :=
  map_add _ _ _

theorem bil_smul_right (a : K) (x y : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) x (a • y) = a * Matrix.toBilin' (spJ K) x y := by
  rw [map_smul, smul_eq_mul]

theorem sp_ext {γ δ : ↥(StatedSp 2 K)} (h : ∀ x, mat 2 K γ *ᵥ x = mat 2 K δ *ᵥ x) : γ = δ :=
  mat_injective (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h x))

@[expose] noncomputable def trv (y : Fin 2 ⊕ Fin 2 → K) (c : K) : ↥(StatedSp 2 K) :=
  (exists_sp4_transvection y c).choose

theorem trv_mulVec (y : Fin 2 ⊕ Fin 2 → K) (c : K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (trv y c) *ᵥ x = x + (c * Matrix.toBilin' (spJ K) x y) • y := by
  have h := (exists_sp4_transvection y c).choose_spec x
  rw [linModelNat_lin] at h
  exact h

theorem trv_zero (y : Fin 2 ⊕ Fin 2 → K) : trv y 0 = 1 :=
  sp_ext fun x => by rw [trv_mulVec, zero_mul, zero_smul, add_zero, map_one, Matrix.one_mulVec]

theorem trv_mul (y : Fin 2 ⊕ Fin 2 → K) (c d : K) : trv y c * trv y d = trv y (c + d) :=
  sp_ext fun x => by
    rw [map_mul, ← Matrix.mulVec_mulVec, trv_mulVec, trv_mulVec, trv_mulVec, bil_add_left,
      bil_smul_left, bil_self, mul_zero, add_zero, add_assoc, ← add_smul]
    congr 2
    ring

theorem trv_conj (γ : ↥(StatedSp 2 K)) (y : Fin 2 ⊕ Fin 2 → K) (c : K) :
    γ * trv y c * γ⁻¹ = trv (mat 2 K γ *ᵥ y) c :=
  sp_ext fun x => by
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, trv_mulVec,
      Matrix.mulVec_add, Matrix.mulVec_smul, mat_mulVec_inv, trv_mulVec]
    congr 3
    rw [← spB_mat γ, mat_mulVec_inv]

theorem trv_smul (a : K) (y : Fin 2 ⊕ Fin 2 → K) (c : K) :
    trv (a • y) c = trv y (a ^ 2 * c) :=
  sp_ext fun x => by
    rw [trv_mulVec, trv_mulVec, bil_smul_right, smul_smul]
    congr 2
    ring

theorem comm_trv {γ : ↥(StatedSp 2 K)} {y : Fin 2 ⊕ Fin 2 → K} (hγ : mat 2 K γ *ᵥ y = y)
    (c : K) : γ * trv y c = trv y c * γ := by
  have h := trv_conj γ y c
  rw [hγ, mul_inv_eq_iff_eq_mul] at h
  exact h

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem eq_one_of_modZ (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hcomm : commV H = ⊤) {τ : MulAut W}
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) (hτ : ∀ w, f (τ w) = f w) : τ = 1 := by
  have hkh : ∀ h ∈ H, τ * h * τ⁻¹ = h := fun h hh =>
    KA.eq_of_forall_f_eq hf (hτH h hh) hh fun v => by
      simp only [MulAut.mul_apply]
      rw [hτ]
      apply KA.act_congr hf hh
      have h1 := hτ (τ⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      exact h1.symm
  let F : Subgroup W :=
    { carrier := {y | τ y = y}
      mul_mem' := fun {a b} ha hb => by
        show τ (a * b) = a * b
        rw [map_mul, show τ a = a from ha, show τ b = b from hb]
      one_mem' := map_one τ
      inv_mem' := fun {a} ha => by
        show τ a⁻¹ = a⁻¹
        rw [map_inv, show τ a = a from ha] }
  have hle : commV H ≤ F := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, v, rfl⟩
    show τ (h v * v⁻¹) = h v * v⁻¹
    have hz : τ v * v⁻¹ ∈ Z := (hf.eq_iff _ _).mp (hτ v)
    have e1 : τ (h v) = h (τ v) := by
      have := congrArg (fun x : MulAut W => x (τ v)) (hkh h hh)
      simpa [MulAut.mul_apply] using this
    have e2 : τ v = (τ v * v⁻¹) * v := by group
    rw [map_mul, map_inv, e1, e2, map_mul, hZ h hh _ hz]
    generalize τ v * v⁻¹ = a
    rw [_root_.mul_inv_rev, mul_comm v⁻¹ a⁻¹, mul_comm a (h v)]
    group
  ext w
  exact hle (hcomm ▸ Subgroup.mem_top w)

theorem eq_pi_of_modZ (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hcomm : commV H = ⊤) {τ : MulAut W}
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {γ : ↥(StatedSp 2 K)}
    (hτ : ∀ w, f (τ w) = mat 2 K γ *ᵥ f w) : τ = ((π γ : ↥H) : MulAut W) := by
  have h1 : ((π γ : ↥H) : MulAut W)⁻¹ * τ = 1 := by
    refine eq_one_of_modZ hf hZ hcomm (fun h hh => ?_) fun w => ?_
    · have e : ((π γ : ↥H) : MulAut W)⁻¹ * τ * h * (((π γ : ↥H) : MulAut W)⁻¹ * τ)⁻¹ =
          ((π γ : ↥H) : MulAut W)⁻¹ * (τ * h * τ⁻¹) * ((π γ : ↥H) : MulAut W) := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem (π γ).2) (hτH h hh)) (π γ).2
    · apply KA.act_cancel hf (π γ).2
      rw [MulAut.mul_apply, MulAut.apply_inv_self, hτ, hf.act4]
  rw [← mul_inv_cancel_left ((π γ : ↥H) : MulAut W) τ, h1, mul_one]

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB

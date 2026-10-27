module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUActAux

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {k : ℕ}

theorem rckSUc_map_add2 (τ : SUF ≃+* SUF) (M N : Matrix (Fin 2) (Fin 2) SUF) :
    (M + N).map τ = M.map τ + N.map τ := by
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, map_add]

theorem rckSUc_map_smul2 (τ : SUF ≃+* SUF) (c : ZMod 2) (M : Matrix (Fin 2) (Fin 2) SUF) :
    (c • M).map τ = c • M.map τ := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with hc | hc <;> rw [hc] <;> simp

@[expose] noncomputable def rckSUc_conjTrLin :
    Matrix (Fin 2) (Fin 2) SUF →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) SUF where
  toFun M := conjTr SUσ M
  map_add' M N := by
    ext i j
    simp [conjTr_apply, Matrix.add_apply, map_add]
  map_smul' c M := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with hc | hc <;> rw [hc] <;>
      ext i j <;> simp [conjTr_apply]

@[expose] noncomputable def rckSUc_herm : Submodule (ZMod 2) (Matrix (Fin 2) (Fin 2) SUF) :=
  LinearMap.ker (rckSUc_conjTrLin -
    (LinearMap.id : Matrix (Fin 2) (Fin 2) SUF →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) SUF))

theorem rckSUc_mem_herm {M : Matrix (Fin 2) (Fin 2) SUF} :
    M ∈ rckSUc_herm ↔ conjTr SUσ M = M := by
  rw [rckSUc_herm, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  rfl

@[expose] noncomputable def rckSUc_AtoFun (v : Fin 4 → ZMod 2) : rckSUc_herm :=
  ⟨rckSUc_A v, by
    rw [rckSUc_mem_herm]
    ext i j
    fin_cases i <;> fin_cases j
    · change SUσ (rckSUc_alpha (v 0)) = rckSUc_alpha (v 0)
      rw [rckSUc_sigma_alpha]
    · change SUσ (SUσ (rckSUc_beta v)) = rckSUc_beta v
      rw [rckSUc_sigma_involutive]
    · change SUσ (rckSUc_beta v) = SUσ (rckSUc_beta v)
      rfl
    · change SUσ (rckSUc_alpha (v 3)) = rckSUc_alpha (v 3)
      rw [rckSUc_sigma_alpha]⟩

@[expose] noncomputable def rckSUc_Ato : (Fin 4 → ZMod 2) →ₗ[ZMod 2] rckSUc_herm where
  toFun := rckSUc_AtoFun
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rckSUc_AtoFun, rckSUc_A, rckSUc_beta, Pi.add_apply, map_add, add_mul] <;> ring
  map_smul' c v := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with hc | hc <;> rw [hc] <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [rckSUc_AtoFun, rckSUc_A, rckSUc_beta]

theorem rckSUc_Ato_injective : Function.Injective rckSUc_Ato := by
  intro v w h
  have hm : rckSUc_A v = rckSUc_A w := congrArg Subtype.val h
  have h0 : rckSUc_alpha (v 0) = rckSUc_alpha (w 0) := by
    have := congrFun (congrFun hm 0) 0
    simpa [rckSUc_A] using this
  have hb : rckSUc_beta v = rckSUc_beta w := by
    have := congrFun (congrFun hm 0) 1
    simpa [rckSUc_A] using this
  have h3 : rckSUc_alpha (v 3) = rckSUc_alpha (w 3) := by
    have := congrFun (congrFun hm 1) 1
    simpa [rckSUc_A] using this
  have h12 := rckSUc_beta_inj hb
  funext i
  fin_cases i
  · exact rckSUc_alpha_inj h0
  · exact h12.1
  · exact h12.2
  · exact rckSUc_alpha_inj h3

theorem rckSUc_Ato_surjective : Function.Surjective rckSUc_Ato := by
  intro M
  have hM : conjTr SUσ M.1 = M.1 := rckSUc_mem_herm.mp M.2
  have h00 : SUσ (M.1 0 0) = M.1 0 0 := by
    have := congrFun (congrFun hM 0) 0
    simpa [conjTr_apply] using this
  have h11 : SUσ (M.1 1 1) = M.1 1 1 := by
    have := congrFun (congrFun hM 1) 1
    simpa [conjTr_apply] using this
  obtain ⟨z0, hz0⟩ := rckSUc_sigma_fixed (M.1 0 0) h00
  obtain ⟨z3, hz3⟩ := rckSUc_sigma_fixed (M.1 1 1) h11
  obtain ⟨p, hp⟩ := rckSUc_L_surjective (M.1 0 1)
  have h10 : M.1 1 0 = SUσ (M.1 0 1) := by
    have h := congrFun (congrFun hM 1) 0
    have h' : SUσ (M.1 0 1) = M.1 1 0 := by simpa [conjTr_apply] using h
    exact h'.symm
  have hp' : rckSUc_alpha (p 0) + rckSUc_alpha (p 1) * suOmega = M.1 0 1 := by
    rw [← rckSUc_L_apply]; exact hp
  have hp'' : SUσ (rckSUc_alpha (p 0) + rckSUc_alpha (p 1) * suOmega)
      = SUσ (M.1 0 1) := by rw [hp']
  refine ⟨![z0, p 0, p 1, z3], ?_⟩
  apply Subtype.ext
  change rckSUc_A ![z0, p 0, p 1, z3] = M.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rckSUc_A, rckSUc_beta, hz0, hz3, hp', hp'', h10,
      Matrix.cons_val_zero, Matrix.cons_val_succ]

@[expose] noncomputable def rckSUc_A_equiv : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] rckSUc_herm where
  toFun := rckSUc_Ato
  invFun M := Classical.choose (rckSUc_Ato_surjective M)
  left_inv v := rckSUc_Ato_injective
    (Classical.choose_spec (rckSUc_Ato_surjective (rckSUc_Ato v)))
  right_inv M := Classical.choose_spec (rckSUc_Ato_surjective M)
  map_add' := rckSUc_Ato.map_add
  map_smul' := rckSUc_Ato.map_smul

theorem rckSUc_A_equiv_apply (v : Fin 4 → ZMod 2) : rckSUc_A_equiv v = rckSUc_Ato v := rfl

theorem rckSUc_tau_sigma_comm (τ : SUF ≃+* SUF) (x : SUF) :
    τ (SUσ x) = SUσ (τ x) := by
  rw [rckSUc_sigma_apply, rckSUc_sigma_apply, map_pow]

theorem rckSUc_conjTr_map_tau (τ : SUF ≃+* SUF) {M : Matrix (Fin 2) (Fin 2) SUF}
    (hM : conjTr SUσ M = M) : conjTr SUσ (M.map τ) = M.map τ := by
  ext i j
  rw [conjTr_apply, Matrix.map_apply, Matrix.map_apply, ← rckSUc_tau_sigma_comm τ (M j i)]
  have h := congrFun (congrFun hM i) j
  rw [conjTr_apply] at h
  rw [h]

@[expose] noncomputable def rckSUc_phi (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) :
    Matrix (Fin 2) (Fin 2) SUF →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) SUF where
  toFun M := rckSUc_g hk B * (M.map τ * rckSUc_gstar hk B)
  map_add' M N := by
    rw [rckSUc_map_add2, Matrix.add_mul, Matrix.mul_add]
  map_smul' c M := by
    calc rckSUc_g hk B * ((c • M).map τ * rckSUc_gstar hk B)
        = rckSUc_g hk B * ((c • M.map τ) * rckSUc_gstar hk B) := by
          rw [rckSUc_map_smul2]
      _ = rckSUc_g hk B * (c • (M.map τ * rckSUc_gstar hk B)) := by rw [smul_mul]
      _ = c • (rckSUc_g hk B * (M.map τ * rckSUc_gstar hk B)) := by rw [Matrix.mul_smul]

theorem rckSUc_phi_apply (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (M : Matrix (Fin 2) (Fin 2) SUF) :
    rckSUc_phi hk B τ M = rckSUc_g hk B * (M.map τ * rckSUc_gstar hk B) := rfl

theorem rckSUc_phi_herm (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) {M : Matrix (Fin 2) (Fin 2) SUF} (hM : M ∈ rckSUc_herm) :
    rckSUc_phi hk B τ M ∈ rckSUc_herm := by
  rw [rckSUc_mem_herm] at hM ⊢
  rw [rckSUc_phi_apply, conjTr_mul, conjTr_mul, rckSUc_gstar,
    conjTr_conjTr rckSUc_sigma_involutive, rckSUc_conjTr_map_tau τ hM]
  simp only [Matrix.mul_assoc]

@[expose] noncomputable def rckSUc_conjLin (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) : rckSUc_herm →ₗ[ZMod 2] rckSUc_herm where
  toFun M := ⟨rckSUc_phi hk B τ M.1, rckSUc_phi_herm hk B τ M.2⟩
  map_add' M N := by
    apply Subtype.ext
    exact map_add (rckSUc_phi hk B τ) M.1 N.1
  map_smul' c M := by
    apply Subtype.ext
    exact map_smul (rckSUc_phi hk B τ) c M.1

theorem rckSUc_conjLin_apply (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (M : rckSUc_herm) :
    (rckSUc_conjLin hk B τ M).1 = rckSUc_phi hk B τ M.1 := rfl

noncomputable abbrev rckSUc_Pi : Matrix (Fin 2) (Fin 2) SUF := rckSUc_J 2

theorem rckSUc_h_eq (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    rckSUc_h hk B = rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [rckSUc_h, rckSUc_g, rckSUc_Pi, rckSUc_J, Matrix.submatrix_apply,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [antidiag, Fin.rev, rckSUc_B_eq_00 hk B hBN, rckSUc_B_eq_01 hk B hBN,
      rckSUc_B_eq_10 hk B hBN, rckSUc_B_eq_11 hk B hBN]

theorem rckSUc_Pi_mul_Pi : rckSUc_Pi * rckSUc_Pi = (1 : Matrix (Fin 2) (Fin 2) SUF) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rckSUc_Pi, rckSUc_J, antidiag, Matrix.mul_apply, Fin.sum_univ_two, Fin.rev]

theorem rckSUc_gstar_Pi_g (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    rckSUc_gstar hk B * rckSUc_Pi * rckSUc_g hk B = rckSUc_Pi := by
  have h1 : rckSUc_gstar hk B * (rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi) = 1 := by
    rw [← rckSUc_h_eq hk B hBN]
    exact rckSUc_gstar_mul_h hk B hB hBN
  have h2 := congrArg (fun X => X * rckSUc_Pi) h1
  rw [Matrix.one_mul] at h2
  have h3 : (rckSUc_gstar hk B * (rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi)) * rckSUc_Pi
      = rckSUc_gstar hk B * rckSUc_Pi * rckSUc_g hk B := by
    rw [show (rckSUc_gstar hk B * (rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi)) * rckSUc_Pi
        = rckSUc_gstar hk B * rckSUc_Pi * rckSUc_g hk B * (rckSUc_Pi * rckSUc_Pi) by
          noncomm_ring]
    rw [rckSUc_Pi_mul_Pi, Matrix.mul_one]
  rwa [h3] at h2

theorem rckSUc_phi_injective (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (τ : SUF ≃+* SUF) :
    Function.Injective (rckSUc_phi hk B τ) := by
  have hrel := rckSUc_gstar_Pi_g hk B hB hBN
  intro M N h
  have h' : rckSUc_phi hk B τ (M - N) = 0 := by rw [map_sub, h, sub_self]
  rw [rckSUc_phi_apply] at h'
  have key : ∀ X : Matrix (Fin 2) (Fin 2) SUF,
      (rckSUc_Pi * rckSUc_gstar hk B * rckSUc_Pi)
        * (rckSUc_g hk B * (X * rckSUc_gstar hk B))
        * (rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi) = X := by
    intro X
    have hrearr : (rckSUc_Pi * rckSUc_gstar hk B * rckSUc_Pi)
        * (rckSUc_g hk B * (X * rckSUc_gstar hk B))
        * (rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi)
        = rckSUc_Pi * ((rckSUc_gstar hk B * rckSUc_Pi * rckSUc_g hk B)
            * (X * (rckSUc_gstar hk B * rckSUc_Pi * rckSUc_g hk B))) * rckSUc_Pi := by
      noncomm_ring
    rw [hrearr, hrel]
    rw [show rckSUc_Pi * (rckSUc_Pi * (X * rckSUc_Pi)) * rckSUc_Pi = X by
      rw [show rckSUc_Pi * (rckSUc_Pi * (X * rckSUc_Pi)) * rckSUc_Pi
          = (rckSUc_Pi * rckSUc_Pi) * X * (rckSUc_Pi * rckSUc_Pi) by noncomm_ring,
        rckSUc_Pi_mul_Pi, Matrix.one_mul, Matrix.mul_one]]
  have h1 : (rckSUc_Pi * rckSUc_gstar hk B * rckSUc_Pi)
        * (rckSUc_g hk B * ((M - N).map τ * rckSUc_gstar hk B))
        * (rckSUc_Pi * rckSUc_g hk B * rckSUc_Pi) = 0 := by
    rw [h', Matrix.mul_zero, Matrix.zero_mul]
  have hX : (M - N).map τ = 0 := by
    have := h1
    rwa [key ((M - N).map τ)] at this
  have hzero : M - N = 0 := by
    ext i j
    have := congrFun (congrFun hX i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    exact τ.injective (by rw [this]; exact (map_zero τ).symm)
  exact sub_eq_zero.mp hzero

theorem rckSUc_conjLin_injective (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (τ : SUF ≃+* SUF) :
    Function.Injective (rckSUc_conjLin hk B τ) := by
  intro M N h
  have hphi := rckSUc_phi_injective hk B hB hBN τ
  have : M.1 = N.1 := hphi (by
    have := congrArg Subtype.val h
    simpa [rckSUc_conjLin_apply] using this)
  exact Subtype.ext this

@[expose] noncomputable def rckSUc_conjEquiv (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (τ : SUF ≃+* SUF) :
    rckSUc_herm ≃ₗ[ZMod 2] rckSUc_herm where
  toFun := rckSUc_conjLin hk B τ
  invFun M := Classical.choose
    (Finite.injective_iff_surjective.mp (rckSUc_conjLin_injective hk B hB hBN τ) M)
  left_inv M := rckSUc_conjLin_injective hk B hB hBN τ
    (Classical.choose_spec
      (Finite.injective_iff_surjective.mp (rckSUc_conjLin_injective hk B hB hBN τ)
        (rckSUc_conjLin hk B τ M)))
  right_inv M := Classical.choose_spec
    (Finite.injective_iff_surjective.mp (rckSUc_conjLin_injective hk B hB hBN τ) M)
  map_add' := (rckSUc_conjLin hk B τ).map_add
  map_smul' := (rckSUc_conjLin hk B τ).map_smul

theorem rckSUc_conjEquiv_apply (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (τ : SUF ≃+* SUF) (M : rckSUc_herm) :
    rckSUc_conjEquiv hk B hB hBN τ M = rckSUc_conjLin hk B τ M := rfl

@[expose] noncomputable def rckSUc_f (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  rckSUc_A_equiv.trans
    ((rckSUc_conjEquiv hk B hB hBN τ).trans rckSUc_A_equiv.symm)

theorem rckSUc_f_apply (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (v : Fin 4 → ZMod 2) :
    rckSUc_f hk B τ hB hBN v
      = rckSUc_A_equiv.symm (rckSUc_conjEquiv hk B hB hBN τ (rckSUc_A_equiv v)) := by
  rw [rckSUc_f, LinearEquiv.trans_apply, LinearEquiv.trans_apply]

theorem rckSUc_A_f (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (v : Fin 4 → ZMod 2) :
    rckSUc_Ato (rckSUc_f hk B τ hB hBN v)
      = rckSUc_conjEquiv hk B hB hBN τ (rckSUc_Ato v) := by
  rw [rckSUc_f_apply, ← rckSUc_A_equiv_apply, LinearEquiv.apply_symm_apply,
    rckSUc_A_equiv_apply]

theorem rckSUc_Ato_val (v : Fin 4 → ZMod 2) : (rckSUc_Ato v).1 = rckSUc_A v := rfl

theorem rckSUc_A_phi (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (v : Fin 4 → ZMod 2) :
    rckSUc_A (rckSUc_f hk B τ hB hBN v)
      = rckSUc_g hk B * ((rckSUc_A v).map τ * rckSUc_gstar hk B) := by
  have h := congrArg Subtype.val (rckSUc_A_f hk B τ hB hBN v)
  rw [rckSUc_Ato_val, rckSUc_conjEquiv_apply, rckSUc_conjLin_apply, rckSUc_phi_apply,
    rckSUc_Ato_val] at h
  exact h

@[expose] noncomputable def rckSUc_glOf (f : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) :
    GL (Fin 4) (ZMod 2) :=
  (Matrix.GeneralLinearGroup.toLin).symm (LinearMap.GeneralLinearGroup.ofLinearEquiv f)

theorem rckSUc_glOf_mulVec (f : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (v : Fin 4 → ZMod 2) :
    (rckSUc_glOf f : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v = f v := by
  have h := Matrix.GeneralLinearGroup.toLin_apply (rckSUc_glOf f) v
  rw [show Matrix.GeneralLinearGroup.toLin (rckSUc_glOf f)
      = LinearMap.GeneralLinearGroup.ofLinearEquiv f from
        MulEquiv.apply_symm_apply Matrix.GeneralLinearGroup.toLin
          (LinearMap.GeneralLinearGroup.ofLinearEquiv f),
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, Matrix.mulVecLin_apply] at h
  exact h.symm

@[expose] noncomputable def rckSUc_psi (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) : GL (Fin 4) (ZMod 2) :=
  rckSUc_glOf (rckSUc_f hk (B : Matrix (Fin k) (Fin k) SUF) τ hB hBN)

theorem rckSUc_psi_mulVec (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    (rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v
      = rckSUc_f hk (B : Matrix (Fin k) (Fin k) SUF) τ hB hBN v :=
  rckSUc_glOf_mulVec _ v

theorem rckSUc_A_psi (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    rckSUc_A ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
      = rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)
          * ((rckSUc_A v).map τ * rckSUc_gstar hk (B : Matrix (Fin k) (Fin k) SUF)) := by
  rw [rckSUc_psi_mulVec]
  exact rckSUc_A_phi hk (B : Matrix (Fin k) (Fin k) SUF) τ hB hBN v

end CFSG.StandardType.RCKK1IIISU

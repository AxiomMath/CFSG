module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private theorem caPair_jGL_eq_single (m : ℕ) :
    (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + Matrix.single (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 1))) 1 := by
  ext i j
  rcases i with iA | iB | iC <;> rcases j with jA | jB | jC <;>
    simp [jGL, uGL, uMat, blk, Matrix.one_apply, Matrix.single, Fin.ext_iff]

private theorem caPair_jGL_mulVec (m : ℕ) (x : BlkIdx 1 m → ZMod 2) :
    (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x =
      x + x (Sum.inr (Sum.inr (0 : Fin 1))) • Pi.single (Sum.inl (0 : Fin 1)) 1 := by
  rw [caPair_jGL_eq_single, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  ext i
  simp

private theorem caPair_jGL_inv (m : ℕ) : (jGL 1 m)⁻¹ = jGL 1 m :=
  inv_eq_of_mul_eq_one_right (jGL_mul_self (r := 1) (m := m))

private theorem caPair_betaStd_eq_single (m : ℕ) :
    (betaStd m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + Matrix.single (Sum.inl (0 : Fin 1)) (Sum.inr (Sum.inr (0 : Fin 1))) 1
        + Matrix.single (Sum.inr (Sum.inr (0 : Fin 1))) (Sum.inl (0 : Fin 1)) 1
        + Matrix.single (Sum.inr (Sum.inr (0 : Fin 1))) (Sum.inr (Sum.inr (0 : Fin 1))) 1 := by
  ext i j
  rcases i with iA | iB | iC <;> rcases j with jA | jB | jC <;>
    simp [betaStd, coe_pairGL, CFSG.LieType.Steinberg.Sp.blockMat, betaTwo,
      Matrix.one_apply, Matrix.single, Fin.ext_iff] <;> decide

private theorem caPair_betaStd_mulVec (m : ℕ) (x : BlkIdx 1 m → ZMod 2) :
    (betaStd m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x =
      x + x (Sum.inr (Sum.inr (0 : Fin 1))) • Pi.single (Sum.inl (0 : Fin 1)) 1
        + x (Sum.inl (0 : Fin 1)) • Pi.single (Sum.inr (Sum.inr (0 : Fin 1))) 1
        + x (Sum.inr (Sum.inr (0 : Fin 1))) • Pi.single (Sum.inr (Sum.inr (0 : Fin 1))) 1 := by
  rw [caPair_betaStd_eq_single]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  ext i
  rcases i with iA | iB | iC <;> simp [Pi.add_apply, Pi.smul_apply, Fin.ext_iff]

private theorem caPair_hcoord {m : ℕ} (h : (BlkIdx 1 m → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : BlkIdx 1 m → ZMod 2) :
    h x = x (Sum.inl (0 : Fin 1)) * h (Pi.single (Sum.inl (0 : Fin 1)) 1)
      + ∑ j : Fin m, x (Sum.inr (Sum.inl j)) * h (Pi.single (Sum.inr (Sum.inl j)) 1)
      + x (Sum.inr (Sum.inr (0 : Fin 1))) * h (Pi.single (Sum.inr (Sum.inr (0 : Fin 1))) 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp only [Fin.sum_univ_one]
  have hsingle : ∀ (i : BlkIdx 1 m),
      Pi.single i (x i) = x i • (Pi.single i (1 : ZMod 2) : BlkIdx 1 m → ZMod 2) := by
    intro i
    rw [← Pi.single_smul]
    simp
  simp only [hsingle, map_smul, smul_eq_mul, Fin.val_zero]
  ring

private theorem caPair_uGL_mulVec {m : ℕ} (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (x : BlkIdx 1 m → ZMod 2) :
    (uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x =
      (fun i => match i with
        | Sum.inl _ => x (Sum.inl (0 : Fin 1))
            + ∑ j : Fin m, a 0 j * x (Sum.inr (Sum.inl j))
            + c 0 0 * x (Sum.inr (Sum.inr (0 : Fin 1)))
        | Sum.inr (Sum.inl j) => x (Sum.inr (Sum.inl j))
            + b j 0 * x (Sum.inr (Sum.inr (0 : Fin 1)))
        | Sum.inr (Sum.inr _) => x (Sum.inr (Sum.inr (0 : Fin 1)))) := by
  ext i
  rcases i with iA | iB | iC
  · fin_cases iA
    simp [uGL, uMat, blk, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
      dotProduct, mul_comm, mul_left_comm, mul_assoc, Matrix.one_apply]
    ring_nf
  · simp [uGL, uMat, blk, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
      dotProduct, mul_comm, mul_left_comm, mul_assoc, Matrix.one_apply]
  · fin_cases iC
    simp [uGL, uMat, blk, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_one,
      dotProduct, mul_comm, mul_left_comm, mul_assoc, Matrix.one_apply]

private theorem caPair_uGL_mulVec_inl {m : ℕ} (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (x : BlkIdx 1 m → ZMod 2) :
    ((uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x)
        (Sum.inl (0 : Fin 1)) =
      x (Sum.inl (0 : Fin 1))
        + ∑ j : Fin m, a (0 : Fin 1) j * x (Sum.inr (Sum.inl j))
        + c (0 : Fin 1) (0 : Fin 1) * x (Sum.inr (Sum.inr (0 : Fin 1))) := by
  rw [caPair_uGL_mulVec]

private theorem caPair_uGL_mulVec_inr_inl {m : ℕ} (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (x : BlkIdx 1 m → ZMod 2) (j : Fin m) :
    ((uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x)
        (Sum.inr (Sum.inl j)) =
      x (Sum.inr (Sum.inl j)) + b j (0 : Fin 1) * x (Sum.inr (Sum.inr (0 : Fin 1))) := by
  rw [caPair_uGL_mulVec]

private theorem caPair_uGL_mulVec_inr_inr {m : ℕ} (a : Matrix (Fin 1) (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin 1) (ZMod 2)) (c : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (x : BlkIdx 1 m → ZMod 2) :
    ((uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x)
        (Sum.inr (Sum.inr (0 : Fin 1))) = x (Sum.inr (Sum.inr (0 : Fin 1))) := by
  rw [caPair_uGL_mulVec]

private theorem caPair_toLinearEquiv_apply {m : ℕ} (M : GL (BlkIdx 1 m) (ZMod 2))
    (x : BlkIdx 1 m → ZMod 2) :
    ((Matrix.GeneralLinearGroup.toLin M).toLinearEquiv :
      (BlkIdx 1 m → ZMod 2) ≃ₗ[ZMod 2] (BlkIdx 1 m → ZMod 2)) x =
      (M : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv]
  rw [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]


private theorem caPair_toLinearEquiv_pow_three {m : ℕ} (γ : GL (BlkIdx 1 m) (ZMod 2))
    (hγ3 : γ ^ 3 = 1) :
    ((Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv :
      (BlkIdx 1 m → ZMod 2) ≃ₗ[ZMod 2] (BlkIdx 1 m → ZMod 2)) ^ 3 = 1 := by
  let Φ : GL (BlkIdx 1 m) (ZMod 2) →*
      ((BlkIdx 1 m → ZMod 2) ≃ₗ[ZMod 2] (BlkIdx 1 m → ZMod 2)) :=
    { toFun := fun g => (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
      map_one' := by
        ext x
        simp [LinearMap.GeneralLinearGroup.coe_toLinearEquiv]
      map_mul' := by
        intro a b
        rw [MulEquiv.map_mul, LinearMap.GeneralLinearGroup.toLinearEquiv_mul] }
  change Φ γ ^ 3 = 1
  rw [← MonoidHom.map_pow Φ γ 3, hγ3, MonoidHom.map_one]

private theorem caPair_f_mulVec_ne_zero {m : ℕ} (γ : GL (BlkIdx 1 m) (ZMod 2))
    (hγ : orderOf γ = 3) (hJγ : jGL 1 m * γ * (jGL 1 m)⁻¹ = γ⁻¹) :
    (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1))) :
        (BlkIdx 1 m → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      ((γ : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ
        Pi.single (Sum.inl (0 : Fin 1)) 1) ≠ 0 := by
  let V := BlkIdx 1 m → ZMod 2
  let eA : V := Pi.single (Sum.inl (0 : Fin 1)) 1
  let eC : V := Pi.single (Sum.inr (Sum.inr (0 : Fin 1))) 1
  let f : V →ₗ[ZMod 2] ZMod 2 := LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))
  let Ψ : GL (BlkIdx 1 m) (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin (n := BlkIdx 1 m) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  let B : V ≃ₗ[ZMod 2] V := Ψ γ
  let J : V ≃ₗ[ZMod 2] V := Ψ (jGL 1 m)
  let h : V →ₗ[ZMod 2] ZMod 2 := f.comp (B : V →ₗ[ZMod 2] V)
  let v : V := B⁻¹ eA
  let t : ZMod 2 := h eA
  have hγ3 : γ ^ 3 = 1 := by rw [← hγ]; exact pow_orderOf_eq_one γ
  have hB3 : B ^ 3 = 1 := by
    change ((Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv :
      V ≃ₗ[ZMod 2] V) ^ 3 = 1
    exact caPair_toLinearEquiv_pow_three γ hγ3
  have hB_apply : ∀ x : V, B x = (γ : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
    intro x
    change ((Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv : V ≃ₗ[ZMod 2] V) x = _
    exact caPair_toLinearEquiv_apply γ x
  have hJ_apply : ∀ x : V, J x =
      (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
    intro x
    change ((Matrix.GeneralLinearGroup.toLin (jGL 1 m)).toLinearEquiv : V ≃ₗ[ZMod 2] V) x = _
    exact caPair_toLinearEquiv_apply (jGL 1 m) x
  have hJ_action : ∀ x : V, J x = x + f x • eA := by
    intro x
    rw [hJ_apply, caPair_jGL_mulVec]
    have hfx : f x = x (Sum.inr (Sum.inr (0 : Fin 1))) := by
      change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))) x = _
      rw [LinearMap.proj_apply]
    rw [hfx]
  have hJeq : J * B * J = B⁻¹ := by
    have hJeqG : jGL 1 m * γ * jGL 1 m = γ⁻¹ := by
      simpa [caPair_jGL_inv] using hJγ
    calc J * B * J = Ψ (jGL 1 m * γ * jGL 1 m) := by rw [map_mul, map_mul]
      _ = Ψ (γ⁻¹) := by rw [hJeqG]
      _ = B⁻¹ := by rw [MulEquiv.map_inv]
  have hmul : B * (B * B) = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hB3
  have hBinv : B⁻¹ = B * B := inv_eq_of_mul_eq_one_right hmul
  have hBinv2 : B⁻¹ * B⁻¹ = B := by
    rw [hBinv]
    calc (B * B) * (B * B) = B * (B * (B * B)) := by group
      _ = B * 1 := by rw [hmul]
      _ = B := by group
  have hSJ : (B⁻¹ * J * B) * J = B := by
    calc (B⁻¹ * J * B) * J = B⁻¹ * (J * B * J) := by group
      _ = B⁻¹ * B⁻¹ := by rw [hJeq]
      _ = B := hBinv2
  have hS : ∀ x : V, (B⁻¹ * J * B) x = x + h x • v := by
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hJ_action]
    change B.symm (B x + f (B x) • eA) = x + f (B x) • v
    rw [map_add, map_smul, B.symm_apply_apply]
    rfl
  have hformula : ∀ x : V, B x = x + f x • eA + (h x + f x * t) • v := by
    intro x
    have hhJ : h (J x) = h x + f x * t := by
      rw [hJ_action, map_add, map_smul]
      simp [t, smul_eq_mul, mul_comm]
    calc B x = ((B⁻¹ * J * B) * J) x := by rw [hSJ]
      _ = (B⁻¹ * J * B) (J x) := by rw [LinearEquiv.mul_apply]
      _ = J x + h (J x) • v := hS (J x)
      _ = x + f x • eA + (h x + f x * t) • v := by rw [hhJ, hJ_action]
  have ht_ne : t ≠ 0 := by
    intro ht0
    have hBeA : B eA = eA := by
      have hfA : f eA = 0 := by
        change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1))))
          (Pi.single (Sum.inl (0 : Fin 1)) 1) = 0
        rw [LinearMap.proj_apply, Pi.single_eq_of_ne]
        exact Sum.inr_ne_inl
      have h := hformula eA
      simpa [f, eA, t, ht0, hfA] using h
    have hv : v = eA := by
      have h := congrArg (fun y => B.symm y) hBeA
      rw [B.symm_apply_apply] at h
      simpa [v, LinearEquiv.coe_inv] using h.symm
    have hhBx : ∀ x : V, h (B x) = h x := by
      intro x
      rw [hformula x]
      simp [map_add, map_smul, hv, ht0, t]
    have hBB : ∀ x : V, B (B x) = B x := by
      intro x
      rw [hformula (B x), hhBx, ht0, hv]
      simp only [mul_zero, add_zero]
      have hss : h x • eA + h x • eA = 0 := by
        rw [← two_smul (ZMod 2) (h x • eA), show (2 : ZMod 2) = 0 by decide, zero_smul]
      rw [show f (B x) = h x from rfl, add_assoc, hss, add_zero]
    have hB2 : B * B = B := by
      apply LinearEquiv.ext
      intro x
      rw [LinearEquiv.mul_apply, hBB x]
    have hB1 : B = 1 := by
      calc B = B⁻¹ * (B * B) := by group
        _ = B⁻¹ * B := by rw [hB2]
        _ = 1 := by group
    have hγ1 : γ = 1 := by
      apply Ψ.injective
      change B = Ψ 1
      rw [hB1, map_one]
    have hord : orderOf (1 : GL (BlkIdx 1 m) (ZMod 2)) = 3 := by
      rw [← hγ1]; exact hγ
    rw [orderOf_one] at hord
    omega
  have ht : t = f ((γ : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA) := by
    change f (B eA) = f ((γ : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA)
    rw [hB_apply]
  have hf_eq : f ((γ : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA) =
      (γ : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
        (Sum.inr (Sum.inr (0 : Fin 1))) (Sum.inl (0 : Fin 1)) := by
    rw [show eA = Pi.single (Sum.inl (0 : Fin 1)) 1 from rfl, Matrix.mulVec_single_one]
    rfl
  simpa [ht, hf_eq] using ht_ne

theorem exists_cent_conj_betaStd {m : ℕ} (β : GL (BlkIdx 1 m) (ZMod 2)) (hβ : orderOf β = 3)
    (hJ : jGL 1 m * β * (jGL 1 m)⁻¹ = β⁻¹) : ∃ g ∈ Cent 1 m, g * β * g⁻¹ = betaStd m := by
  let V := BlkIdx 1 m → ZMod 2
  let eA : V := Pi.single (Sum.inl (0 : Fin 1)) 1
  let eC : V := Pi.single (Sum.inr (Sum.inr (0 : Fin 1))) 1
  let f : V →ₗ[ZMod 2] ZMod 2 := LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))
  let Ψ : GL (BlkIdx 1 m) (ZMod 2) ≃* (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin (n := BlkIdx 1 m) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  let B : V ≃ₗ[ZMod 2] V := Ψ β
  let J : V ≃ₗ[ZMod 2] V := Ψ (jGL 1 m)
  let h : V →ₗ[ZMod 2] ZMod 2 := f.comp (B : V →ₗ[ZMod 2] V)
  let v : V := B⁻¹ eA
  let t : ZMod 2 := h eA
  have hβ3 : β ^ 3 = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  have hB3 : B ^ 3 = 1 := by
    change ((Matrix.GeneralLinearGroup.toLin β).toLinearEquiv :
      V ≃ₗ[ZMod 2] V) ^ 3 = 1
    exact caPair_toLinearEquiv_pow_three β hβ3
  have hB_apply : ∀ x : V, B x = (β : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
    intro x
    change ((Matrix.GeneralLinearGroup.toLin β).toLinearEquiv : V ≃ₗ[ZMod 2] V) x = _
    exact caPair_toLinearEquiv_apply β x
  have hJ_apply : ∀ x : V, J x =
      (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
    intro x
    change ((Matrix.GeneralLinearGroup.toLin (jGL 1 m)).toLinearEquiv : V ≃ₗ[ZMod 2] V) x = _
    exact caPair_toLinearEquiv_apply (jGL 1 m) x
  have hJ_action : ∀ x : V, J x = x + f x • eA := by
    intro x
    rw [hJ_apply, caPair_jGL_mulVec]
    have hfx : f x = x (Sum.inr (Sum.inr (0 : Fin 1))) := by
      change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))) x = _
      rw [LinearMap.proj_apply]
    rw [hfx]
  have hJeq : J * B * J = B⁻¹ := by
    have hJeqG : jGL 1 m * β * jGL 1 m = β⁻¹ := by
      simpa [caPair_jGL_inv] using hJ
    calc J * B * J = Ψ (jGL 1 m * β * jGL 1 m) := by rw [map_mul, map_mul]
      _ = Ψ (β⁻¹) := by rw [hJeqG]
      _ = B⁻¹ := by rw [MulEquiv.map_inv]
  have hmul : B * (B * B) = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hB3
  have hBinv : B⁻¹ = B * B := inv_eq_of_mul_eq_one_right hmul
  have hBinv2 : B⁻¹ * B⁻¹ = B := by
    rw [hBinv]
    calc (B * B) * (B * B) = B * (B * (B * B)) := by group
      _ = B * 1 := by rw [hmul]
      _ = B := by group
  have hSJ : (B⁻¹ * J * B) * J = B := by
    calc (B⁻¹ * J * B) * J = B⁻¹ * (J * B * J) := by group
      _ = B⁻¹ * B⁻¹ := by rw [hJeq]
      _ = B := hBinv2
  have hS : ∀ x : V, (B⁻¹ * J * B) x = x + h x • v := by
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hJ_action]
    change B.symm (B x + f (B x) • eA) = x + f (B x) • v
    rw [map_add, map_smul, B.symm_apply_apply]
    rfl
  have ht_ne : t ≠ 0 := by
    have h := caPair_f_mulVec_ne_zero β hβ hJ
    have ht : t = f ((β : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA) := by
      change f (B eA) = f ((β : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA)
      rw [hB_apply]
    rw [← ht] at h
    exact h
  have ht1 : t = 1 := by
    have h2 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    exact (h2 t).resolve_left ht_ne
  have hfA : f eA = 0 := by
    change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1))))
      (Pi.single (Sum.inl (0 : Fin 1)) 1) = 0
    rw [LinearMap.proj_apply, Pi.single_eq_of_ne]
    exact Sum.inr_ne_inl
  have hvB : B v = eA := by
    change B (B.symm eA) = eA
    rw [B.apply_symm_apply]
  have hhv : h v = 0 := by
    change f (B v) = 0
    rw [hvB, hfA]
  have hfv_ne : f v ≠ 0 := by
    have hγ : orderOf β⁻¹ = 3 := by rw [orderOf_inv, hβ]
    have hJγ : jGL 1 m * β⁻¹ * (jGL 1 m)⁻¹ = (β⁻¹)⁻¹ := by
      have hinv := congrArg Inv.inv hJ
      rw [inv_inv] at hinv
      rw [show (jGL 1 m * β * (jGL 1 m)⁻¹)⁻¹ =
          jGL 1 m * β⁻¹ * (jGL 1 m)⁻¹ from by group] at hinv
      exact hinv
    have h := caPair_f_mulVec_ne_zero β⁻¹ hγ hJγ
    have hv : v = ((β⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA := by
      change (Ψ β)⁻¹ eA = ((β⁻¹ : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ eA
      rw [← MulEquiv.map_inv]
      change ((Matrix.GeneralLinearGroup.toLin (β⁻¹)).toLinearEquiv :
        V ≃ₗ[ZMod 2] V) eA = _
      exact caPair_toLinearEquiv_apply (β⁻¹) eA
    rw [show Pi.single (Sum.inl (0 : Fin 1)) 1 = eA from rfl] at h
    rw [← hv] at h
    change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))) v ≠ 0
    exact h
  have hfv1 : f v = 1 := by
    have h2 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    exact (h2 (f v)).resolve_left hfv_ne
  let eB : Fin m → V := fun j => Pi.single (Sum.inr (Sum.inl j)) 1
  let a : Matrix (Fin 1) (Fin m) (ZMod 2) := fun _ j => h (eB j)
  let b : Matrix (Fin m) (Fin 1) (ZMod 2) := fun j _ => v (Sum.inr (Sum.inl j))
  let c : Matrix (Fin 1) (Fin 1) (ZMod 2) := fun _ _ => h eC
  let g : GL (BlkIdx 1 m) (ZMod 2) := uGL a b c
  have hg_mem : g ∈ Cent 1 m := uSub_le_cent 1 m ⟨a, b, c, rfl⟩
  let gL : V ≃ₗ[ZMod 2] V := Ψ g
  have hgL_apply : ∀ x : V, gL x = (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
    intro x
    change ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv : V ≃ₗ[ZMod 2] V) x = _
    exact caPair_toLinearEquiv_apply g x
  have hgC : ∀ x : V, (gL x) (Sum.inr (Sum.inr (0 : Fin 1))) = f x := by
    intro x
    rw [hgL_apply, caPair_uGL_mulVec_inr_inr]
    change x (Sum.inr (Sum.inr (0 : Fin 1))) =
      (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))) x
    rw [LinearMap.proj_apply]
  have heA1 : h (Pi.single (Sum.inl (0 : Fin 1)) 1) = 1 := by
    change h eA = 1
    change t = 1
    exact ht1
  have hgA : ∀ x : V, (gL x) (Sum.inl (0 : Fin 1)) = h x := by
    intro x
    rw [hgL_apply, caPair_uGL_mulVec_inl, caPair_hcoord h x, heA1]
    simp only [a, c, one_mul]
    rw [Finset.sum_congr rfl (fun j _ => by rw [mul_comm])]
    ring
  have hg_eA : gL eA = eA := by
    funext i
    rcases i with iA | iB | iC
    · have hi : iA = 0 := Subsingleton.elim iA 0
      subst hi
      rw [hgA]
      rw [show h eA = t from rfl, ht1]
      simp [eA]
    · rw [hgL_apply, caPair_uGL_mulVec_inr_inl]
      simp [eA]
    · have hi : iC = 0 := Subsingleton.elim iC 0
      subst hi
      rw [hgL_apply, caPair_uGL_mulVec_inr_inr]
  have hvC : v (Sum.inr (Sum.inr (0 : Fin 1))) = 1 := by
    change f v = 1
    exact hfv1
  have hg_v : gL v = eC := by
    funext i
    rcases i with iA | iB | iC
    · have hi : iA = 0 := Subsingleton.elim iA 0
      subst hi
      rw [hgA, show h v = 0 from hhv]
      simp [eC]
    · rw [hgL_apply, caPair_uGL_mulVec_inr_inl]
      rw [hvC, show b iB (0 : Fin 1) = v (Sum.inr (Sum.inl iB)) from rfl, mul_one]
      rw [show v (Sum.inr (Sum.inl iB)) + v (Sum.inr (Sum.inl iB)) = 0 from by
        rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]]
      simp [eC]
    · have hi : iC = 0 := Subsingleton.elim iC 0
      subst hi
      rw [hgC, hfv1]
      simp [eC]
  have hgAinv : ∀ x : V, h (gL.symm x) = x (Sum.inl (0 : Fin 1)) := by
    intro x
    have h := hgA (gL.symm x)
    rw [gL.apply_symm_apply] at h
    exact h.symm
  have hgCinv : ∀ x : V, f (gL.symm x) = f x := by
    intro x
    have h := hgC (gL.symm x)
    rw [gL.apply_symm_apply] at h
    have hfx : f x = x (Sum.inr (Sum.inr (0 : Fin 1))) := by
      change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))) x = _
      rw [LinearMap.proj_apply]
    rw [hfx]
    exact h.symm
  have hgJ : gL * J * gL⁻¹ = J := by
    have hcomm : g * jGL 1 m = jGL 1 m * g :=
      (Subgroup.mem_centralizer_singleton_iff.mp hg_mem)
    calc gL * J * gL⁻¹ = Ψ (g * jGL 1 m * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = Ψ (jGL 1 m) := by rw [hcomm]; group
      _ = J := rfl
  have hgS : ∀ x : V, (gL * (B⁻¹ * J * B) * gL⁻¹) x =
      x + x (Sum.inl (0 : Fin 1)) • eC := by
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hS (gL⁻¹ x), map_add, map_smul,
      LinearEquiv.coe_inv, gL.apply_symm_apply, hgAinv, hg_v]
  have hconj : gL * B * gL⁻¹ = Ψ (betaStd m) := by
    apply LinearEquiv.ext
    intro x
    have hJxA : (J x) (Sum.inl (0 : Fin 1)) = x (Sum.inl (0 : Fin 1)) + f x := by
      rw [hJ_action]
      rw [Pi.add_apply, Pi.smul_apply, show eA (Sum.inl (0 : Fin 1)) = 1 from rfl]
      simp [smul_eq_mul]
    calc (gL * B * gL⁻¹) x = (gL * ((B⁻¹ * J * B) * J) * gL⁻¹) x := by rw [hSJ]
      _ = ((gL * (B⁻¹ * J * B) * gL⁻¹) * (gL * J * gL⁻¹)) x := by group
      _ = ((gL * (B⁻¹ * J * B) * gL⁻¹) * J) x := by rw [hgJ]
      _ = (gL * (B⁻¹ * J * B) * gL⁻¹) (J x) := by rw [LinearEquiv.mul_apply]
      _ = J x + (J x) (Sum.inl (0 : Fin 1)) • eC := hgS (J x)
      _ = x + f x • eA + (x (Sum.inl (0 : Fin 1)) + f x) • eC := by
        rw [hJxA, hJ_action]
      _ = x + f x • eA + x (Sum.inl (0 : Fin 1)) • eC + f x • eC := by
        rw [add_smul]; abel
      _ = (betaStd m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *ᵥ x := by
        rw [caPair_betaStd_mulVec]
        have hfx : f x = x (Sum.inr (Sum.inr (0 : Fin 1))) := by
          change (LinearMap.proj (Sum.inr (Sum.inr (0 : Fin 1)))) x = _
          rw [LinearMap.proj_apply]
        rw [hfx]
      _ = Ψ (betaStd m) x := by
        rw [show Ψ (betaStd m) = (Matrix.GeneralLinearGroup.toLin (betaStd m)).toLinearEquiv
          from rfl]
        exact (caPair_toLinearEquiv_apply (betaStd m) x).symm
  have hGL : g * β * g⁻¹ = betaStd m := by
    apply Ψ.injective
    rw [map_mul, map_mul, map_inv]
    exact hconj
  exact ⟨g, hg_mem, hGL⟩

end CFSG.StandardType.FF81.CentA

end

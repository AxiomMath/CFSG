module

public import CFSG.Quasithin.Vol2.Asc94.TSModel1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def sgM (A : Mt) : Mt := Matrix.of fun i j => A j.rev i.rev

theorem sgM_apply (A : Mt) (i j : Fin 5) : sgM A i j = A j.rev i.rev := rfl

theorem sgM_one : sgM (1 : Mt) = 1 := by
  ext i j
  simp only [sgM_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have : j.rev ≠ i.rev := fun h' => h (Fin.rev_injective h').symm
    simp [h, this]

theorem sgM_mul (A B : Mt) : sgM (A * B) = sgM B * sgM A := by
  ext i j
  simp only [sgM_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun k => by simp [mul_comm]).symm

theorem sgM_sgM (A : Mt) : sgM (sgM A) = A := by
  ext i j
  simp [sgM_apply]

theorem sgM_sub (A B : Mt) : sgM (A - B) = sgM A - sgM B := by
  ext i j
  simp [sgM_apply]

theorem det_sgM (A : Mt) : (sgM A).det = A.det := by
  have : sgM A = Matrix.reindex Fin.revPerm Fin.revPerm Aᵀ := by
    ext i j
    simp [sgM_apply]
  rw [this, Matrix.det_reindex_self, Matrix.det_transpose]

theorem Hc_ext {x y : Hc} (h : cm x = cm y) : x = y := Subtype.ext (Subtype.ext h)

theorem rev_aux1 : ∀ i : Fin 5, ((1 : Mt) 4 i.rev) = (1 : Mt) i 0 := by decide

theorem rev_aux2 : ∀ j : Fin 5, ((1 : Mt) j.rev 0) = (1 : Mt) 4 j := by decide

theorem det_cm (x : Hc) : (cm x).det = 1 := x.1.2

@[expose] def sigmaFun (x : Hc) : Hc :=
  mkH (sgM (cm x⁻¹)) (by rw [det_sgM, det_cm])
    (fun i => by
      rw [sgM_apply]
      show cm x⁻¹ 4 i.rev = _
      rw [cm_row4, rev_aux1])
    (fun j => by
      rw [sgM_apply]
      show cm x⁻¹ j.rev 0 = _
      rw [cm_col0, rev_aux2])

theorem cm_sigmaFun (x : Hc) : cm (sigmaFun x) = sgM (cm x⁻¹) := rfl

@[expose] def sigmaHom : Hc →* Hc where
  toFun := sigmaFun
  map_one' := by
    apply Hc_ext
    show sgM (cm (1 : Hc)⁻¹) = cm 1
    rw [inv_one, cm_one, sgM_one]
  map_mul' := fun x y => by
    apply Hc_ext
    show sgM (cm (x * y)⁻¹) = cm (sigmaFun x) * cm (sigmaFun y)
    rw [cm_sigmaFun, cm_sigmaFun, _root_.mul_inv_rev, cm_mul, sgM_mul]

theorem cm_sigmaHom (x : Hc) : cm (sigmaHom x) = sgM (cm x⁻¹) := rfl

theorem sigmaHom_sigmaHom (x : Hc) : sigmaHom (sigmaHom x) = x := by
  apply Hc_ext
  rw [cm_sigmaHom, ← map_inv, cm_sigmaHom, inv_inv, sgM_sgM]

@[expose] def sigma : Hc ≃* Hc :=
  MonoidHom.toMulEquiv sigmaHom sigmaHom (MonoidHom.ext sigmaHom_sigmaHom)
    (MonoidHom.ext sigmaHom_sigmaHom)

theorem sigma_apply (x : Hc) : sigma x = sigmaHom x := rfl

theorem sigma_sigma (x : Hc) : sigma (sigma x) = x := sigmaHom_sigmaHom x

theorem sigma_symm : sigma.symm = sigma :=
  MulEquiv.ext fun x => by
    rw [MulEquiv.symm_apply_eq]
    exact (sigma_sigma x).symm

theorem refl_S1 : ∀ i j : Fin 5, S1 j.rev i.rev ↔ S2 i j := by decide
theorem refl_S2 : ∀ i j : Fin 5, S2 j.rev i.rev ↔ S1 i j := by decide
theorem refl_SA : ∀ i j : Fin 5, SA j.rev i.rev ↔ SA2 i j := by decide
theorem refl_SA2 : ∀ i j : Fin 5, SA2 j.rev i.rev ↔ SA i j := by decide

theorem sigma_mem_patSub {S S' : Fin 5 → Fin 5 → Prop} (hS : ∀ i k j, S i k → S k j → False)
    (hS' : ∀ i k j, S' i k → S' k j → False) (hrefl : ∀ i j, S j.rev i.rev ↔ S' i j) {x : Hc}
    (hx : x ∈ patSub S hS) : sigma x ∈ patSub S' hS' := by
  have hxx : cm x * cm x = 1 := sq_one_of_supp hS ((mem_patSub hS).1 hx)
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (Hc_ext hxx)
  rw [mem_patSub] at hx ⊢
  intro i j hij
  have e : cm (sigma x) - 1 = sgM (cm x - 1) := by
    rw [sigma_apply, cm_sigmaHom, hinv, sgM_sub, sgM_one]
  rw [e, sgM_apply]
  exact hx _ _ (fun h => hij ((hrefl i j).1 h))

theorem sigma_U1 {x : Hc} (hx : x ∈ U1) : sigma x ∈ U2 := sigma_mem_patSub hS1 hS2 refl_S1 hx
theorem sigma_U2 {x : Hc} (hx : x ∈ U2) : sigma x ∈ U1 := sigma_mem_patSub hS2 hS1 refl_S2 hx
theorem sigma_A1 {x : Hc} (hx : x ∈ A1) : sigma x ∈ A2 := sigma_mem_patSub hSA hSA2 refl_SA hx
theorem sigma_A2 {x : Hc} (hx : x ∈ A2) : sigma x ∈ A1 := sigma_mem_patSub hSA2 hSA refl_SA2 hx

theorem sigma_zt : sigma zt = zt := by
  have hzz : zt⁻¹ = zt := inv_eq_of_mul_eq_one_right (by
    have := zt_sq
    rw [sq] at this
    exact this)
  apply Hc_ext
  rw [sigma_apply, cm_sigmaHom, hzz, cm_zt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sgM_apply, tt, Matrix.one_apply, Matrix.single_apply]

theorem map_sigma_U1 : U1.map sigmaHom = U2 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact sigma_U1 hx
  · intro y hy
    exact ⟨sigma y, sigma_U2 hy, sigmaHom_sigmaHom y⟩

theorem map_sigma_U2 : U2.map sigmaHom = U1 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact sigma_U2 hx
  · intro y hy
    exact ⟨sigma y, sigma_U1 hy, sigmaHom_sigmaHom y⟩

theorem map_sigma_A1 : A1.map sigmaHom = A2 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact sigma_A1 hx
  · intro y hy
    exact ⟨sigma y, sigma_A2 hy, sigmaHom_sigmaHom y⟩

theorem map_sigma_A2 : A2.map sigmaHom = A1 := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact sigma_A2 hx
  · intro y hy
    exact ⟨sigma y, sigma_A1 hy, sigmaHom_sigmaHom y⟩

end CFSG.Quasithin.A94.L52

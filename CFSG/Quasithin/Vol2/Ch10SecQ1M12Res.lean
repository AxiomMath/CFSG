module

public import CFSG.Quasithin.Vol2.Ch10SecQ1M12Data

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

open CFSG.Monster.Code CFSG.Quasithin

theorem perm_apply_inv (σ : Equiv.Perm (Fin 24)) (y : Fin 24) : σ (σ⁻¹ y) = y := by simp

theorem perm_inv_apply (σ : Equiv.Perm (Fin 24)) (y : Fin 24) : σ⁻¹ (σ y) = y := by simp

@[expose] def dodecadE : G6.PermMod 24 := Multiplicative.ofAdd dodecadW

theorem dodecadE_mem_golayC : dodecadE ∈ golayC := dodecadW_mem_C

theorem hammingNorm_dodecadE : hammingNorm (Multiplicative.toAdd dodecadE) = 12 :=
  hammingNorm_dodecadW

theorem permAct_dodecadE_eq_iff (σ : Equiv.Perm (Fin 24)) :
    G6.permAct 24 σ dodecadE = dodecadE ↔ ∀ y, dodecadW (σ⁻¹ y) = dodecadW y := by
  constructor
  · intro h y
    have := congrArg (fun x : G6.PermMod 24 => Multiplicative.toAdd x y) h
    simpa [G6.permAct_apply, dodecadE] using this
  · intro h
    apply Multiplicative.toAdd.injective
    funext y
    rw [G6.permAct_apply]
    exact h y

@[expose] def presSub : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {σ | ∀ y, dodecadW (σ y) = dodecadW y}
  one_mem' y := rfl
  mul_mem' {σ τ} hσ hτ y := (hσ (τ y)).trans (hτ y)
  inv_mem' {σ} hσ y := by
    have := hσ (σ⁻¹ y)
    rw [perm_apply_inv] at this
    exact this.symm

theorem m24Fix_le_presSub : m24Fix dodecadE ≤ presSub := by
  intro σ hσ y
  have h := (permAct_dodecadE_eq_iff σ).1 hσ.2 (σ y)
  rw [perm_inv_apply] at h
  exact h.symm

theorem dodecadW_apply_j12 {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ presSub) (i : Fin 12) :
    dodecadW (σ (j12 i)) = 1 :=
  (hσ (j12 i)).trans (dodecadW_j12 i)

@[expose] def resHom : ↥presSub →* Equiv.Perm (Fin 12) where
  toFun σ :=
    { toFun := fun i => k12 ((σ : Equiv.Perm (Fin 24)) (j12 i))
      invFun := fun i => k12 ((σ : Equiv.Perm (Fin 24))⁻¹ (j12 i))
      left_inv := fun i => by
        simp only
        rw [j12_k12 _ (dodecadW_apply_j12 σ.2 i), perm_inv_apply, k12_j12]
      right_inv := fun i => by
        simp only
        rw [j12_k12 _ (dodecadW_apply_j12 (presSub.inv_mem σ.2) i), perm_apply_inv,
          k12_j12] }
  map_one' := Equiv.ext fun i => by
    simp only [Equiv.coe_fn_mk, OneMemClass.coe_one, Equiv.Perm.one_apply]
    exact k12_j12 i
  map_mul' σ τ := Equiv.ext fun i => by
    simp only [Equiv.coe_fn_mk, Subgroup.coe_mul, Equiv.Perm.mul_apply]
    rw [j12_k12 _ (dodecadW_apply_j12 τ.2 i)]

@[expose] def res12 : ↥(m24Fix dodecadE) →* Equiv.Perm (Fin 12) :=
  resHom.comp (Subgroup.inclusion m24Fix_le_presSub)

theorem m12A_mem_m24Fix : m12A ∈ m24Fix dodecadE :=
  ⟨m12A_mem, (permAct_dodecadE_eq_iff m12A).2 m12A_fix⟩

theorem m12B_mem_m24Fix : m12B ∈ m24Fix dodecadE :=
  ⟨m12B_mem, (permAct_dodecadE_eq_iff m12B).2 m12B_fix⟩

theorem res12_m12A : res12 ⟨m12A, m12A_mem_m24Fix⟩ = CFSG.Sporadic.Mathieu.m12gA :=
  Equiv.ext res_m12A

theorem res12_m12B : res12 ⟨m12B, m12B_mem_m24Fix⟩ = CFSG.Sporadic.Mathieu.m12gB :=
  Equiv.ext res_m12B

theorem m12_le_range_res12 : CFSG.Blueprint.NativeSporadic.M12 ≤ res12.range := by
  rw [CFSG.Sporadic.Mathieu.m12_eq, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨_, res12_m12A⟩
  · exact ⟨_, res12_m12B⟩

end CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

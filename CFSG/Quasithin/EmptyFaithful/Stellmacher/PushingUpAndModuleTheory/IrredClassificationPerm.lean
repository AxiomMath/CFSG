module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

@[expose] def dtQuad : Fin 15 → Fin 5 × Fin 5 × Fin 5 × Fin 5 :=
  ![(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 1, 3), (0, 2, 1, 4), (0, 2, 3, 4),
    (0, 3, 1, 2), (0, 3, 1, 4), (0, 3, 2, 4), (0, 4, 1, 2), (0, 4, 1, 3), (0, 4, 2, 3),
    (1, 2, 3, 4), (1, 3, 2, 4), (1, 4, 2, 3)]

@[expose] def dt (k : Fin 15) : Perm (Fin 5) :=
  swap (dtQuad k).1 (dtQuad k).2.1 * swap (dtQuad k).2.2.1 (dtQuad k).2.2.2

@[expose] def zDT : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem dt_injective : Function.Injective dt := by
  have h : ∀ a b : Fin 15, dt a = dt b → a = b := by decide +kernel
  exact fun a b hab => h a b hab

theorem exists_dt_conj (σ : Perm (Fin 5)) (ω : Fin 15) : ∃ ω', dt ω' = σ * dt ω * σ⁻¹ := by
  have hcases : ∀ p : Perm (Fin 5), p ≠ 1 → p * p = 1 → Perm.sign p = 1 → ∃ ω, dt ω = p := by
    decide +kernel
  have hne : ∀ ω, dt ω ≠ 1 := by decide +kernel
  have hsq : ∀ ω, dt ω * dt ω = 1 := by decide +kernel
  have hsign : ∀ ω, Perm.sign (dt ω) = 1 := by decide +kernel
  refine hcases _ ?_ ?_ ?_
  · intro h
    apply hne ω
    have := congrArg (fun q => σ⁻¹ * q * σ) h
    simpa [mul_assoc] using this
  · calc σ * dt ω * σ⁻¹ * (σ * dt ω * σ⁻¹) = σ * (dt ω * dt ω) * σ⁻¹ := by group
      _ = 1 := by rw [hsq]; group
  · simp [Perm.sign_mul, hsign]

noncomputable def piF (σ : Perm (Fin 5)) (ω : Fin 15) : Fin 15 :=
  Classical.choose (exists_dt_conj σ ω)

theorem dt_piF (σ : Perm (Fin 5)) (ω : Fin 15) : dt (piF σ ω) = σ * dt ω * σ⁻¹ :=
  Classical.choose_spec (exists_dt_conj σ ω)

theorem piF_eq_of {σ : Perm (Fin 5)} {ω ω' : Fin 15} (h : dt ω' = σ * dt ω * σ⁻¹) :
    piF σ ω = ω' :=
  dt_injective (by rw [dt_piF, h])

@[expose] def rotTab : Fin 15 → Fin 15 := ![12, 6, 9, 13, 3, 10, 14, 4, 7, 0, 1, 2, 11, 8, 5]

@[expose] def swapTab : Fin 15 → Fin 15 := ![0, 1, 2, 6, 9, 12, 3, 10, 13, 4, 7, 14, 5, 8, 11]

theorem piF_rot (ω : Fin 15) : piF (finRotate 5) ω = rotTab ω := by
  have h : ∀ ω : Fin 15, dt (rotTab ω) = finRotate 5 * dt ω * (finRotate 5)⁻¹ := by
    decide +kernel
  exact piF_eq_of (h ω)

theorem piF_swap (ω : Fin 15) : piF (swap 0 1) ω = swapTab ω := by
  have h : ∀ ω : Fin 15, dt (swapTab ω) = swap 0 1 * dt ω * (swap 0 1)⁻¹ := by decide +kernel
  exact piF_eq_of (h ω)

theorem piF_mul (σ τ : Perm (Fin 5)) (ω : Fin 15) : piF (σ * τ) ω = piF σ (piF τ ω) := by
  apply dt_injective
  rw [dt_piF, dt_piF, dt_piF]
  group

theorem piF_one (ω : Fin 15) : piF 1 ω = ω := by
  apply dt_injective
  rw [dt_piF]
  group

@[expose] noncomputable def piHom : Perm (Fin 5) →* Perm (Fin 15) where
  toFun σ :=
    { toFun := piF σ
      invFun := piF σ⁻¹
      left_inv := fun ω => by rw [← piF_mul, inv_mul_cancel, piF_one]
      right_inv := fun ω => by rw [← piF_mul, mul_inv_cancel, piF_one] }
  map_one' := Equiv.ext fun ω => piF_one ω
  map_mul' := fun σ τ => Equiv.ext fun ω => piF_mul σ τ ω

noncomputable abbrev Pm : Model 5 where
  W := Multiplicative (Fin 15 → ZMod 2)
  act := (G6.permAct 15).comp piHom
  sq := by
    intro w
    apply Multiplicative.toAdd.injective
    funext i
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h2 _

theorem Pm_act_apply (σ : Perm (Fin 5)) (x : Pm.W) (ω : Fin 15) :
    Multiplicative.toAdd (Pm.act σ x) ω = Multiplicative.toAdd x (piF σ⁻¹ ω) := by
  show Multiplicative.toAdd (G6.permAct 15 (piHom σ) x) ω = _
  rw [G6.permAct_apply]
  rfl

@[expose] noncomputable def frobHom (M : Model 5) (u : Fin 15 → M.W) : Pm.W →* M.W where
  toFun x := ∏ ω, if Multiplicative.toAdd x ω = 1 then u ω else 1
  map_one' := by
    refine Finset.prod_eq_one fun ω _ => ?_
    have h : Multiplicative.toAdd (1 : Multiplicative (Fin 15 → ZMod 2)) ω = 0 := rfl
    show (if Multiplicative.toAdd (1 : Multiplicative (Fin 15 → ZMod 2)) ω = 1 then u ω else 1) = 1
    rw [h]
    simp
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ω _ => ?_
    have key : ∀ a b : ZMod 2, (if a + b = 1 then u ω else 1) =
        (if a = 1 then u ω else 1) * (if b = 1 then u ω else 1) := by
      intro a b
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      have e1 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases e1 a with rfl | rfl <;> rcases e1 b with rfl | rfl <;> simp [h11, M.sq (u ω)]
    exact key _ _

theorem frobHom_act (M : Model 5) (u : Fin 15 → M.W)
    (hu : ∀ (σ : Perm (Fin 5)) (ω : Fin 15), M.act σ (u ω) = u (piF σ ω))
    (σ : Perm (Fin 5)) (x : Pm.W) :
    frobHom M u (Pm.act σ x) = M.act σ (frobHom M u x) := by
  show (∏ ω, if Multiplicative.toAdd (Pm.act σ x) ω = 1 then u ω else 1) =
    M.act σ (∏ ω, if Multiplicative.toAdd x ω = 1 then u ω else 1)
  rw [map_prod]
  symm
  refine Fintype.prod_equiv (piHom σ) _ _ fun ω => ?_
  have h1 : (piHom σ) ω = piF σ ω := rfl
  rw [h1, Pm_act_apply, ← piF_mul, inv_mul_cancel, piF_one]
  split_ifs <;> simp [hu]

theorem exists_conj_zDT : ∀ ω : Fin 15, ∃ g : Perm (Fin 5), g * zDT * g⁻¹ = dt ω := by
  decide +kernel

theorem centralizer_zDT {s : Perm (Fin 5)} (h : s * zDT * s⁻¹ = zDT) : s ∈ S5Syl := by
  have key : ∀ s : Perm (Fin 5), s * zDT * s⁻¹ = zDT → s ∈ S5SylF := by decide +kernel
  exact (mem_S5Syl_iff s).mpr (key s h)

theorem dt_three : dt 3 = zDT := by decide +kernel

end CFSG.Quasithin.F53Mod

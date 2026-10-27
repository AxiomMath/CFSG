module

public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.EmptyFaithful.SBc5S8Part

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth

namespace SBc5S8

set_option maxRecDepth 100000

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[expose] def quadVec : ↥(permCore 8) :=
  ⟨fun i => if i.val < 4 then 1 else 0, by
    show ∑ i : Fin 8, (fun i : Fin 8 => if i.val < 4 then (1 : ZMod 2) else 0) i = 0
    decide⟩

@[expose] def w0 : p4insporth_V8 := Submodule.Quotient.mk quadVec

@[expose] def s8Stab (w : p4insporth_V8) : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | p4insporth_perm8Hom σ w = w}
  one_mem' := by
    show p4insporth_perm8Hom 1 w = w
    rw [map_one]
    rfl
  mul_mem' := by
    intro a b ha hb
    have ha' : p4insporth_perm8Hom a w = w := ha
    have hb' : p4insporth_perm8Hom b w = w := hb
    show p4insporth_perm8Hom (a * b) w = w
    rw [map_mul, LinearEquiv.mul_apply, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : p4insporth_perm8Hom a w = w := ha
    show p4insporth_perm8Hom a⁻¹ w = w
    have h : p4insporth_perm8Hom a⁻¹ (p4insporth_perm8Hom a w) = w := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [ha'] at h

theorem mem_s8Stab {w : p4insporth_V8} {σ : Equiv.Perm (Fin 8)} :
    σ ∈ s8Stab w ↔ p4insporth_perm8Hom σ w = w := Iff.rfl

theorem perm8Hom_fix_iff (σ : Equiv.Perm (Fin 8)) (x : ↥(permCore 8)) :
    p4insporth_perm8Hom σ (Submodule.Quotient.mk x) = Submodule.Quotient.mk x ↔
      ∃ a : ZMod 2, ∀ i : Fin 8, x.1 (σ.symm i) - x.1 i = a := by
  rw [p4insporth_perm8Hom_mk, Submodule.Quotient.eq]
  constructor
  · intro h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
    refine ⟨a, fun i => ?_⟩
    have := congrFun (congrArg Subtype.val ha) i
    simpa [p4insporth_L8, p4insporth_one8, p4insporth_permHom_apply, permAct] using this.symm
  · rintro ⟨a, ha⟩
    refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
    apply Subtype.ext
    funext i
    simpa [p4insporth_one8, p4insporth_permHom_apply, permAct] using (ha i).symm

theorem ite_eq_ite_iff (p r : Prop) [Decidable p] [Decidable r] :
    ((if p then (1 : ZMod 2) else 0) = if r then 1 else 0) ↔ (p ↔ r) := by
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem ite_sub_ite_eq_one (p r : Prop) [Decidable p] [Decidable r] :
    ((if p then (1 : ZMod 2) else 0) - (if r then 1 else 0) = 1) ↔ ¬ (p ↔ r) := by
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem s8Stab_w0 : s8Stab w0 = partStab := by
  ext σ
  rw [mem_s8Stab, w0, perm8Hom_fix_iff, mem_partStab]
  have hq : ∀ j : Fin 8, quadVec.1 j = if j.val < 4 then 1 else 0 := fun j => rfl
  simp only [hq]
  constructor
  · rintro ⟨a, ha⟩
    rcases zmod2_cases a with rfl | rfl
    · left
      intro i
      have h := ha (σ i)
      rw [Equiv.symm_apply_apply, sub_eq_zero, ite_eq_ite_iff] at h
      exact h.symm
    · right
      intro i
      have h := ha (σ i)
      rw [Equiv.symm_apply_apply, ite_sub_ite_eq_one] at h
      tauto
  · rintro (h | h)
    · refine ⟨0, fun i => ?_⟩
      have h1 := h (σ.symm i)
      rw [Equiv.apply_symm_apply] at h1
      rw [sub_eq_zero, ite_eq_ite_iff]
      exact h1.symm
    · refine ⟨1, fun i => ?_⟩
      have h1 := h (σ.symm i)
      rw [Equiv.apply_symm_apply] at h1
      rw [ite_sub_ite_eq_one]
      tauto

@[expose] def e1 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def e2 : Equiv.Perm (Fin 8) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def e3 : Equiv.Perm (Fin 8) := Equiv.swap 4 5 * Equiv.swap 6 7

@[expose] def e4 : Equiv.Perm (Fin 8) := Equiv.swap 4 6 * Equiv.swap 5 7

theorem fix_aux : ∀ (y : Fin 8 → ZMod 2) (a1 a2 a3 a4 : ZMod 2),
    (∀ i : Fin 8, y (e1.symm i) - y i = a1) → (∀ i : Fin 8, y (e2.symm i) - y i = a2) →
    (∀ i : Fin 8, y (e3.symm i) - y i = a3) → (∀ i : Fin 8, y (e4.symm i) - y i = a4) →
      (y = 0 ∨ y = 1 ∨ y = quadVec.1 ∨ y = quadVec.1 + 1) := by
  decide +kernel

theorem fix_gens {v : p4insporth_V8} (h1 : p4insporth_perm8Hom e1 v = v)
    (h2 : p4insporth_perm8Hom e2 v = v) (h3 : p4insporth_perm8Hom e3 v = v)
    (h4 : p4insporth_perm8Hom e4 v = v) : v = 0 ∨ v = w0 := by
  revert h1 h2 h3 h4
  refine Submodule.Quotient.induction_on _ v fun x => ?_
  intro h1 h2 h3 h4
  obtain ⟨a1, k1⟩ := (perm8Hom_fix_iff _ _).1 h1
  obtain ⟨a2, k2⟩ := (perm8Hom_fix_iff _ _).1 h2
  obtain ⟨a3, k3⟩ := (perm8Hom_fix_iff _ _).1 h3
  obtain ⟨a4, k4⟩ := (perm8Hom_fix_iff _ _).1 h4
  have hx := fix_aux x.1 a1 a2 a3 a4 k1 k2 k3 k4
  have hone : (Submodule.Quotient.mk p4insporth_one8 : p4insporth_V8) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self _)
  rcases hx with hx | hx | hx | hx
  · left
    have : x = 0 := Subtype.ext hx
    rw [this]
    rfl
  · left
    have : x = p4insporth_one8 := Subtype.ext hx
    rw [this, hone]
  · right
    have : x = quadVec := Subtype.ext hx
    rw [this]
    rfl
  · right
    have : x = quadVec + p4insporth_one8 := Subtype.ext hx
    rw [this, Submodule.Quotient.mk_add, hone, add_zero]
    rfl

theorem act_conj (g e : Equiv.Perm (Fin 8)) (v : p4insporth_V8) :
    p4insporth_perm8Hom e (p4insporth_perm8Hom g⁻¹ v) =
      p4insporth_perm8Hom g⁻¹ (p4insporth_perm8Hom (g * e * g⁻¹) v) := by
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul,
    show g⁻¹ * (g * e * g⁻¹) = e * g⁻¹ by group]

theorem fix_conj {g : Equiv.Perm (Fin 8)} {v : p4insporth_V8}
    (h1 : p4insporth_perm8Hom (g * e1 * g⁻¹) v = v) (h2 : p4insporth_perm8Hom (g * e2 * g⁻¹) v = v)
    (h3 : p4insporth_perm8Hom (g * e3 * g⁻¹) v = v) (h4 : p4insporth_perm8Hom (g * e4 * g⁻¹) v = v) :
    p4insporth_perm8Hom g⁻¹ v = 0 ∨ p4insporth_perm8Hom g⁻¹ v = w0 :=
  fix_gens (by rw [act_conj, h1]) (by rw [act_conj, h2]) (by rw [act_conj, h3])
    (by rw [act_conj, h4])

theorem s8Stab_conj (g : Equiv.Perm (Fin 8)) (w : p4insporth_V8) (σ : Equiv.Perm (Fin 8)) :
    σ ∈ s8Stab (p4insporth_perm8Hom g w) ↔ g⁻¹ * σ * g ∈ s8Stab w := by
  rw [mem_s8Stab, mem_s8Stab]
  have hinv : ∀ X : p4insporth_V8, p4insporth_perm8Hom g⁻¹ (p4insporth_perm8Hom g X) = X := fun X => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hcancel : ∀ X : p4insporth_V8, p4insporth_perm8Hom g (p4insporth_perm8Hom g⁻¹ X) = X := fun X => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hconj : p4insporth_perm8Hom (g⁻¹ * σ * g) w =
      p4insporth_perm8Hom g⁻¹ (p4insporth_perm8Hom σ (p4insporth_perm8Hom g w)) := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hconj]
  constructor
  · intro h
    rw [h, hinv]
  · intro h
    have h1 := congrArg (p4insporth_perm8Hom g) h
    rw [hcancel] at h1
    exact h1

end SBc5S8

end CFSG.Quasithin

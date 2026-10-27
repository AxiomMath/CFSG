module

public import CFSG.Sporadic.Schreier.Co1LocalModuleUniq
public import CFSG.Sporadic.Schreier.Co1Generation

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

theorem rep_mul (ρ : GA →* GL (Fin 24) (ZMod 2)) {g h : GL24} (hg : g ∈ GA) (hh : h ∈ GA) :
    ρ ⟨g * h, GA.mul_mem hg hh⟩ = ρ ⟨g, hg⟩ * ρ ⟨h, hh⟩ := by
  rw [← map_mul]
  rfl

theorem rep_pow (ρ : GA →* GL (Fin 24) (ZMod 2)) {g : GL24} (hg : g ∈ GA) (n : ℕ) :
    ρ ⟨g ^ n, GA.pow_mem hg n⟩ = ρ ⟨g, hg⟩ ^ n := by
  rw [← map_pow]
  rfl

theorem rep_one (ρ : GA →* GL (Fin 24) (ZMod 2)) : ρ ⟨1, GA.one_mem⟩ = 1 := map_one ρ

theorem conj_rel {ρ : GA →* GL (Fin 24) (ZMod 2)} {T : GL24}
    (hTA : ∀ (a : GL24) (ha : a ∈ A), T * ρ ⟨a, A_le_GA ha⟩ = a * T) {a : GL24} (ha : a ∈ A) :
    T⁻¹ * a = ρ ⟨a, A_le_GA ha⟩ * T⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hTA a ha, mul_inv_cancel_right]

section ConjX

variable {ρ : GA →* GL (Fin 24) (ZMod 2)} {T : GL24}
  (hTA : ∀ (a : GL24) (ha : a ∈ A), T * ρ ⟨a, A_le_GA ha⟩ = a * T)

include hTA in
theorem conjX_extH
    (i : Fin 3) :
    T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ * extH i =
      extK i * (T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹) := by
  have hh : extH i ∈ A := locWord_mem _
  have hk : extK i ∈ A := locWord_mem _
  have e2 : ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * ρ ⟨extH i, A_le_GA hh⟩ =
      ρ ⟨extK i, A_le_GA hk⟩ * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ := by
    rw [← rep_mul, ← rep_mul]
    exact congrArg ρ (Subtype.ext (x_mul_extH i))
  calc T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ * extH i
      = T * (ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * (T⁻¹ * extH i)) := by simp only [mul_assoc]
    _ = T * (ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * ρ ⟨extH i, A_le_GA hh⟩) * T⁻¹ := by
        rw [conj_rel hTA hh]
        simp only [mul_assoc]
    _ = T * ρ ⟨extK i, A_le_GA hk⟩ * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ := by
        rw [e2]
        simp only [mul_assoc]
    _ = extK i * T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ := by rw [hTA _ hk]
    _ = extK i * (T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹) := by simp only [mul_assoc]

theorem conjX_sq :
    (T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹) ^ 2 = 1 := by
  have hsq : ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ ^ 2 = 1 := by
    rw [← rep_pow, ← rep_one ρ]
    exact congrArg ρ (Subtype.ext local_extension_matrix_rigidity.2.2.1)
  rw [conj_pow, hsq, mul_one, mul_inv_cancel]

include hTA in
theorem conjX_pow :
    (T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ * a 1) ^ 28 = 1 := by
  have ha : a 1 ∈ A := E_le_A (a_mem_E 1)
  have hpow : (ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * ρ ⟨a 1, A_le_GA ha⟩) ^ 28 = 1 := by
    rw [← rep_mul, ← rep_pow, ← rep_one ρ]
    exact congrArg ρ (Subtype.ext local_extension_matrix_rigidity.2.2.2.1)
  have e2 : T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ * a 1 =
      T * (ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * ρ ⟨a 1, A_le_GA ha⟩) * T⁻¹ := by
    rw [mul_assoc (T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩), conj_rel hTA ha]
    simp only [mul_assoc]
  rw [e2, conj_pow, hpow, mul_one, mul_inv_cancel]

include hTA in
theorem conj_x :
    T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ = ThreeLocal.x * T := by
  have hX := rigidity_main _ (conjX_extH hTA) conjX_sq (conjX_pow hTA)
  calc T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩
      = T * ρ ⟨ThreeLocal.x, threeLocal_mem.1⟩ * T⁻¹ * T := by rw [inv_mul_cancel_right]
    _ = ThreeLocal.x * T := by rw [hX]

end ConjX

@[expose] noncomputable def intertw (ρ : GA →* GL (Fin 24) (ZMod 2)) (T : GL24) :
    Subgroup GL24 where
  carrier := {g | ∃ hg : g ∈ GA, T * ρ ⟨g, hg⟩ = g * T}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨GA.mul_mem hg hh, ?_⟩
    rw [rep_mul ρ hg hh, ← mul_assoc, hg', mul_assoc, hh', ← mul_assoc]
  one_mem' := ⟨GA.one_mem, by rw [rep_one, mul_one, one_mul]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨GA.inv_mem hg, ?_⟩
    have h1 : ρ ⟨g⁻¹, GA.inv_mem hg⟩ = (ρ ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h1, mul_inv_eq_iff_eq_mul, mul_assoc, hg', inv_mul_cancel_left]

theorem exists_conj_natural_GA
    (ρ : GA →* GL (Fin 24) (ZMod 2))
    (hE : ∃ e : E, ρ ⟨e, A_le_GA (E_le_A e.2)⟩ ≠ 1) :
    ∃ T : GL (Fin 24) (ZMod 2), ∀ g : GA, T * ρ g = (g : GL24) * T := by
  obtain ⟨T, hT⟩ := exists_conj_natural (ρ.comp (Subgroup.inclusion A_le_GA)) hE
  have hTA : ∀ (a : GL24) (ha : a ∈ A), T * ρ ⟨a, A_le_GA ha⟩ = a * T := fun a ha => hT ⟨a, ha⟩
  have hle : Subgroup.closure ((A : Set GL24) ∪ {ThreeLocal.x}) ≤ intertw ρ T := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    rcases hg with hg | hg
    · exact ⟨A_le_GA hg, hTA g hg⟩
    · rw [Set.mem_singleton_iff.mp hg]
      exact ⟨threeLocal_mem.1, conj_x hTA⟩
  rw [local_enlargement_generation.1] at hle
  refine ⟨T, fun g => ?_⟩
  obtain ⟨_, h⟩ := hle g.2
  exact h

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def matRepGA (b : Module.Basis (Fin 24) (ZMod 2) W)
    (ρ : Representation (ZMod 2) GA W) : GA →* GL (Fin 24) (ZMod 2) where
  toFun g := ⟨LinearMap.toMatrix b b (ρ g), LinearMap.toMatrix b b (ρ g⁻¹),
    by rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one],
    by rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]⟩
  map_one' := Units.ext (by
    show LinearMap.toMatrix b b (ρ 1) = 1
    rw [map_one, LinearMap.toMatrix_one])
  map_mul' g h := Units.ext (by
    show LinearMap.toMatrix b b (ρ (g * h)) =
      LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ h)
    rw [map_mul, LinearMap.toMatrix_mul])

theorem matRepGA_mulVec (b : Module.Basis (Fin 24) (ZMod 2) W)
    (ρ : Representation (ZMod 2) GA W) (g : GA) (w : W) :
    ((matRepGA b ρ g : GL24) : Mat24) *ᵥ b.repr w = b.repr (ρ g w) :=
  LinearMap.toMatrix_mulVec_repr b b (ρ g) w

theorem exists_equiv_natural_module_GA
    (hW : Module.finrank (ZMod 2) W = 24)
    (ρ : Representation (ZMod 2) GA W) (hE : ∃ e : E, ρ ⟨e, A_le_GA (E_le_A e.2)⟩ ≠ 1) :
    ∃ φ : W ≃ₗ[ZMod 2] (Fin 24 → ZMod 2), ∀ (g : GA) (w : W),
      φ (ρ g w) = ((g : GL24) : Mat24) *ᵥ φ w := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_eq_succ hW
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 24) (ZMod 2) W) :=
    ⟨Module.finBasisOfFinrankEq (ZMod 2) W hW⟩
  have hE' : ∃ e : E, matRepGA b ρ ⟨e, A_le_GA (E_le_A e.2)⟩ ≠ 1 := by
    obtain ⟨e, he⟩ := hE
    refine ⟨e, fun h => he ?_⟩
    have h1 : LinearMap.toMatrix b b (ρ ⟨e, A_le_GA (E_le_A e.2)⟩) = LinearMap.toMatrix b b 1 := by
      rw [LinearMap.toMatrix_one]
      exact congrArg Units.val h
    exact (LinearMap.toMatrix b b).injective h1
  obtain ⟨T, hT⟩ := exists_conj_natural_GA (matRepGA b ρ) hE'
  have hφ : ∀ v, Matrix.toLinearEquiv' (T : Mat24) (Units.invertible T) v = (T : Mat24) *ᵥ v :=
    fun v => Matrix.toLin'_apply (T : Mat24) v
  refine ⟨b.equivFun.trans (Matrix.toLinearEquiv' (T : Mat24) (Units.invertible T)),
    fun g w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hφ, hφ, Module.Basis.equivFun_apply,
    Module.Basis.equivFun_apply, ← matRepGA_mulVec, mulVec_mulVec, mulVec_mulVec]
  have h := congrArg Units.val (hT g)
  rw [Units.val_mul, Units.val_mul] at h
  rw [h]

theorem a_one_ne_one :
    a 1 ≠ 1 := local_extension_matrix_rigidity.2.1

@[expose] noncomputable def autRepGA (α : GA ≃* GA) : GA →* GL (Fin 24) (ZMod 2) where
  toFun g := α g
  map_one' := by
    show ((α 1 : GA) : GL24) = 1
    rw [map_one, OneMemClass.coe_one]
  map_mul' g h := by
    show ((α (g * h) : GA) : GL24) = (α g : GL24) * (α h : GL24)
    rw [map_mul, Subgroup.coe_mul]

theorem nontrivial_of_injective
    {ρ : GA →* GL (Fin 24) (ZMod 2)} (hρ : Function.Injective ρ) :
    ∃ e : E, ρ ⟨e, A_le_GA (E_le_A e.2)⟩ ≠ 1 := by
  refine ⟨⟨a 1, a_mem_E 1⟩, fun h => a_one_ne_one ?_⟩
  have h1 := (map_eq_one_iff ρ hρ).mp h
  exact congrArg Subtype.val h1

theorem autRepGA_injective (α : GA ≃* GA) : Function.Injective (autRepGA α) := fun _ _ hgh =>
  α.injective (Subtype.ext hgh)

theorem degree_twenty_four_module_uniqueness :
    (∀ ρ : GA →* GL (Fin 24) (ZMod 2), (∃ e : E, ρ ⟨e, A_le_GA (E_le_A e.2)⟩ ≠ 1) →
      ∃ T : GL (Fin 24) (ZMod 2), ∀ g : GA, T * ρ g = (g : GL24) * T) ∧
    (∀ (W : Type*) [AddCommGroup W] [Module (ZMod 2) W], Module.finrank (ZMod 2) W = 24 →
      ∀ ρ : Representation (ZMod 2) GA W, (∃ e : E, ρ ⟨e, A_le_GA (E_le_A e.2)⟩ ≠ 1) →
        ∃ φ : W ≃ₗ[ZMod 2] (Fin 24 → ZMod 2), ∀ (g : GA) (w : W),
          φ (ρ g w) = ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ φ w) ∧
    (∀ ρ : GA →* GL (Fin 24) (ZMod 2), Function.Injective ρ →
      ∃ T : GL (Fin 24) (ZMod 2), ∀ g : GA, T * ρ g = (g : GL24) * T) ∧
    ∀ α : GA ≃* GA, ∃ T : GL (Fin 24) (ZMod 2), ∀ g : GA, T * (α g : GL24) = (g : GL24) * T :=
  ⟨fun ρ hE => exists_conj_natural_GA ρ hE,
    fun _ _ _ hW ρ hE => exists_equiv_natural_module_GA hW ρ hE,
    fun ρ hρ => exists_conj_natural_GA ρ (nontrivial_of_injective hρ),
    fun α => exists_conj_natural_GA (autRepGA α) (nontrivial_of_injective (autRepGA_injective α))⟩

end CFSG.Sporadic.Co1Schreier

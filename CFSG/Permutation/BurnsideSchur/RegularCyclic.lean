module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG

open MulAction

namespace BurnsideSchur

variable {Ω α : Type*}

section Transport

variable (e : Ω ≃ α) (G : Subgroup (Equiv.Perm Ω))

private noncomputable def mapPermCongrHom : G →* G.map e.permCongrHom.toMonoidHom :=
  (G.equivMapOfInjective _ e.permCongrHom.injective).toMonoidHom

private theorem mapPermCongrHom_surjective : Function.Surjective (mapPermCongrHom e G) :=
  (G.equivMapOfInjective _ e.permCongrHom.injective).surjective

private def permCongrActionHom : Ω →ₑ[mapPermCongrHom e G] α where
  toFun := e
  map_smul' g x := by
    change e ((g : Equiv.Perm Ω) x) = e.permCongr g (e x)
    simp

theorem isPreprimitive_map_permCongrHom_iff :
    IsPreprimitive (G.map e.permCongrHom.toMonoidHom) α ↔ IsPreprimitive G Ω :=
  (isPreprimitive_congr (f := permCongrActionHom e G) (mapPermCongrHom_surjective e G)
    e.bijective).symm

theorem isMultiplyPretransitive_map_permCongrHom_iff (n : ℕ) :
    IsMultiplyPretransitive (G.map e.permCongrHom.toMonoidHom) α n ↔
      IsMultiplyPretransitive G Ω n :=
  (IsPretransitive.of_embedding_congr (f := permCongrActionHom e G)
    (mapPermCongrHom_surjective e G) e.bijective).symm

end Transport

theorem exists_equiv_zmod_image_eq [Finite Ω] [Nonempty Ω] (K : Subgroup (Equiv.Perm Ω))
    [IsCyclic K] [IsPretransitive K Ω] (hK : ∀ x : Ω, stabilizer K x = ⊥) :
    ∃ e : Ω ≃ ZMod (Nat.card Ω), e.permCongr '' (K : Set (Equiv.Perm Ω)) =
      {t | ∃ a, ∀ x, t x = x + a} := by
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have horbit : Function.Bijective fun k : K => k • ω := by
    refine ⟨fun k k' h => ?_, fun x => exists_smul_eq K ω x⟩
    have : k'⁻¹ * k ∈ stabilizer K ω := by
      rw [mem_stabilizer_iff, mul_smul]
      exact inv_smul_eq_iff.2 h
    rw [hK ω, Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this.symm
  have hcard : Nat.card (Multiplicative (ZMod (Nat.card Ω))) = Nat.card K := by
    rw [Nat.card_congr (Equiv.ofBijective _ horbit)]
    simp
  let φ : Multiplicative (ZMod (Nat.card Ω)) ≃* K := mulEquivOfCyclicCardEq hcard
  let f : ZMod (Nat.card Ω) ≃ Ω :=
    (Multiplicative.ofAdd.trans φ.toEquiv).trans (Equiv.ofBijective _ horbit)
  have hf (k : K) (a : ZMod (Nat.card Ω)) :
      (k : Equiv.Perm Ω) (f a) = f (a + Multiplicative.toAdd (φ.symm k)) := by
    change k • φ (Multiplicative.ofAdd a) • ω =
      φ (Multiplicative.ofAdd (a + Multiplicative.toAdd (φ.symm k))) • ω
    rw [add_comm, ofAdd_add, map_mul, ofAdd_toAdd, MulEquiv.apply_symm_apply, mul_smul]
  refine ⟨f.symm, Set.ext fun t => ⟨?_, fun ⟨a, ha⟩ => ?_⟩⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨Multiplicative.toAdd (φ.symm ⟨k, hk⟩), fun x => ?_⟩
    simpa using congrArg f.symm (hf ⟨k, hk⟩ x)
  · refine ⟨φ (Multiplicative.ofAdd a), (φ _).2, Equiv.ext fun x => ?_⟩
    rw [ha, Equiv.permCongr_apply, Equiv.symm_symm, hf, Equiv.symm_apply_apply,
      MulEquiv.symm_apply_apply, toAdd_ofAdd]

end BurnsideSchur

end CFSG

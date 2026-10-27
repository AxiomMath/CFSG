module

public import CFSG.Sporadic.Schreier.Co1LocalRep
public import CFSG.Sporadic.Schreier.Co1Descent

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

theorem exists_conj_natural
    (ρ : A →* GL (Fin 24) (ZMod 2))
    (hE : ∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) :
    ∃ T : GL (Fin 24) (ZMod 2), ∀ x : A, T * ρ x = (x : GL24) * T := by
  obtain ⟨f, hf⟩ := exists_equiv_natural hE
  have hsymm : ∀ (x : A) (v : Fin 24 → Kbar),
      f.symm (rhoK ρ x *ᵥ v) = rhoK A.subtype x *ᵥ f.symm v := by
    intro x v
    apply f.injective
    have := hf x (f.symm v)
    rw [repK_apply, repK_apply, LinearEquiv.apply_symm_apply] at this
    rw [LinearEquiv.apply_symm_apply, this]
  have hSv : ∀ v, LinearMap.toMatrix' f.symm.toLinearMap *ᵥ v = f.symm v := fun v =>
    LinearMap.toMatrix'_mulVec _ v
  have hS0 : LinearMap.toMatrix' f.symm.toLinearMap ≠ 0 := by
    intro h0
    have h1 := hSv (Pi.single 0 1)
    rw [h0, zero_mulVec] at h1
    have h2 : (Pi.single 0 1 : Fin 24 → Kbar) = 0 :=
      f.symm.injective (h1.symm.trans (map_zero _).symm)
    have h3 := congrFun h2 0
    rw [Pi.single_eq_same, Pi.zero_apply] at h3
    exact one_ne_zero h3
  have hSP : ∀ x : A, LinearMap.toMatrix' f.symm.toLinearMap *
      ((ρ x : GL24) : Mat24).map (algebraMap (ZMod 2) Kbar) =
      ((x : GL24) : Mat24).map (algebraMap (ZMod 2) Kbar) *
        LinearMap.toMatrix' f.symm.toLinearMap := fun x =>
    Matrix.ext_of_mulVec_single fun i => by
      rw [← mulVec_mulVec, ← mulVec_mulVec, hSv, hSv]
      exact hsymm x _
  obtain ⟨T, hT0, hT⟩ := Descent.exists_intertwiner_of_map (fun x : A => ((ρ x : GL24) : Mat24))
    (fun x : A => ((x : GL24) : Mat24)) hS0 hSP
  have hirr := ((degree_bound ρ hE).2 rfl).2
  have hTu : IsUnit T := Descent.isUnit_of_intertwiner (K := Kbar)
    (fun x : A => ((ρ x : GL24) : Mat24)) (fun x : A => ((x : GL24) : Mat24))
    (fun S hS => hirr S hS) hT0 hT
  refine ⟨hTu.unit, fun x => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec]
  exact hT x

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def matRep (b : Module.Basis (Fin 24) (ZMod 2) W)
    (ρ : Representation (ZMod 2) A W) : A →* GL (Fin 24) (ZMod 2) where
  toFun x := ⟨LinearMap.toMatrix b b (ρ x), LinearMap.toMatrix b b (ρ x⁻¹),
    by rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one],
    by rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one, LinearMap.toMatrix_one]⟩
  map_one' := Units.ext (by
    show LinearMap.toMatrix b b (ρ 1) = 1
    rw [map_one, LinearMap.toMatrix_one])
  map_mul' x y := Units.ext (by
    show LinearMap.toMatrix b b (ρ (x * y)) =
      LinearMap.toMatrix b b (ρ x) * LinearMap.toMatrix b b (ρ y)
    rw [map_mul, LinearMap.toMatrix_mul])

theorem matRep_mulVec (b : Module.Basis (Fin 24) (ZMod 2) W) (ρ : Representation (ZMod 2) A W)
    (x : A) (w : W) : ((matRep b ρ x : GL24) : Mat24) *ᵥ b.repr w = b.repr (ρ x w) :=
  LinearMap.toMatrix_mulVec_repr b b (ρ x) w

theorem exists_equiv_natural_module
    (hW : Module.finrank (ZMod 2) W = 24)
    (ρ : Representation (ZMod 2) A W) (hE : ∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) :
    ∃ φ : W ≃ₗ[ZMod 2] (Fin 24 → ZMod 2), ∀ (x : A) (w : W),
      φ (ρ x w) = ((x : GL24) : Mat24) *ᵥ φ w := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_eq_succ hW
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 24) (ZMod 2) W) :=
    ⟨Module.finBasisOfFinrankEq (ZMod 2) W hW⟩
  have hE' : ∃ e : E, matRep b ρ ⟨e, E_le_A e.2⟩ ≠ 1 := by
    obtain ⟨e, he⟩ := hE
    refine ⟨e, fun h => he ?_⟩
    have h1 : LinearMap.toMatrix b b (ρ ⟨e, E_le_A e.2⟩) = LinearMap.toMatrix b b 1 := by
      rw [LinearMap.toMatrix_one]
      exact congrArg Units.val h
    exact (LinearMap.toMatrix b b).injective h1
  obtain ⟨T, hT⟩ := exists_conj_natural (matRep b ρ) hE'
  have hφ : ∀ v, Matrix.toLinearEquiv' (T : Mat24) (Units.invertible T) v = (T : Mat24) *ᵥ v :=
    fun v => Matrix.toLin'_apply (T : Mat24) v
  refine ⟨b.equivFun.trans (Matrix.toLinearEquiv' (T : Mat24) (Units.invertible T)),
    fun x w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hφ, hφ, Module.Basis.equivFun_apply,
    Module.Basis.equivFun_apply, ← matRep_mulVec, mulVec_mulVec, mulVec_mulVec]
  have h := congrArg Units.val (hT x)
  rw [Units.val_mul, Units.val_mul] at h
  rw [h]

@[expose] noncomputable def autRep (α : GA ≃* GA) : A →* GL (Fin 24) (ZMod 2) where
  toFun x := α ⟨x, A_le_GA x.2⟩
  map_one' := by
    show ((α ⟨((1 : A) : GL24), A_le_GA (1 : A).2⟩ : GA) : GL24) = 1
    rw [show (⟨((1 : A) : GL24), A_le_GA (1 : A).2⟩ : GA) = 1 from rfl, map_one,
      OneMemClass.coe_one]
  map_mul' x y := by
    show ((α ⟨((x * y : A) : GL24), A_le_GA (x * y).2⟩ : GA) : GL24) =
      (α ⟨x, A_le_GA x.2⟩ : GL24) * (α ⟨y, A_le_GA y.2⟩ : GL24)
    rw [show (⟨((x * y : A) : GL24), A_le_GA (x * y).2⟩ : GA) =
      ⟨x, A_le_GA x.2⟩ * ⟨y, A_le_GA y.2⟩ from rfl, map_mul, Subgroup.coe_mul]

theorem autRep_nontrivial
    (α : GA ≃* GA) : ∃ e : E, autRep α ⟨e, E_le_A e.2⟩ ≠ 1 := by
  refine ⟨⟨a 0, a_mem_E 0⟩, fun h => z_ne_one ?_⟩
  have h1 : α ⟨a 0, A_le_GA (E_le_A (a_mem_E 0))⟩ = 1 := Subtype.ext h
  rw [map_eq_one_iff α α.injective] at h1
  rw [← a_zero]
  exact congrArg Subtype.val h1

theorem elementary_three_local_module_uniqueness :
    (∀ ρ : A →* GL (Fin 24) (ZMod 2), (∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) →
      ∃ T : GL (Fin 24) (ZMod 2), ∀ x : A, T * ρ x = (x : GL24) * T) ∧
    (∀ (W : Type*) [AddCommGroup W] [Module (ZMod 2) W], Module.finrank (ZMod 2) W = 24 →
      ∀ ρ : Representation (ZMod 2) A W, (∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) →
        ∃ φ : W ≃ₗ[ZMod 2] (Fin 24 → ZMod 2), ∀ (x : A) (w : W),
          φ (ρ x w) = ((x : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ φ w) ∧
    ∀ α : GA ≃* GA, ∃ T : GL (Fin 24) (ZMod 2), ∀ x : A,
      T * (α ⟨x, A_le_GA x.2⟩ : GL24) = (x : GL24) * T :=
  ⟨fun ρ hE => exists_conj_natural ρ hE,
    fun _ _ _ hW ρ hE => exists_equiv_natural_module hW ρ hE,
    fun α => exists_conj_natural (autRep α) (autRep_nontrivial α)⟩

end CFSG.Sporadic.Co1Schreier

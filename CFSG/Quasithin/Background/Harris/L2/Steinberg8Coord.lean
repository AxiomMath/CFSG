module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups TensorProduct

section Coord

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {F : Type*} [Field F] {ρ : Representation (ZMod 2) SL(2, F) V}
variable {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) V)
variable {E : Type*} [Field E] [Algebra (ZMod 2) E] (ι : EndRing ρ →+* E)

@[expose] noncomputable def coordV : V →ₗ[ZMod 2] (Fin m → E) :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v i => ι (b.equivFun v i)
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }

theorem coordV_apply (v : V) (i : Fin m) : coordV b ι v i = ι (b.equivFun v i) := rfl

@[expose] noncomputable def baseCoord : E ⊗[ZMod 2] V →ₗ[E] (Fin m → E) :=
  LinearMap.liftBaseChange E (coordV b ι)

theorem baseCoord_tmul (e : E) (v : V) : baseCoord b ι (e ⊗ₜ v) = e • coordV b ι v := rfl

variable [Finite V] [Fact ρ.IsIrreducible]

theorem coordV_rep (g : SL(2, F)) (v : V) :
    coordV b ι (ρ g v) = matRepE b ι g (coordV b ι v) := by
  funext i
  rw [matRepE_apply, coordV_apply]
  have h1 : b.equivFun (ρ g v) = (matRep b g).mulVec (b.equivFun v) := by
    have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) v
    simpa [matRep, Module.Basis.equivFun_apply, repD_apply] using this.symm
  rw [h1]
  exact RingHom.map_mulVec ι (matRep b g) (b.equivFun v) i

theorem baseCoord_rep (g : SL(2, F)) (x : E ⊗[ZMod 2] V) :
    baseCoord b ι (LinearMap.baseChange E (ρ g) x) = matRepE b ι g (baseCoord b ι x) := by
  induction x using TensorProduct.inductionOn with
  | tmul e v =>
    simp only [LinearMap.baseChange_tmul, baseCoord_tmul, coordV_rep, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Finite V] [Fact ρ.IsIrreducible] in
theorem baseCoord_surjective : Function.Surjective (baseCoord b ι) := by
  classical
  have hmem : ∀ j, (Pi.basisFun E (Fin m) j) ∈ LinearMap.range (baseCoord b ι) := by
    intro j
    refine ⟨1 ⊗ₜ b j, ?_⟩
    funext i
    simp [baseCoord_tmul, coordV_apply, Pi.single_apply, eq_comm]
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basisFun E (Fin m)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact hmem j

omit [Fact ρ.IsIrreducible] in
theorem baseCoord_bijective (hm : Module.finrank (ZMod 2) V = m) :
    Function.Bijective (baseCoord b ι) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have : Module.Finite E (E ⊗[ZMod 2] V) := inferInstance
  have hrk : Module.finrank E (E ⊗[ZMod 2] V) = Module.finrank E (Fin m → E) := by
    rw [Module.finrank_baseChange, hm, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mpr
    (baseCoord_surjective b ι), baseCoord_surjective b ι⟩

end Coord

end CFSG.Quasithin.G11.Harris.L2

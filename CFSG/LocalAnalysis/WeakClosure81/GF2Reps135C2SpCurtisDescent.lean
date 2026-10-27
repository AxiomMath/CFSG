module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
public import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup.X7 CFSG.LieType.SpecialLinear
open scoped Matrix TensorProduct

private theorem spCD_isIrreducibleAdd_of_isIrreducible {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible] :
    IsIrreducibleAdd (fun (g : G) (w : W) => ρ g w) := by
  intro A hA
  have hirr := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp
    (inferInstance : ρ.IsIrreducible)
  rcases hirr.2 (AddSubgroup.toZModSubmodule 2 A) (fun g v hv => by
    rw [AddSubgroup.mem_toZModSubmodule] at hv ⊢
    exact hA g hv) with h | h
  · left
    rw [← AddSubgroup.toZModSubmodule_toAddSubgroup (n := 2) A, h]
    rfl
  · right
    rw [← AddSubgroup.toZModSubmodule_toAddSubgroup (n := 2) A, h]
    rfl

private theorem spCD_addEquiv_of_addHom {G V I K k : Type*} [Group G] [AddCommGroup V]
    [Fintype I] [Field K] [Field k] [Algebra K k] [DistribMulAction G V]
    (hV : IsIrreducibleAdd (fun (g : G) (v : V) => g • v))
    (T : G → Matrix I I K) (hT : IsIrreducibleAdd (fun (g : G) (v : I → K) => T g *ᵥ v))
    (Φ : V →+ (I → k)) (hΦ : Φ ≠ 0)
    (hΦeq : ∀ g v, Φ (g • v) = (T g).map (algebraMap K k) *ᵥ Φ v) :
    ∃ β : V ≃+ (I → K), ∀ g v, β (g • v) = T g *ᵥ β v := by
  obtain ⟨Ψ, hΨ, hΨeq⟩ := exists_addHom_of_extend T Φ hΦ hΦeq
  have hbij := bijective_of_ne_zero_of_irreducible T hV hT Ψ hΨ hΨeq
  exact ⟨AddEquiv.ofBijective Ψ hbij, fun g v => hΨeq g v⟩

theorem exists_addEquiv_of_extendScalars_equiv {G : Type*} [Group G] {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W)
    [ρ.IsIrreducible] {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (R : G →* Matrix I I K) (hR : IsIrreducibleAdd (fun (g : G) (v : I → K) => R g *ᵥ v))
    (k : Type*) [Field k] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k]
    (φ : K →+* k)
    (β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) ≃ₗ[k] (I → k))
    (hβ : ∀ (g : G) v,
      β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
        matRep (matMap φ R) g (β v)) :
    ∃ β : W ≃+ (I → K), ∀ (g : G) (w : W), β (ρ g w) = R g *ᵥ β w := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  let Φ : W →+ (I → k) := β.toLinearMap.toAddMonoidHom.comp
    ((TensorProduct.mk E k ρ.asModule 1).toAddMonoidHom.comp
      ρ.asModuleEquiv.symm.toAddMonoidHom)
  have hΦ : ∀ w, Φ w = β ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w) := fun _ => rfl
  have hΦinj : Function.Injective Φ := β.injective.comp
    ((Module.FaithfullyFlat.tensorProduct_mk_injective (A := E) (B := k) ρ.asModule).comp
      ρ.asModuleEquiv.symm.injective)
  have : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hΦ0 : Φ ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hΦinj (by rw [h0, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]))
  let : Algebra K k := φ.toAlgebra
  let : DistribMulAction G W := DistribMulAction.compHom W ρ
  have hsmul : ∀ (g : G) (w : W), g • w = ρ g w := fun _ _ => rfl
  have hΦeq : ∀ (g : G) (w : W), Φ (g • w) = (R g).map (algebraMap K k) *ᵥ Φ w := by
    intro g w
    rw [hsmul, hΦ, hΦ]
    have hact : ρ.asModuleEquiv.symm (ρ g w) =
        CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w) := by
      rw [CFSG.endFieldRep_apply]
      exact congrArg (fun v => ρ.asModuleEquiv.symm (ρ g v))
        (ρ.asModuleEquiv.apply_symm_apply w).symm
    have hbc : (1 : k) ⊗ₜ[E] (CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w)) =
        CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g
          ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w) := by
      rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul]
    rw [hact, hbc, hβ, matRep_apply, matMap_apply, RingHom.algebraMap_toAlgebra]
  exact spCD_addEquiv_of_addHom (spCD_isIrreducibleAdd_of_isIrreducible ρ)
    (fun g => R g) hR Φ hΦ0 hΦeq

theorem exists_addEquiv_of_isCurtisType {G : Type*} [Group G] [Finite G] {B : Type*}
    {M : CoxeterMatrix B} {A : Type*} [Group A] {cs : CoxeterSystem M A}
    (D : CurtisDatum G cs 2) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible] {K I : Type*} [Field K] [Fintype I]
    [DecidableEq I] (R : G →* Matrix I I K)
    (hR : IsIrreducibleAdd (fun (g : G) (v : I → K) => R g *ᵥ v)) (k : Type*) [Field k]
    [CharP k 2] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k] (φ : K →+* k)
    (hRk : IsSimpleRep (matRep (matMap φ R)))
    {y₀ : k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule} {y : I → k}
    {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y₀ χ μ)
    (htR : D.IsCurtisType (matRep (matMap φ R)) y χ μ) :
    ∃ β : W ≃+ (I → K), ∀ (g : G) (w : W), β (ρ g w) = R g *ᵥ β w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleRep
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  obtain ⟨β, hβ⟩ := D.iso_of_isCurtisType hsimp hRk ht htR
  exact exists_addEquiv_of_extendScalars_equiv ρ R hR k φ β hβ

end CFSG.LocalAnalysis.WeakClosure81

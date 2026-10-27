module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6NatType
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix Module CFSG.Open CFSG.Quasithin.SmithCurtis
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.QuasithinUnique.Setup.X7 CFSG.LieType.SpecialLinear
open scoped Matrix TensorProduct

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Fintype K] [CharP K 2] in
private theorem exists_addEquiv_sp6_of_endFieldEquiv
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [ρ.IsIrreducible]
    (k : Type*) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule) k]
    [Algebra K k]
    (β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule)
      ≃ₗ[k] (Fin 3 ⊕ Fin 3 → k))
    (hβ : ∀ (g : StatedSp 3 K) v,
      β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
        (mat 3 K g).map (algebraMap K k) *ᵥ β v) :
    ∃ β : W ≃+ (Fin 3 ⊕ Fin 3 → K), ∀ (g : StatedSp 3 K) (w : W),
      β (ρ g w) = ((g : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ β w := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule
  let Φ : W →+ (Fin 3 ⊕ Fin 3 → k) := β.toLinearMap.toAddMonoidHom.comp
    ((TensorProduct.mk E k ρ.asModule 1).toAddMonoidHom.comp
      ρ.asModuleEquiv.symm.toAddMonoidHom)
  have hΦ : ∀ w, Φ w = β ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w) := fun _ => rfl
  let _ : DistribMulAction (StatedSp 3 K) W := DistribMulAction.compHom W ρ
  have hsmul : ∀ (g : StatedSp 3 K) (w : W), g • w = ρ g w := fun _ _ => rfl
  have hΦeq : ∀ (g : StatedSp 3 K) (w : W),
      Φ (g • w) = (mat 3 K g).map (algebraMap K k) *ᵥ Φ w := by
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
    rw [hact, hbc]
    exact hβ g ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w)
  have : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hΦ0 : Φ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    intro hzero
    have hinj : Function.Injective Φ := β.injective.comp
      ((Module.FaithfullyFlat.tensorProduct_mk_injective (A := E) (B := k) ρ.asModule).comp
        ρ.asModuleEquiv.symm.injective)
    have hww : Φ w = Φ 0 :=
      (congrArg (fun f : W →+ (Fin 3 ⊕ Fin 3 → k) => f w) hzero).trans
        (congrArg (fun f : W →+ (Fin 3 ⊕ Fin 3 → k) => f 0) hzero).symm
    exact hw (hinj hww)
  have hW : IsIrreducibleAdd (fun (g : StatedSp 3 K) (w : W) => g • w) := by
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
  have hN : IsIrreducibleAdd
      (fun (g : StatedSp 3 K) (v : Fin 3 ⊕ Fin 3 → K) => mat 3 K g *ᵥ v) := by
    intro A hA
    by_cases hbot : A = ⊥
    · exact Or.inl hbot
    right
    obtain h | ⟨v, hv, hv0⟩ := A.bot_or_exists_ne_zero
    · exact (hbot h).elim
    rw [eq_top_iff]
    intro w _
    by_cases hw : w = 0
    · rw [hw]
      exact A.zero_mem
    obtain ⟨g, hg, hgv⟩ := CFSG.ClassicalGroups.Symplectic.exists_statedSp_mulVec_eq hv0 hw
    have hmem := hA ⟨g, hg⟩ hv
    change (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v ∈ A at hmem
    rwa [hgv] at hmem
  obtain ⟨Ψ, hΨ, hΨeq⟩ := exists_addHom_of_extend (fun g => mat 3 K g) Φ hΦ0 hΦeq
  have hbij := bijective_of_ne_zero_of_irreducible (fun g => mat 3 K g) hW hN Ψ hΨ hΨeq
  refine ⟨AddEquiv.ofBijective Ψ hbij, fun g w => ?_⟩
  exact hΨeq g w


theorem exists_addEquiv_natural_of_isCurtisType {e : ℕ}
    (hK : Fintype.card K = 2 ^ e) (he : 3 ≤ e)
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [ρ.IsIrreducible]
    {y₀ : AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule)
      ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule}
    {χ : StatedSp 3 K →
      AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule)}
    (ht : (spCurtisDatum 3 K).IsCurtisType
      (CFSG.Theory.Representation.extendScalars
        (AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule))
        (CFSG.endFieldRep ρ)) y₀ χ 0)
    (φ : K →+*
      AlgebraicClosure (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule))
    (h0 : ∀ a : Kˣ, χ (corootSp 0 a) = φ a)
    (h1 : ∀ a : Kˣ, χ (corootSp 1 a) = 1)
    (h2 : ∀ a : Kˣ, χ (corootSp 2 a) = 1) :
    ∃ β : W ≃+ (Fin 3 ⊕ Fin 3 → K), ∀ (g : StatedSp 3 K) (w : W),
      β (ρ g w) = ((g : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ β w := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule
  let k := AlgebraicClosure E
  let _ : Algebra K k := φ.toAlgebra
  have : CharP k 2 := charP_of_injective_ringHom φ.injective 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfour : 4 ≤ Fintype.card K := by
    rw [hK]
    exact (show 4 ≤ 2 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by decide) he)
  have hχ : ∀ t : Fin 3 → Kˣ, χ (diagHom 3 K t) = φ (t 0) := by
    intro t
    rw [diagHom_three_eq]
    change χ (corootSp 0 (t 0) * corootSp 1 (t 0 * t 1) *
      corootSp 2 (t 0 * t 1 * t 2)) = φ (t 0)
    rw [ht.chi_mul (Subgroup.mul_mem _ (corootSp_mem_H 0 _) (corootSp_mem_H 1 _))
      (corootSp_mem_H 2 _), ht.chi_mul (corootSp_mem_H 0 _) (corootSp_mem_H 1 _),
      h0, h1, h2, mul_one, mul_one]
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  obtain ⟨β, hβ⟩ := (spCurtisDatum 3 K).iso_of_isCurtisType hsimp
    (isSimpleRep_sp_matMap (by decide) φ) ht (isCurtisType_sp6_matMap hfour φ χ hχ)
  exact exists_addEquiv_sp6_of_endFieldEquiv ρ k β hβ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

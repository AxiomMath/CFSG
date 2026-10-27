module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem inn_sup_compatParamAut_eq_range_twConj (σ : K ≃+* K) :
    (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range ⊔
      (RootCentExc.compatParamAut σ.toRingHom).range = (RecipeExcLang.twConj K σ).range := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, RecipeExcLang.twConj_of_mem_C0 σ c⟩
    · rintro _ ⟨b, rfl⟩
      refine ⟨⟨rootDiagUnit TwistTag.E6.tag (b : Fin 6 → Kˣ),
        RecipeExcLang.rootDiagUnit_mem_twInndiag (fun i => b.2 i)⟩, ?_⟩
      exact MulEquiv.ext fun h => Subtype.ext rfl
  · rintro _ ⟨⟨w, hw⟩, rfl⟩
    have hw' : w ∈ Subgroup.closure
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom : Set (ModGL TwistTag.E6.tag K)) ∪
          {w | ∃ b, RecipeExcLang.IsCompatE6 σ.toRingHom b ∧
            w = rootDiagUnit TwistTag.E6.tag b}) := hw
    induction hw' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hc | ⟨b, hb, rfl⟩
      · rw [show (⟨x, _⟩ : RecipeExcLang.twInndiagGroup K σ) =
          ⟨(⟨x, hc⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
            RecipeExcLang.graphFixedRootGroup_le_twInndiag σ hc⟩ from rfl,
          RecipeExcLang.twConj_of_mem_C0]
        exact Subgroup.mem_sup_left ⟨_, rfl⟩
      · refine Subgroup.mem_sup_right ⟨⟨b, fun i => hb i⟩, ?_⟩
        exact MulEquiv.ext fun h => Subtype.ext rfl
    | one =>
      rw [show (⟨1, _⟩ : RecipeExcLang.twInndiagGroup K σ) = 1 from rfl, map_one]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      rw [show (⟨x * y, _⟩ : RecipeExcLang.twInndiagGroup K σ) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl,
        map_mul]
      exact mul_mem (ihx hx) (ihy hy)
    | inv x hx ihx =>
      rw [show (⟨x⁻¹, _⟩ : RecipeExcLang.twInndiagGroup K σ) = (⟨x, hx⟩)⁻¹ from rfl, map_inv]
      exact inv_mem (ihx hx)

@[expose] noncomputable def frobQEquiv
    {f : ℕ} (hf : 1 ≤ f) :
    GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  RingEquiv.ofBijective (frobQ 2 f)
    (Function.Involutive.bijective (frobQ_frobQ 2 f hf))

theorem twInndiagAut_eq_range_twConj
    {f : ℕ} (hf : 1 ≤ f) :
    LayerSixE.twInndiagAut f = (RecipeExcLang.twConj _ (frobQEquiv hf)).range :=
  inn_sup_compatParamAut_eq_range_twConj (frobQEquiv hf)

end CFSG.StandardType

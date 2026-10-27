module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedLift
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial

theorem largeEvenMarking_twD3_inn {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {f : ℕ}
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 4 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ I = LargeEvenInnSet R) := by
  have hf : 1 ≤ f := hM.1.2.1
  have hlab : LargeEvenInLambda2 (⟨.twD, 3, f⟩ : LargeEvenLabel) := by
    refine ⟨hf, by norm_num⟩
  have hChev : GGChevStTag (⟨.twD, 3, f⟩ : LargeEvenLabel) := by
    simp [GGChevStTag]
  refine ⟨hX.1, ⟨.twD, 3, f⟩, hlab, ?_⟩
  have hraw : LargeEvenRawDatum (⟨.twD, 3, f⟩ : LargeEvenLabel) (fun R _ I _ =>
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ I = LargeEvenInnSet R) := by
    rw [LargeEvenRawDatum]
    obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := recipeUnitary_of_statedClassicalModel hM
    refine ⟨K, hF, hfin, hK, ⟨e⟩, ?_⟩
    apply le_antisymm
    · exact TableB.matConjImage_gu_subset_inn hK (coprime_two_pow_add_one_four hf)
    · refine innSet_subset_matConjImage (LargeEvenSUGroup (Fin 4) K (2 ^ f))
        (LargeEvenGUSet (Fin 4) K (2 ^ f)) (fun g hg => ?_)
      have hgu := (GGL45TG.SU.mem_su_iff (n := f) (d := 4)
        (TableBU.unitaryFieldData_of_card hK hf)).mp hg
      refine ⟨1, one_ne_zero, one_pow _, ?_⟩
      have hbar : (fun x : K => (TableBU.unitaryFieldData_of_card hK hf).bar x) =
          fun x : K => x ^ 2 ^ f := by
        funext x
        rw [UnitaryFieldData.bar_apply]
      simpa [hbar] using hgu.1
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hI⟩ := hRI
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨e.symm.isSimpleGroup, ?_, e, hChev, hI⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance
  exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩

end CFSG.StandardType

public section
namespace CFSG.StandardType

open CFSG.Assembly

theorem kgFieldRestrictionOn_twD_three :
    KGFieldRestrictionOn
      (fun p lab => lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ lab.n) := by
  intro p lab hp hp2 hlab ht3 hrow
  exact kgFieldRestrictionOn_unitaryLabel p lab hp hp2 hlab ht3
    (Or.inr ⟨hrow.1, hrow.2.1⟩)

end CFSG.StandardType

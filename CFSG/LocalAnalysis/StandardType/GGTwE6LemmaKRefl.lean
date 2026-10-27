module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKCheck
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylMat
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.R3
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open scoped Matrix

private def lemKTheta : Fin Tag.E6.rank → ℤ :=
  reflect Tag.E6 (e6Idx (1:Fin 6)) (reflect Tag.E6 (e6Idx (3:Fin 6)) (reflect Tag.E6 (e6Idx (4:Fin 6))
    (reflect Tag.E6 (e6Idx (5:Fin 6)) (reflect Tag.E6 (e6Idx (2:Fin 6)) (reflect Tag.E6 (e6Idx (3:Fin 6))
      (reflect Tag.E6 (e6Idx (4:Fin 6)) (reflect Tag.E6 (e6Idx (0:Fin 6)) (reflect Tag.E6 (e6Idx (2:Fin 6))
        (reflect Tag.E6 (e6Idx (3:Fin 6)) (Pi.single (e6Idx (1:Fin 6)) 1))))))))))

private theorem isRoot_lemKTheta : IsRoot Tag.E6 lemKTheta :=
  IsRoot.reflect (e6Idx (1:Fin 6)) (IsRoot.reflect (e6Idx (3:Fin 6)) (IsRoot.reflect (e6Idx (4:Fin 6))
    (IsRoot.reflect (e6Idx (5:Fin 6)) (IsRoot.reflect (e6Idx (2:Fin 6)) (IsRoot.reflect (e6Idx (3:Fin 6))
      (IsRoot.reflect (e6Idx (4:Fin 6)) (IsRoot.reflect (e6Idx (0:Fin 6)) (IsRoot.reflect (e6Idx (2:Fin 6))
        (IsRoot.reflect (e6Idx (3:Fin 6)) (IsRoot.basis (e6Idx (1:Fin 6))))))))))))

private theorem lemKTheta_apply (i : Fin 6) :
    lemKTheta (e6Idx i) = ([1, 2, 2, 3, 2, 1] : List ℤ).getD i.val 0 := by
  fin_cases i <;> decide

section Refl


theorem e6WeylMat_rootReflection {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    e6WeylMat (rootReflection β) = Matrix.of fun k j =>
      (if k = j then (1 : ZMod 3) else 0) -
        ((corootPair β (Pi.single (e6Idx k) 1) : ℤ) : ZMod 3) * ((β (e6Idx j) : ℤ) : ZMod 3) := by
  ext k j
  simp only [e6WeylMat_apply, e6WeylEntry, Matrix.of_apply]
  rw [rootReflection_inv hβ, rootReflection_smul hβ]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    e6Idx.injective.eq_iff]
  push_cast
  by_cases h : k = j
  · subst h; simp
  · have h' : ¬ j = k := fun e => h e.symm
    simp [h, h']

theorem lemKTab_spec : ∀ s ∈ lemKTab, ∃ a b : Fin Tag.E6.rank → ℤ,
    IsRoot Tag.E6 a ∧ IsRoot Tag.E6 b ∧
    (∀ i : Fin 6, a (e6Idx i) = s.1.getD i.val 0) ∧ (∀ i : Fin 6, b (e6Idx i) = s.2.1.getD i.val 0) ∧
    toMatL 3 6 s.2.2.1 = e6WeylMat (rootReflection a) ∧
    toMatL 3 6 s.2.2.2 = e6WeylMat (rootReflection b) := by
  intro s hs
  simp only [lemKTab, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · refine ⟨Pi.single (e6Idx 0) 1, Pi.single (e6Idx 2) 1,
      isRoot_single Tag.E6 (e6Idx 0), isRoot_single Tag.E6 (e6Idx 2), ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;> decide
    · rw [e6WeylMat_rootReflection (isRoot_single Tag.E6 (e6Idx 0))]
      ext k j; fin_cases k <;> fin_cases j <;> decide
    · rw [e6WeylMat_rootReflection (isRoot_single Tag.E6 (e6Idx 2))]
      ext k j; fin_cases k <;> fin_cases j <;> decide
  · refine ⟨Pi.single (e6Idx 4) 1, Pi.single (e6Idx 5) 1,
      isRoot_single Tag.E6 (e6Idx 4), isRoot_single Tag.E6 (e6Idx 5), ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i; fin_cases i <;> decide
    · rw [e6WeylMat_rootReflection (isRoot_single Tag.E6 (e6Idx 4))]
      ext k j; fin_cases k <;> fin_cases j <;> decide
    · rw [e6WeylMat_rootReflection (isRoot_single Tag.E6 (e6Idx 5))]
      ext k j; fin_cases k <;> fin_cases j <;> decide
  · refine ⟨lemKTheta, Pi.single (e6Idx 1) 1, isRoot_lemKTheta,
      isRoot_single Tag.E6 (e6Idx 1), ?_, ?_, ?_, ?_⟩
    · intro i; exact lemKTheta_apply i
    · intro i; fin_cases i <;> decide
    · rw [e6WeylMat_rootReflection isRoot_lemKTheta]
      ext k j; fin_cases k <;> fin_cases j <;> decide
    · rw [e6WeylMat_rootReflection (isRoot_single Tag.E6 (e6Idx 1))]
      ext k j; fin_cases k <;> fin_cases j <;> decide

end Refl

end CFSG.StandardType.TwE6LemmaK

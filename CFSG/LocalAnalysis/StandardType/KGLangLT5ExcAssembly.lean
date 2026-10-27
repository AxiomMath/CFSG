module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusDatum
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrame
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridge
public import CFSG.LocalAnalysis.StandardType.GGL45NtRecHolds
public import CFSG.LocalAnalysis.StandardType.GGL45NtSimp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
public import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcGlue
import CFSG.LocalAnalysis.StandardType.KGLangLT5ExcModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.C14Exc

private theorem kgLangExcAsmAux_not_triD4_three {p : ℕ} {lab : LargeEvenLabel}
    (h : GGL45FamNonTorsion p lab) : ¬ (lab.tag = .triD4 ∧ p = 3) := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [GGL45FamNonTorsion] at h ⊢
  exact h

theorem kgLangTorusDatumOn_of_excBridge
    {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGL45KGLabel p lab ∧ GGL45NtFamEx p lab)
    (hbr : GGL45NtOn S fun p lab => ExcBridgeCont p (AlgebraicClosure (ZMod 2)) lab.tag)
    (hcyc : GGRawPCyclicOn S) : KGLangTorusDatumOn S := by
  intro p lab hp hp2 hlab hSl
  obtain ⟨hkg, hfam⟩ := hS p lab hSl
  have hb : LargeEvenLabelAll lab (ExcBridgeCont p (AlgebraicClosure (ZMod 2)) lab.tag) :=
    hbr p hp hp2 lab hlab hkg hSl
  have hr : LargeEvenLabelAll lab (GGL45NtRec p) :=
    (ggL45NtRecOn_ex.antitone (fun p lab h => (hS p lab h).2)) p hp hp2 lab hlab hkg hSl
  have hsi : LargeEvenLabelAll lab GGL45NtSimp :=
    ggL45NtSimpOn_all S p hp hp2 lab hlab hkg hSl
  have hc : LargeEvenLabelAll lab (GGRawFieldConj p) :=
    ggRawFieldConjInputExc_holds p hp hp2 lab hlab
      (kgLangExcAsmAux_not_triD4_three hfam.1)
  have hy : LargeEvenLabelAll lab (GGRawPCyclic p) :=
    hcyc p hp hp2 lab hlab hSl
  exact (largeEvenLabelAll_and
      (largeEvenLabelAll_and
        (largeEvenLabelAll_and
          (largeEvenLabelAll_and hb hr) hsi) hc) hy).mono
    (fun R _ I F ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ =>
      kgLangTorusDatumCont_of_excBridge LieCore.ggLieToralPosition_holds
        LieCore.ggLieLangPosition_holds hp hp2 hfam.1 hfam.2.2 algClosure_zmod_isAlgebraic
        h1 h2 h3 h4 h5)

theorem kgLangTorusDatumOn_excUntw :
    KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧
      (lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) := by
  refine kgLangTorusDatumOn_of_excBridge
    (S := fun p lab => GGNbrLangRegExcLabel p lab ∧
      (lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8)) ?_ ?_ ?_
  · intro p lab h
    obtain ⟨tag, rank, n⟩ := lab
    refine kgLangExcLabel_fam h.1 ?_
    rintro rfl
    rcases h.2 with h | h | h | h | h <;> simp at h
  · exact ((excBridge_U (AlgebraicClosure (ZMod 2))).union
        (excBridge_E6 (AlgebraicClosure (ZMod 2)))).antitone (fun p lab h => by
      rcases h.2 with h | h | h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h))))
  · exact (ggRawPCyclicOn_excCyclic.or ggRawPCyclicOn_E6).mono (fun p lab h => by
      rcases h.2 with h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h)))))

theorem kgLangTorusDatumOn_excTw :
    KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧
      (lab.tag = .twE6 ∨ lab.tag = .triD4) := by
  refine kgLangTorusDatumOn_of_excBridge
    (S := fun p lab => GGNbrLangRegExcLabel p lab ∧ (lab.tag = .twE6 ∨ lab.tag = .triD4)) ?_ ?_ ?_
  · intro p lab h
    obtain ⟨tag, rank, n⟩ := lab
    refine kgLangExcLabel_fam h.1 ?_
    rintro rfl
    rcases h.2 with h | h <;> simp at h
  · exact ((excBridge_twE6 (AlgebraicClosure (ZMod 2))).union
        (excBridge_triD4 (AlgebraicClosure (ZMod 2)))).antitone (fun p lab h => by
      rcases h.2 with ht | ht
      · exact Or.inl ht
      · obtain ⟨-, hfamEx⟩ := kgLangExcLabel_fam h.1 (by rw [ht]; simp)
        exact Or.inr ⟨⟨hfamEx, Or.inl ht⟩, ht⟩)
  · exact (ggRawPCyclicOn_twE6.or ggRawPCyclicOn_excCyclic).mono (fun p lab h => by
      rcases h.2 with ht | ht
      · exact Or.inl ht
      · exact Or.inr (Or.inr (Or.inl ht)))

theorem kgLangTorusDatumOn_exc12 :
    KGLangTorusDatumOn fun p lab =>
      GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab ∧ lab.tag ≠ .twF4 := by
  intro p lab hp hp2 hlab hSX
  obtain ⟨hreg, -, htw⟩ := hSX
  have hreg0 : GGNbrLangRegExcLabel p lab := hreg
  rcases hreg with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩
  · exact kgLangTorusDatumOn_excUntw p lab hp hp2 hlab ⟨hreg0, Or.inl h⟩
  · exact kgLangTorusDatumOn_excTw p lab hp hp2 hlab ⟨hreg0, Or.inr h⟩
  · rcases h with h | h | h | h | h
    · exact kgLangTorusDatumOn_excUntw p lab hp hp2 hlab ⟨hreg0, Or.inr (Or.inl h)⟩
    · exact absurd h htw
    · exact kgLangTorusDatumOn_excUntw p lab hp hp2 hlab
        ⟨hreg0, Or.inr (Or.inr (Or.inl h))⟩
    · exact kgLangTorusDatumOn_excTw p lab hp hp2 hlab ⟨hreg0, Or.inl h⟩
    · exact kgLangTorusDatumOn_excUntw p lab hp hp2 hlab
        ⟨hreg0, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact kgLangTorusDatumOn_excUntw p lab hp hp2 hlab
      ⟨hreg0, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩

theorem kgLangTorusDatumOn_exc_of_twF4
    (hF : KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab ∧
        lab.tag = .twF4) :
    KGLangTorusDatumOn fun p lab => GGNbrLangRegExcLabel p lab ∧ GGNbrLangRest12Label p lab := by
  intro p lab hp hp2 hlab hS
  obtain ⟨hreg, h12⟩ := hS
  by_cases htw : lab.tag = .twF4
  · exact hF p lab hp hp2 hlab ⟨hreg, h12, htw⟩
  · exact kgLangTorusDatumOn_exc12 p lab hp hp2 hlab ⟨hreg, h12, htw⟩

end CFSG.StandardType

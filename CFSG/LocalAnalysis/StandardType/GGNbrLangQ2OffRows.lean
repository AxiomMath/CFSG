module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Lin
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Rows

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGBstarAbelianPreimageJLinResOffRowsInput (S : Q2RowKind → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
        (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        p ∣ d → p ∣ Nat.card K - 1 →
        (∀ kind, S kind →
          ¬ GGInnerDiagOnLab (fun p lab => q2RowFits kind p d (Nat.card K) lab) p Bs L) →
        IsMulCommutative
          ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K))

theorem ggBstarAbelianPreimageJLinResOffRowsInput_of_rows {S T : Q2RowKind → Prop}
    (hT : ∀ kind, T kind → ¬ S kind → Q2RowSolverInput kind)
    (h : GGBstarAbelianPreimageJLinResOffRowsInput T) :
    GGBstarAbelianPreimageJLinResOffRowsInput S := by
  classical
  intro G instG instFin p B Bs x L D J hcfg hInner hN d K instK instFinK θ hpd hpq hoff
  by_cases hex : ∃ kind, T kind ∧ ¬ S kind ∧
      GGInnerDiagOnLab (fun p lab => q2RowFits kind p d (Nat.card K) lab) p Bs L
  · obtain ⟨kind, hkT, hkS, hmark⟩ := hex
    exact hT kind hkT hkS G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hmark
  · refine h G p B Bs x L D J hcfg hInner hN d K θ hpd hpq ?_
    intro kind hkT hmark
    by_cases hkS : S kind
    · exact hoff kind hkS hmark
    · exact hex ⟨kind, hkT, hkS, hmark⟩

theorem ggBstarAbelianPreimageJLinResNotOrthogonalPlusInput_of_offRows
    (h : GGBstarAbelianPreimageJLinResOffRowsInput
      fun kind => kind = .orthogonalPlus ∨ kind = .linear ∨ kind = .fieldTwo) :
    GGBstarAbelianPreimageJLinResNotOrthogonalPlusInput := by
  classical
  intro G instG instFin p B Bs x L D J hcfg hInner hN d K instK instFinK θ hpd hpq hnotplus
  by_cases hlin : GGInnerDiagOnLab
      (fun p lab => q2RowFits .linear p d (Nat.card K) lab) p Bs L
  · exact q2RowSolver_linear_holds G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hlin
  by_cases hf2 : GGInnerDiagOnLab
      (fun p lab => q2RowFits .fieldTwo p d (Nat.card K) lab) p Bs L
  · exact q2RowSolver_fieldTwo_holds G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hf2
  refine h G p B Bs x L D J hcfg hInner hN d K θ hpd hpq ?_
  intro kind hkind
  rcases hkind with rfl | rfl | rfl
  · exact hnotplus
  · exact hlin
  · exact hf2

end CFSG.StandardType

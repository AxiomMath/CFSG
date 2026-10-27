module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSzLowK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagPSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagU4U5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagG2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiag3D4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiag2F4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagSp6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagCovers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagProducts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup


theorem kDiag_of_omega8m_case
    (hΩ : ∀ {n : ℕ} {X : Type} [Group X] [Finite X], IsOmega8m X n →
      ∀ (θ : MulAut X), Odd (orderOf θ) →
      ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∀ (P : Subgroup X), IsParabolicTwo X P →
        (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) → ∀ x ∈ P, θ x ∈ P) :
    KDiag := by
  intro X _instX _finX hshape θ hodd S hSθ P hP hSP x hx
  rcases hshape with
      ⟨n, _hn, hsingle⟩ | hU4two | hU5two | hOm8two | h3D4two | h3D4one |
        ⟨n, _hn, hprod⟩ | hSq
  ·
    rcases hsingle with
        hSz | hL2 | hL3 | hU3 | hPSL4 | hU4 | hG2 | h3D4 | hF4 | hSp4 | hSL3 | hSU3 |
          hPSp6 | hOm8
    · exact kDiag_of_isSz hSz θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isL2 hL2 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isL3 hL3 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isU3 hU3 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_lieModel_psl4 hPSL4 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_lieModel_psu4 hU4 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isG2 hG2 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_is3D4 h3D4 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_lieModel_twistedF4 hF4 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isSp4 hSp4 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isSL3 hSL3 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_isSU3 hSU3 θ hodd S hSθ P hP hSP x hx
    · exact kDiag_of_lieModel_psp6 hPSp6 θ hodd S hSθ P hP hSP x hx
    · exact hΩ hOm8 θ hodd S hSθ P hP hSP x hx
  · exact kDiag_of_lieModel_psu4 hU4two θ hodd S hSθ P hP hSP x hx
  · exact kDiag_of_lieModel_psu5 hU5two θ hodd S hSθ P hP hSP x hx
  · exact hΩ hOm8two θ hodd S hSθ P hP hSP x hx
  · exact kDiag_of_is3D4 h3D4two θ hodd S hSθ P hP hSP x hx
  · exact kDiag_of_is3D4 h3D4one θ hodd S hSθ P hP hSP x hx
  · exact kDiag_of_isSzL2Product hprod θ hodd S hSθ P hP hSP x hx
  · exact kDiag_of_isSU3CentralSquare hSq θ hodd S hSθ P hP hSP x hx

theorem kDiag_of_omega8m
    (hΩ : ∀ {n : ℕ} {X : Type} [Group X] [Finite X], IsOmega8m X n →
      ∀ (θ : MulAut X), Odd (orderOf θ) →
      ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∀ (P : Subgroup X), IsParabolicTwo X P →
        (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) → ∀ x ∈ P, θ x ∈ P) :
    KDiag :=
  kDiag_of_omega8m_case hΩ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

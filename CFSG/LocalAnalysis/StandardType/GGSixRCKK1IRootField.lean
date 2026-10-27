module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLineChev
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLinePSL2All
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLinePSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLineOmM
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLineTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaH

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)
open CFSG.StandardType.RCKC1

theorem rckK1I_rootField_ggU
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f) :
    ∃ β : Fin (ggU t n f).D.rank → ℤ, β ∈ (ggU t n f).D.roots ∧ GGLongRoot (ggU t n f).D β ∧
      ∃ (Fq : Type) (_ : Field Fq) (_ : Finite Fq) (ε : Multiplicative Fq ≃* (ggU t n f).D.rootGroup β),
        Nat.card Fq = 2 ^ f ∧ RCKRootFieldExact ((ggU t n f).D.rootGroup β) Fq ε := by
  have hline : RCKRootLineAt (ggU t n f) f := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hn : 3 ≤ n
      · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inl ⟨rfl, hn⟩) hadm)
      · obtain rfl : n = 2 := by have := hadm.2.2.1; omega
        exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLineAll_PSL2 hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_PSU hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inr (Or.inl rfl)) hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inl rfl))) hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_POmegaMinus hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_chev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hadm)
    · exact (fun h => rckRootLineAt_of_all h.2 h.1) (rckK1I_rootLine_twistedE6 hadm)
  obtain ⟨β, hβ, hlong, Fq, _, _, ε, hcard, hsc⟩ := hline
  exact ⟨β, hβ, hlong, Fq, inferInstance, inferInstance, ε, hcard,
    rckRootFieldExact_of_scalars hsc (rck_lemmaH_long.1 t n f β ht hadm.2.1 hlong)⟩


end CFSG.StandardType.RCKK1I

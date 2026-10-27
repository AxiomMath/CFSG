module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactCore

public section

open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.RankThree.PartTwo.Sec19 CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem sl3_plane_closure_linear {k : Type} [Field k] [Finite k] (h4 : 4 ≤ Nat.card k)
    (h3 : 3 ∣ Nat.card k - 1) (E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) k)))
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    (hout : ¬ E ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) k →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) k)).range)
    (hconj : ∀ e ∈ E, ∃ g : Matrix.GeneralLinearGroup (Fin 3) k, IsConjBy e g) :
    Subgroup.closure (fixSet E) = ⊤ := by
  by_cases hF : FixCube E
  · exact closure_fixSet_eq_top_linear h3 E hE hcard hF
  · unfold FixCube at hF
    push Not at hF
    obtain ⟨e, he, s, hs3, hsE, hes⟩ := hF
    exact Item19Res5Proof.closure_fixSet_sl_of_conj_outer h4 E hE hcard hout hconj
      ⟨e, he, s, hs3, hsE, hes⟩

theorem su3_plane_closure_unitary
    {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq3 : p ^ f % 3 = 2) (hq : 2 < p ^ f)
    (E : Subgroup (MulAut (unitarySU p f F 3))) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    (hout : ¬ E ≤ (MulAut.conj : unitarySU p f F 3 →* MulAut (unitarySU p f F 3)).range)
    (hdiag : E ≤ (CFSG.RankThree.PartTwo.KFacts.suConj h).range) :
    Subgroup.closure (fixSet E) = ⊤ := by
  by_cases hF : FixCube E
  · exact closure_fixSet_eq_top_unitary_of_conj h (Nat.dvd_of_mod_eq_zero (by omega)) hq E hE hcard
      hF (fun e he => by
        obtain ⟨B, hB⟩ := hdiag he
        exact ⟨B, hB.symm⟩)
  · unfold FixCube at hF
    push Not at hF
    obtain ⟨e, he, s, hs3, hsE, hes⟩ := hF
    exact seitz199OuterUnitaryDiag_holds p f F h hq3 hq E (fun φ hφ => hE.2 φ hφ) hcard hout
      ⟨e, he, s, hs3, hsE, hes⟩ hdiag

end CFSG.RankThree.PartTwo.Sec4.E27

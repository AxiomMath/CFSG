module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairAB

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec19

section Facts


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem D4Par.two_le_of_four_le_card_fix (P : D4Par n X σ) (h : 4 ≤ Nat.card (fixSubfield σ)) :
    2 ≤ n := by
  by_contra hlt
  have hn1 : n = 1 := by have := P.one_le; omega
  rw [P.card_fix, hn1] at h
  omega

theorem trialityABFacts_of_par (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) : TrialityABFacts σ where
  inf_bot := Asub_inf_Bsub P
  max := ab_maximal hgold P hn
  tau3 := tauAut_pow_three P
  tau_A := fun a ha => tau_mem_Asub P ha
  tau_B := fun b hb => show tauAut σ b = b from Bsub_le_Gsub P hb
  sl2A := by
    refine ⟨(asubEquiv P).symm, fun a ha => ?_⟩
    obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) X, asubEquiv P g = ⟨a, ha⟩ :=
      (asubEquiv P).surjective _
    have hga : iotaA P g = a := congrArg Subtype.val hg
    have h1 : (⟨tauAut σ a, tau_mem_Asub P ha⟩ : Asub σ) =
        asubEquiv P (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
      apply Subtype.ext
      show tauAut σ a = iotaA P (Matrix.SpecialLinearGroup.map σ.toRingHom g)
      rw [← hga, tau_iotaA P g]
    rw [h1, ← hg, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    rfl
  sl2B := ⟨(bsubEquiv P).symm⟩

theorem trialityR1Facts_of_par (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) :
    TrialityR1Facts σ where
  Eb := fun h4 a b ha hb ha3 hb3 ha1 hb1 =>
    planeGen_Eb hgold P (P.two_le_of_four_le_card_fix h4) ha hb ha3 hb3 ha1 hb1
  N4 := fun h4 b hb hb3 hb1 =>
    planeGen_N4 hgold P (P.two_le_of_four_le_card_fix h4) hb hb3 hb1
  N3 := fun h4 a ha ha3 ha1 =>
    planeGen_N3 hgold P (P.two_le_of_four_le_card_fix h4) ha ha3 ha1
  Nreg := fun h4 a b ha hb ha3 hb3 ha1 hb1 =>
    planeGen_Nreg hgold P (P.two_le_of_four_le_card_fix h4) ha hb ha3 hb3 ha1 hb1

end Facts

end CFSG.RankThree.PartTwo.Sec19

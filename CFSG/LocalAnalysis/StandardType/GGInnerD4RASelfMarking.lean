module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAMarking
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

private lemma ltrra1_center_eq_bot {R : Type} [Group R] [IsSimpleGroup R]
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by
      rw [h]
      exact Subgroup.mem_top a
    have hba : b * a = a * b := (Subgroup.mem_center_iff.mp ha) b
    exact hab hba.symm

private lemma ltrra1_commutator_eq_top {R : Type} [Group R] [IsSimpleGroup R]
    (hna : ∃ a b : R, a * b ≠ b * a) : commutator R = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    letI : Bracket R R := commutatorElement
    have hmem : ⁅a, b⁆ ∈ commutator R :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h] at hmem
    have h1 : ⁅a, b⁆ = 1 := Subgroup.mem_bot.mp hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · exact h

private lemma ltrra1_induces_quotCenter_ofBot {R : Type} [Group R]
    (hcen : Subgroup.center R = ⊥) (β : MulAut R) :
    LargeEvenInduces (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen)
      (fun s s' => s' = β s) β := by
  intro s s' hs
  subst hs
  simp [CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]

theorem raModelSelfMarking_holds : S2MathAs51600RAMarking.RAModelSelfMarking := by
  intro lab hlab htag Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  rcases htag with hA | hA
  · subst hA
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfK, hfinK, hcard, hQK⟩ := hQ
    refine ⟨K, hfK, hfinK, hcard, hQK, ?_⟩
    rintro hR hna β hβ
    haveI := hR
    dsimp only [CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind,
      CFSG.Assembly.LargeEvenMarking]
    refine ⟨ltrra1_commutator_eq_top hna, ⟨⟨.A, rank, n⟩, hlab, ?_⟩⟩
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    refine ⟨K, hfK, hfinK, hcard, hR, hna,
      CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot
        (ltrra1_center_eq_bot hna), rfl, β, hβ, ?_⟩
    exact ltrra1_induces_quotCenter_ofBot (ltrra1_center_eq_bot hna) β
  · subst hA
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hfK, hfinK, hcard, hQK⟩ := hQ
    refine ⟨K, hfK, hfinK, hcard, hQK, ?_⟩
    rintro hR hna β hβ
    haveI := hR
    dsimp only [CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind,
      CFSG.Assembly.LargeEvenMarking]
    refine ⟨ltrra1_commutator_eq_top hna, ⟨⟨.twA, rank, n⟩, hlab, ?_⟩⟩
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    refine ⟨K, hfK, hfinK, hcard, hR, hna,
      CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot
        (ltrra1_center_eq_bot hna), rfl, β, hβ, ?_⟩
    exact ltrra1_induces_quotCenter_ofBot (ltrra1_center_eq_bot hna) β

end CFSG.StandardType.GGInnerD4RAParts

end

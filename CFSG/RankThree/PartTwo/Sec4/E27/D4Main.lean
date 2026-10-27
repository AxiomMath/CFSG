module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4TypeII

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Main

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem seitz27_C0_layer (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ) (hn : 2 ≤ n)
    (hA : StepALayer σ) : Seitz27 (C0 σ) := by
  intro E hE hcard
  by_cases hG : ∃ φ : MulAut (C0 σ), tauAut σ ∈ E.map (MulAut.congr φ).toMonoidHom
  · obtain ⟨φ, hφ⟩ := hG
    exact typeI_of_conj_tau hgold P hn hE hcard φ hφ
  · push Not at hG
    exact typeII_seitzHyperGamma_layer hgold P hn hA hE hcard hG

@[expose] def StepALayerAll : Prop :=
  ∀ (n : ℕ) (X : Type) [Field X] [Finite X] (σ : X ≃+* X), D4Par n X σ → 2 ≤ n → StepALayer σ

theorem seitz27_trialityD4_layer (hgold : CFSG.Goldschmidt.TopStatement) (hA : StepALayerAll) :
    ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      2 ≤ q.exponent → ∀ (Y : Type) [Group Y] [Finite Y],
        Nonempty (Y ≃* Cat ⟨TauCeti.LieTypeIndex.trialityD4 q, hq⟩) → Seitz27 Y := by
  intro q hq hqp hqe Y _ _ ⟨eY⟩
  obtain ⟨X', hF, hfin, σ, hcard, hσ, -, ⟨e⟩⟩ :=
    exists_trialityD4_model (K := Cat ⟨TauCeti.LieTypeIndex.trialityD4 q, hq⟩) hqp
      ⟨hq, ⟨MulEquiv.refl _⟩⟩
  have P : D4Par q.exponent X' σ := ⟨q.exponent_pos, hcard, hσ⟩
  exact seitz27_of_mulEquiv (eY.trans e)
    (seitz27_C0_layer hgold P hqe (hA q.exponent X' σ P hqe))

theorem seitz27_trialityD4_layer_of_stepA (hA : StepALayerAll) :
    ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      2 ≤ q.exponent → ∀ (Y : Type) [Group Y] [Finite Y],
        Nonempty (Y ≃* Cat ⟨TauCeti.LieTypeIndex.trialityD4 q, hq⟩) → Seitz27 Y :=
  seitz27_trialityD4_layer CFSG.Goldschmidt.topStatement hA

end Main

end CFSG.RankThree.PartTwo.Sec4.E27

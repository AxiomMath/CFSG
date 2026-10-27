module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s16k_hat_of_tripleA6 {Q : Type} [CommGroup Q] {L' : Subgroup (MulAut Q)}
    (h : TripleA6Six L' ⊤ ⊥) :
    IsHat ↥L' ↥(alternatingGroup (Fin 6)) ∧ Nat.card Q = 2 ^ 6 := by
  obtain ⟨K, hK, hKf, Γ₀, hK4, -, hhat, -, hreal⟩ := h
  obtain ⟨π, hπ⟩ := hreal
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful Γ₀) hπ
  have hL : IsHat ↥L' ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩) hhat
  refine ⟨hL, ?_⟩
  obtain ⟨e, -⟩ := B5.exists_linModel hπ
  have h1 : Nat.card ↥(⊤ : Subgroup Q) = Nat.card (Multiplicative (Fin 3 → K)) :=
    Nat.card_congr e.toEquiv
  rw [Subgroup.card_top] at h1
  rw [h1]
  change Nat.card (Fin 3 → K) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_fin, hK4]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

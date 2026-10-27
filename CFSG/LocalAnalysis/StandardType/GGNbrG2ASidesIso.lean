module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ASidesDefs
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossLin
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHighWit

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggInnDiagPSL3_transport {Q : ℕ} (h3 : 3 ∣ Q - 1) {X : Type} [Group X] {α : MulAut X}
    (h : GGInnDiagPSL3 Q X α) {K : Type} [Field K] [Finite K] (hK : Nat.card K = Q)
    (e : X ≃* projectiveSL 3 K) : MulAut.congr e α ∈ linearAutGroup 3 K := by
  obtain ⟨K₁, _, _, e₁, hK₁, hD₁⟩ := h
  have hmem := CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.congr_mem_linearAutGroup
    (hK ▸ h3) (hK₁ ▸ h3) (e₁.symm.trans e) hD₁
  have hEq : MulAut.congr (e₁.symm.trans e) (MulAut.congr e₁ α) = MulAut.congr e α := by
    ext y
    simp [MulAut.congr_apply]
  rwa [hEq] at hmem

theorem ggInnDiagPSL3_iff {Q : ℕ} (h3 : 3 ∣ Q - 1) {X : Type} [Group X] {α : MulAut X}
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Q) (e : X ≃* projectiveSL 3 K) :
    GGInnDiagPSL3 Q X α ↔ MulAut.congr e α ∈ linearAutGroup 3 K :=
  ⟨fun h => ggInnDiagPSL3_transport h3 h hK e, fun h => ⟨K, inferInstance, inferInstance, e, hK, h⟩⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType

theorem spInnerDiagData_holds : SpInnerDiagData := by
  intro G _ _ H E m h
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hS, _, _⟩ := hQ
  change lab = planeAmbientLabel .symplectic m at hS
  subst lab
  simp only [LargeEvenRawDatum, planeAmbientLabel] at hraw
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨-, -, θ, -, hEN, hInd⟩ := hQK
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hlab' : LargeEvenInLambda2 (⟨.C, m, 1⟩ : LargeEvenLabel) := by
    simpa [planeAmbientLabel] using hlab
  have h2m : 2 ≤ m := by simpa [LargeEvenInLambda2] using hlab'.2.1
  haveI : NeZero m := ⟨by omega⟩
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    apply charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
    simpa [Nat.card_eq_fintype_card] using hK2
  have hmem : ∀ (b : G) (hb : b ∈ E),
      ggLAut H θ ⟨b, hEN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
    intro b hb
    exact ggLAut_mem_of_induces H θ hEN hInd hb
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, hK2, hperf, θ, hEN, hmem⟩

end CFSG.StandardType.GGQ2Frame.SpPlacement

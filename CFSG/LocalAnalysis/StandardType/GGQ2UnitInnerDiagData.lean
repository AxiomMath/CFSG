module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag

theorem unitInnerDiagData_holds : UnitInnerDiagData := by
  intro G _ _ H E N h
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hS, _, _⟩ := hQ
  change lab = ⟨.twA, N - 1, 1⟩ at hS
  subst lab
  have hN : 4 ≤ N := by
    have h2 : LargeEvenInLambda2 (⟨.twA, N - 1, 1⟩ : LargeEvenLabel) := hlab
    simp only [LargeEvenInLambda2] at h2
    omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only at hraw
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨-, -, θ, -, hEN, hInd⟩ := hQK
  have hK4 : Nat.card K = 4 := by simpa using hK
  have hmem : ∀ (b : G) (hb : b ∈ E),
      ggLAut H θ ⟨b, hEN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K (n + 1)))
          (LargeEvenGUSet (Fin (n + 1)) K (2 ^ 1)) := by
    intro b hb
    exact ggLAut_mem_of_induces H θ hEN hInd hb
  exact ⟨K, inferInstance, inferInstance, hK4, hN, hperf, θ, hEN, hmem⟩

end CFSG.StandardType.GGQ2Frame.UnitPlacement

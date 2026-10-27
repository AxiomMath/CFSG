module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType

theorem linInnerDiagData_holds : LinInnerDiagData := by
  intro G _ _ H E r h
  obtain ⟨hperf, lab, -, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hS, _, _⟩ := hQ
  change lab = ⟨.A, r, 1⟩ at hS
  subst lab
  simp only at hraw
  obtain ⟨K, _, _, hK, hQK⟩ := hraw
  obtain ⟨-, -, θ, -, hEN, hInd⟩ := hQK
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    apply charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
    simpa [Nat.card_eq_fintype_card] using hK2
  have hmem : ∀ (b : G) (hb : b ∈ E),
      ggLAut H θ ⟨b, hEN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) K)) Set.univ := by
    intro b hb
    exact ggLAut_mem_of_induces H θ hEN hInd hb
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK2, hperf, θ, hEN, hmem⟩

end CFSG.StandardType.GGQ2Frame.LinPlacement

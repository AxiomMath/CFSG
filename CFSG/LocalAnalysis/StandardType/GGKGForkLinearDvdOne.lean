module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvd
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem ggKGTo_recipeLinear_rootSL2_dvd {d N p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : p ∣ d)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hd5 : 5 ≤ d := le_trans hp5 (Nat.le_of_dvd (by omega) hpd)
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hsec : SLHasSections d K := slHasSections_of_four_le hp hpK (by omega)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  exact ⟨d - 2, ggTorusLift_of_mulEquiv (recipeEquiv d K)
      (ggTorusLift_sub_two hp hpK hd hsec),
    ggKGOn_torusRootSL2_of_mulEquiv (recipeEquiv d K) hI
      (ggTorusRootSL2_psl_dvd hp hp2 hpK hd5 h4)⟩

end TypeA

theorem ggKGOneOn_typeADvd : GGKGOneOn fun p lab => GGTypeALabelDvd p lab := by
  intro p lab hp hlab hl hdvd Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨h, hpn, hpl⟩ := hdvd
  dsimp only at h hpn hpl
  subst h
  have hl1 : 1 ≤ l := hlab.2.1
  exact TypeA.ggKGTo_recipeLinear_rootSL2_dvd hp hl.1 hpn ⟨n, rfl⟩ (by omega) hpl hQ

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGKGForkUnitaryOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdOne
public import CFSG.LocalAnalysis.StandardType.GGKGForkSmallRow
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRealKGThreeRow_uNonsplit :
    GGRealKGThreeRow .uNonsplit := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn, hpl⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hpl
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hn2 : 2 ≤ n := hl.2.1
  have hl2 : 2 ≤ l := hlab.2.1
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  exact ⟨0, TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := l + 1) (by omega)),
    ggTorusRootSL2_psu_coprime (d := l + 1) hK hn2 (by omega) hp hpn hpl⟩

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem recipeLinear_rootSL2_dvd_three {d N : ℕ} (hpN : 3 ∣ N - 1) (hN : ∃ m, N = 2 ^ m)
    (hd5 : 5 ≤ d) {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGTorusRootSL2 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hpK : 3 ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hsec : SLHasSections d K := slHasSections_of_four_le hp hpK (by omega)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  exact ⟨d - 2, ggTorusLift_of_mulEquiv (recipeEquiv d K)
      (ggTorusLift_sub_two hp hpK (by omega) hsec),
    ggKGOn_torusRootSL2_of_mulEquiv (recipeEquiv d K) hI
      (ggTorusRootSL2_psl_dvd hp (by norm_num) hpK hd5 h4)⟩

end TypeA

theorem ggRealRootSL2On_three_A2 :
    GGRealRootSL2On fun p lab => p = 3 ∧ lab.tag = .A ∧ lab.rank = 2 := by
  intro p lab hp _ _ hs Q hQ
  obtain ⟨hp3, htag, hl⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl
  subst htag hl
  obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
    largeEvenLabelAll_card_lt_A2_all (lab := ⟨.A, 2, n⟩) hp (by norm_num) rfl rfl Q hQ
  have := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQ', 0,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num))), ?_⟩
  intro L' _ _ ψ A hA
  exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim

theorem ggRealKGThreeRow_aSplitDvd : GGRealKGThreeRow .aSplitDvd := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, hpn, hpl⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hpl
  subst htag
  have hl1 : 1 ≤ l := hlab.2.1
  rcases (show l = 2 ∨ 5 ≤ l by omega) with rfl | hl5
  · exact ggRealRootSL2On_three_A2 3 _ hp hlab hl ⟨rfl, rfl, rfl⟩
  intro Q hQ
  exact TypeA.recipeLinear_rootSL2_dvd_three hpn ⟨n, rfl⟩ (show 5 ≤ l + 1 by omega) hQ

end CFSG.StandardType

end

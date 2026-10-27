module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdLat
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearDvdModel
public import CFSG.LocalAnalysis.StandardType.GGKGForkLinearRow
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeADvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorusLattice_psl_sub_two {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hpd : p ∣ d) (hd : 5 ≤ d) :
    GGTorusLattice p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup hp hpK (by omega) le_rfl
      ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩
  obtain ⟨S, Θ, hS, hΘ, hker', hperm⟩ :=
    ggKGTAD_permModel hp hp2 hpK hd hφ's hφ'ker hAe hr hsc hdiag
  exact ggKGTAD_lattice hp hp2 hpd hd hS Θ hΘ hker' hperm

private theorem ggKGTg_recipeLinear_lattice_dvd {d N p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : p ∣ d)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I := by
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
  have hsec : SLHasSections d K := slHasSections_of_four_le hp hpK (by omega)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  exact ⟨d - 2, ggTorusLift_of_mulEquiv (recipeEquiv d K)
      (ggTorusLift_sub_two hp hpK hd hsec),
    ggTorusLattice_of_mulEquiv (recipeEquiv d K) hI
      (ggTorusLattice_psl_sub_two hp hp2 hpK hpd hd5)⟩

end TypeA

theorem ggKGTwoOn_typeADvd : GGKGTwoOn fun p lab => GGTypeALabelDvd p lab := by
  intro p lab hp hlab hl hdvd
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨h, hpn, hpl⟩ := hdvd
  dsimp only at h hpn hpl
  subst h
  intro Q hQ
  have hl1 : 1 ≤ l := hlab.2.1
  exact TypeA.ggKGTg_recipeLinear_lattice_dvd hp hl.1 hpn ⟨n, rfl⟩ (by omega) hpl hQ

end CFSG.StandardType

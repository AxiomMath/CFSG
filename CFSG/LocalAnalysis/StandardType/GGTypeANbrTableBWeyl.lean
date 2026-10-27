module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBWeylOn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

theorem ggTorusReflGenW_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    GGTorusReflGenW p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ A hA
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Fintype.ofFinite K
    have h0 : ((Fintype.card K : ℕ) : K) = 0 := by simp
    have h2 : 2 ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp h0
    have h1 : 0 < Nat.card K := Nat.card_pos
    omega
  obtain ⟨φ', hφ's, hφ'ker, hdiag⟩ :=
    exists_actsDiag_model_of_tbGroup hp hpK hd le_rfl hA
  exact TypeANbrDvd.ggAutomizer_le_closure_reflSet_of_model hp hp2 hpK (by omega) hφ's hφ'ker
    hA.2.2.2.1 hA.2.2.2.2.2.2.2 hdiag

theorem ggTorusReflGenW_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusReflGenW p r R' I') :
    GGTorusReflGenW p r R I := by
  intro L' _ _ ψ A hA
  exact h L' (e.toMonoidHom.comp ψ) A (hA.mulEquiv e hI)

theorem recipeLinear_reflGenW {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I := by
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
  have hp2 : p ≠ 2 := TypeA.prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (TypeA.recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    TypeA.congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL hd)),
      ggTorusReflGenW_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (fun L' _ _ ψ A hA =>
          absurd hA (not_ggTorusTBGroup_small hp hp2 hpK (by omega) hd3))⟩
  · exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_sub_two hp hpK (by omega) (slHasSections_of_four_le hp hpK hd4)),
      ggTorusReflGenW_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (ggTorusReflGenW_PSL hp hpK hd4)⟩

theorem ggNbrTableBWeylInputOn_typeA_holds :
    GGNbrTableBWeylInputOn fun _ lab => lab.tag = .A := by
  rintro p hp - ⟨tag, n, f⟩ hlab htag - hsp Q hQ
  dsimp only at htag
  subst htag
  have hl1 : 1 ≤ n := hlab.2.1
  exact recipeLinear_reflGenW (d := n + 1) (N := 2 ^ f) hp hsp.2.2 ⟨f, rfl⟩ (by omega) hQ

end CFSG.StandardType

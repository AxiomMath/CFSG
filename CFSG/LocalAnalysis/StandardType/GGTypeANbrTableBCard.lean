module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBAutCard
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification TypeA

theorem ggTorusAutCardSCr_PSL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) :
    GGTorusAutCardSCr p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) d.factorial := by
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
  exact TypeANbrDvd.card_ggAutomizer_eq_factorial_of_model hp hp2 hpK hd hφ's hφ'ker
    hA.2.2.2.1 hA.2.2.2.2.2.2.2 hdiag

theorem ggTorusAutCardSC_PSL_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) :
    GGTorusAutCardSC 3 (projectiveSL 4 K) (Set.range (conjAut 4 K)) 3 24 := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h27 hsc
  refine ⟨h27, ?_⟩
  have h9 : 3 ^ (4 - 2) ≤ Nat.card A := by
    have h27' := h27
    norm_num at h27' ⊢
    omega
  exact ggTorusAutCardSCr_PSL (d := 4) (p := 3) (K := K) (by norm_num) h3 (by norm_num)
    L' ψ A ⟨hψ, hker, hperf, hA, hAI, h9, h27, hsc⟩

theorem ggTorusAutNotDvdSCJ_PSL_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K - 1) (labJ : LargeEvenLabel) :
    GGTorusAutNotDvdSCJ 3 labJ (projectiveSL 4 K) (Set.range (conjAut 4 K)) 3 9 := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h27 hle hsc he
  obtain ⟨-, hcard⟩ :=
    ggTorusAutCardSC_PSL_four (K := K) h3 L' ψ hψ hker hperf A hA hAI h27 hsc
  rw [hcard]
  norm_num

theorem ggTorusAutNotDvdSCJ_of_mulEquiv {p rmax bad : ℕ} {labJ : LargeEvenLabel}
    {R R' : Type} [Group R] [Group R'] {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusAutNotDvdSCJ p labJ R' I' rmax bad) :
    GGTorusAutNotDvdSCJ p labJ R I rmax bad := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hle hsc he
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ h3 hle hsc he
  · exact (TypeA.ker_comp_mulEquiv e ψ).symm ▸ hker
  · intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφI, fun l => ?_⟩
    change e (φ (e.symm (e (ψ l)))) = e (ψ (a l))
    rw [MulEquiv.symm_apply_apply, hφ]

theorem ggPumpLineAutKnown_A3_split_label {f : ℕ} (h3 : 3 ∣ 2 ^ f - 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.A, 3, f⟩ fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I 3 9 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hQ
  have h3K : 3 ∣ Nat.card K - 1 := by rw [hKcard]; exact h3
  have hchar : CharP K 2 := charP_two_of_card hKcard
  refine ⟨K, hKfield, hKfinite, hKcard, hQ, ?_⟩
  exact ggTorusAutNotDvdSCJ_of_mulEquiv (TypeA.recipeEquiv 4 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (ggTorusAutNotDvdSCJ_PSL_four (K := K) h3K labJ)

theorem recipeLinear_autCard {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusAutCardSCr p r R I d.factorial := by
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
      ggTorusAutCardSCr_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (fun L' _ _ ψ A hA =>
          absurd hA (not_ggTorusTBGroup_small hp hp2 hpK (by omega) hd3))⟩
  · exact ⟨d - 2, TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
        (TypeA.ggTorusLift_sub_two hp hpK (by omega) (slHasSections_of_four_le hp hpK hd4)),
      ggTorusAutCardSCr_of_mulEquiv (TypeA.recipeEquiv d K) hI
        (ggTorusAutCardSCr_PSL hp hpK hd4)⟩

theorem ggNbrTableBCardInput_holds : GGNbrTableBCardInput := by
  intro p hp hp2 n f hlab hpf Q hQ
  have hl1 : 1 ≤ n := hlab.2.1
  have hd' : 2 ≤ n + 1 := by omega
  exact recipeLinear_autCard (d := n + 1) (N := 2 ^ f) hp hpf ⟨f, rfl⟩ hd' hQ

end CFSG.StandardType

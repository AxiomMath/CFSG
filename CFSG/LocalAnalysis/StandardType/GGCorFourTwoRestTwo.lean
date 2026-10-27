module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRest
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThree
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CorFourTwoTwo

open TableB TypeA TwoThree CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem odd_orderOf_of_pow_three {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) :
    Odd (orderOf g) := by
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2 <;> rw [h2] <;> decide

theorem mem_range_conjAut_of_odd_two {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hd : 3 ≤ d) {φ : MulAut (projectiveSL d K)}
    (hφ : Odd (orderOf φ)) : φ ∈ Set.range (conjAut d K) := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp
    (CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      hd hφ)
  have hσ : σ = 1 := by
    ext x
    rcases eq_zero_or_eq_one_of_card hK x with rfl | rfl <;> simp
  exact ⟨A, by rw [hσ, map_one, mul_one]⟩

theorem ggInnerDiagBound_psl_two {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hd : 3 ≤ d) (r : ℕ) :
    GGInnerDiagBound 3 r (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro Eb Eh _ _ _ _ _ hEhA _ hnot
  exact absurd (fun φ hφ =>
    mem_range_conjAut_of_odd_two hK hd (odd_orderOf_of_pow_three (hEhA.2 φ hφ))) hnot

theorem recipeLinear_innerDiag_two {d N : ℕ} (hd : 3 ≤ d) (hN : N = 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGInnerDiagBound 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
      (ggTorusLift_zero (two_dvd_card_projectiveSL (by omega))),
    ggInnerDiagBound_of_mulEquiv (recipeEquiv d K) (fun _ hφ => congr_recipeEquiv_mem hφ)
      (fun _ hφ => mem_of_congr_recipeEquiv_mem hφ) (ggInnerDiagBound_psl_two hK hd 0)⟩

theorem ggInnerDiagBound_sp_two {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (p r : ℕ) :
    GGInnerDiagBound p r (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro Eb Eh _ _ _ _ _ _ _ hnot
  exact absurd (fun φ _ => RecipeFieldSp.mem_conjImage_iff_inn.mpr (mem_range_conj_sp hK hm φ))
    hnot

theorem recipeSymplectic_innerDiag_two {m N : ℕ} (hm : 3 ≤ m) (hN : N = 2)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGInnerDiagBound 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact ⟨k, ggTorusLift_sp_two hK, ggInnerDiagBound_sp_two hK hm 3 k⟩

end CorFourTwoTwo

open CorFourTwoTwo

theorem largeEvenLabelAll_innerDiag_twoThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with rfl | ⟨rfl, rfl⟩
  · have hl : 2 ≤ l := by
      have h1 := hlab.2
      dsimp only at h1
      omega
    exact recipeLinear_innerDiag_two (d := l + 1) (by omega) (by norm_num) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    exact recipeLinear_innerDiag_two (d := 4) (by norm_num) (by norm_num) hQ

theorem largeEvenLabelAll_innerDiag_spTwoThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  have hl : 3 ≤ l := by
    have h1 := hlab.2
    rcases ht with rfl | rfl <;> dsimp only at h1 <;> omega
  rcases ht with rfl | rfl <;> exact recipeSymplectic_innerDiag_two hl (by norm_num) hQ

theorem ggBstarInnerDiagLInputOn_twoThree : GGBstarInnerDiagLInputOn GGTwoThreeLabel :=
  ggBstarInnerDiagLInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ _ hlab h =>
    largeEvenLabelAll_innerDiag_twoThree hlab h

theorem ggBstarInnerDiagLInputOn_spTwoThree : GGBstarInnerDiagLInputOn GGSpTwoThreeLabel :=
  ggBstarInnerDiagLInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ _ hlab h =>
    largeEvenLabelAll_innerDiag_spTwoThree hlab h

@[expose] def GGCorFourTwoRestLIDLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoRestSpLabel p lab ∧ ¬ GGTwoThreeLabel p lab ∧ ¬ GGSpTwoThreeLabel p lab

theorem GGTwoThreeLabel.corFourTwoRestSp {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTwoThreeLabel p lab) : GGCorFourTwoRestSpLabel p lab := by
  obtain ⟨rfl, hn, ht⟩ := h
  refine ⟨?_, ?_, GGTwoThreeLabel.split ⟨rfl, hn, ht⟩⟩
  · rintro (⟨-, h1, -⟩ | ⟨-, -, h1⟩ | ⟨h1, -, -⟩)
    · rw [hn] at h1
      norm_num at h1
    · rw [hn] at h1
      norm_num at h1
    · rcases ht with h2 | ⟨h2, -⟩ <;> rw [h2] at h1 <;> exact absurd h1 (by decide)
  · rintro ⟨h1, -⟩
    rcases ht with h2 | ⟨h2, -⟩ <;> rcases h1 with h1 | h1 <;> rw [h2] at h1 <;>
      exact absurd h1 (by decide)

theorem GGSpTwoThreeLabel.corFourTwoRestSp {p : ℕ} {lab : LargeEvenLabel}
    (h : GGSpTwoThreeLabel p lab) : GGCorFourTwoRestSpLabel p lab := by
  obtain ⟨rfl, hn, ht⟩ := h
  refine ⟨?_, ?_, Or.inr (Or.inr (Or.inr ⟨hn, rfl⟩))⟩
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩) <;> rcases ht with h2 | h2 <;> rw [h2] at h1 <;>
      exact absurd h1 (by decide)
  · rintro ⟨-, h1⟩
    rw [hn] at h1
    norm_num at h1

theorem ggBstarInnerDiagLInputOn_restSp_of_restLID
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoRestLIDLabel) :
    GGBstarInnerDiagLInputOn GGCorFourTwoRestSpLabel := by
  have h' := (ggBstarInnerDiagLInputOn_twoThree.or ggBstarInnerDiagLInputOn_spTwoThree).or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono_split fun p lab hlab _ => ?_)).mono fun p lab hlab => ?_
  · by_cases h1 : GGTwoThreeLabel p lab
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : GGSpTwoThreeLabel p lab
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨hlab, h1, h2⟩
  · rcases hlab with (h1 | h1) | h1
    · exact h1.corFourTwoRestSp
    · exact h1.corFourTwoRestSp
    · exact h1.1

theorem ggBstarInnerDiagLInputOn_rest_of_restLID
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoRestLIDLabel) :
    GGBstarInnerDiagLInputOn GGCorFourTwoRestLabel :=
  ggBstarInnerDiagLInputOn_rest_of_restSp (ggBstarInnerDiagLInputOn_restSp_of_restLID h)

theorem ggCor42Input_of_restLID
    (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoRestLIDLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoRestSpLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoRestSpLabel)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_restSp hK (ggBstarInnerDiagLInputOn_restSp_of_restLID hLID) hcen hline hnorm
    hgraph hfield

theorem ggNoTransvectionInput_of_restLID
    (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoRestLIDLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoRestSpLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoRestSpLabel) : GGNoTransvectionInput :=
  ggNoTransvectionInput_of_restSp hK (ggBstarInnerDiagLInputOn_restSp_of_restLID hLID) hcen
    hline

end CFSG.StandardType

end

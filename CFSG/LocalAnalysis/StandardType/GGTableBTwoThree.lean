module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA TwoThree CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem recipeLinear_tableB_two {d N : ℕ} (hd : 2 ≤ d) (hN : N = 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGBstarBound 3 r R I ∧ GGEndNode 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 5 ∨ 6 ≤ d by omega) with hd5 | hd6
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggBstarBound_of_mulEquiv (recipeEquiv d K) hI (ggBstarBound_two_small hK (by omega) hd5),
      ggEndNode_of_mulEquiv (recipeEquiv d K) hI (ggEndNode_two_small hK (by omega) hd5)⟩
  · exact ⟨d / 2, ggTorusLift_of_mulEquiv (recipeEquiv d K) (ggTorusLift_two hK (by omega)),
      ggBstarBound_of_mulEquiv (recipeEquiv d K) hI (ggBstarBound_two hK (by omega)),
      ggEndNode_of_mulEquiv (recipeEquiv d K) hI (ggEndNode_two hK hd6)⟩

@[expose] def GGTwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ lab.n = 1 ∧ (lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3))

theorem GGTwoThreeLabel.split {p : ℕ} {lab : LargeEvenLabel} (h : GGTwoThreeLabel p lab) :
    LargeEvenSplit p lab :=
  Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1⟩))

theorem GGTwoThreeLabel.pilot {p : ℕ} {lab : LargeEvenLabel} (h : GGTwoThreeLabel p lab) :
    GGOutdiagPilotLabel lab := by
  rcases h.2.2 with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem largeEvenLabelAll_twoThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
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
    exact recipeLinear_tableB_two (d := l + 1) (by omega) (by norm_num) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    exact recipeLinear_tableB_two (d := 4) (by norm_num) (by norm_num) hQ

theorem ggBstarInputOn_twoThree : GGBstarInputOn GGTwoThreeLabel :=
  ggBstarInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ _ hlab h =>
    (largeEvenLabelAll_twoThree hlab h).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggStdSubPreInputOn_twoThree : GGStdSubPreInputOn GGTwoThreeLabel :=
  ggStdSubPreInputOn_of_labels fun _ _ _ hlab h =>
    (largeEvenLabelAll_twoThree hlab h).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

end CFSG.StandardType

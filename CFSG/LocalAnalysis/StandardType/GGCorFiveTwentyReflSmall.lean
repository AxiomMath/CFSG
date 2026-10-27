module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeB2der

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TypeA TwoThree

namespace TwoThree

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem ggTorusReflBridge_of_not_dvd {p : ℕ} (hp : p.Prime) {H : Subgroup (GL ι K)}
    {S : Set (GL ι K)} (hS : S ⊆ Subgroup.normalizer (H : Set (GL ι K)))
    (hGL : ¬ p ^ 3 ∣ Nat.card (GL ι K)) :
    GGTorusReflBridge p 0 (LargeEvenProj H) (LargeEvenMatConjImage (LargeEvenProjMk H) S) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (LargeEvenProj H))) :
      Set (MulAut (LargeEvenProj H))) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hlt := card_lt_of_not_dvd hp hS hGL hX hXI
  rw [hcard] at hlt
  omega

end TwoThree

theorem not_pow_three_dvd_20160 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 3 ∣ 20160 := by
  intro h
  have hle : p ^ 3 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hp27 : p ≤ 27 := by
    by_contra hc
    have h28 : 28 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p
  all_goals first
    | exact hp2 rfl
    | (revert h; decide)
    | (norm_num at hp)

theorem recipeB2der_reflBridge {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic 2 2 true Q) :
    LargeEvenRecipeSymplectic 2 2 true fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  refine ⟨0, ggTorusLift_zero (two_dvd_card_b2der hK),
    ggTorusReflBridge_of_not_dvd hp (gsp_subset_normalizer hK) ?_⟩
  rw [card_GL_four hK]
  exact not_pow_three_dvd_20160 hp hp2

@[expose] def GGReflB2derLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B2der ∧ p ≠ 2

theorem largeEvenLabelAll_reflBridge_b2der {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGReflB2derLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflBridge p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hp2⟩ := h
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeB2der_reflBridge hp hp2 hQ

end CFSG.StandardType

end

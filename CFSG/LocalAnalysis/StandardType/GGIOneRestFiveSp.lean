module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveRoot
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreNarrow
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneSpTwoRootInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ m : ℕ, 4 ≤ m →
    GGEndNodeRootEltBig 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m))

section Certs

theorem ggEndNodeIOne_spTwo_of_root (hE : GGIOneSpTwoRootInput) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) :
    GGEndNodeIOne 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have : NeZero m := ⟨by omega⟩
  obtain ⟨-, hC⟩ := ggSpNonsplitTorusInput_holds K m 3 (by omega) Nat.prime_three (by rw [hK])
  exact ggEndNodeIOne_of_rootEltBig (fun φ hφ _ => TableBSymp.sp_I_subset_inn hφ)
    TableBSymp.center_spProj_eq_bot hC (hE K hK m hm)

theorem recipeSymplectic_endNodeIOne_spTwo (hE : GGIOneSpTwoRootInput) {m : ℕ} (hm : 4 ≤ m)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m (2 ^ 1) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ 1) false fun R _ I F => Q R I F ∧ GGOutdiagOdd 3 R I ∧
      ∃ r, GGTorusLift 3 r R ∧ GGEndNodeIOne 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ggOutdiagOdd_of_prime fun φ hφ _ =>
    TableBSymp.sp_I_subset_inn hφ, k + 1 - 1, ?_, ggEndNodeIOne_spTwo_of_root hE hK2 hm⟩
  rw [hk]
  exact TwoThree.ggTorusLift_sp_two hK2

theorem largeEvenLabelAll_endNodeIOne_spTwoRest (hE : GGIOneSpTwoRootInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGIOneMoreSpTwoRestLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, rfl⟩ := h
  dsimp only at ht hl hn
  subst hn
  intro Q hQ
  rcases ht with rfl | rfl <;> exact recipeSymplectic_endNodeIOne_spTwo hE hl hQ

theorem ggStdSubIOneProperInputOn_spTwoRest (ha₀ : GGLNoncyclicInput)
    (hE : GGIOneSpTwoRootInput) : GGStdSubIOneProperInputOn GGIOneMoreSpTwoRestLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ _ _ h _ =>
    largeEvenLabelAll_endNodeIOne_spTwoRest hE h

end Certs

end CFSG.StandardType

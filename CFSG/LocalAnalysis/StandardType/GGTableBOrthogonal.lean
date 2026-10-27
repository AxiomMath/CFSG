module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBstarMinus
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp TableBOrth

theorem recipeOmegaPlus_tableB {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 4 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    ggTorusLift_omegaPlus hp hp2 hpq (by omega), ggBstarBound_omegaPlus hp hp2 hpq (by omega),
    ggEndNode_omegaPlus hp hp2 hpq hl⟩

theorem recipeOmegaMinus_tableB {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hm : 3 ≤ m) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m,
    ggTorusLift_omegaMinus hp hp2 hpq hm b c, ggBstarBound_omegaMinus hp hp2 hpq hm hbc,
    ggEndNode_omegaMinus hp hp2 hpq hm hbc⟩

theorem largeEvenLabelAll_tableB_D {lab : LargeEvenLabel} (htag : lab.tag = .D)
    (hlab : LargeEvenInLambda2 lab) (hl : 4 ≤ lab.rank) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · exact recipeOmegaPlus_tableB hp hp2 hpn hl hQ

theorem largeEvenLabelAll_tableB_twD {lab : LargeEvenLabel} (htag : lab.tag = .twD)
    (hlab : LargeEvenInLambda2 lab) (hl : 4 ≤ lab.rank) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · exact recipeOmegaMinus_tableB hp hp2 hpn (by omega) hQ

theorem largeEvenLabelAll_tableB_orthogonal {lab : LargeEvenLabel}
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hlab : LargeEvenInLambda2 lab) (hl : 4 ≤ lab.rank)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  rcases htag with h | h
  · exact largeEvenLabelAll_tableB_D h hlab hl hp hpn
  · exact largeEvenLabelAll_tableB_twD h hlab hl hp hpn

theorem largeEvenSplit_D_iff {p : ℕ} {lab : LargeEvenLabel} (htag : lab.tag = .D) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  simp [LargeEvenSplit, LargeEvenUntwisted]

theorem largeEvenSplit_twD_iff {p : ℕ} {lab : LargeEvenLabel} (htag : lab.tag = .twD) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  simp [LargeEvenSplit, LargeEvenUntwisted]

end CFSG.StandardType

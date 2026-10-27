module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp

theorem recipeSymplectic_tableB {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 2 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    ggTorusLift_symplectic hp hp2 hpq (by omega), ggBstarBound_symplectic hp hp2 hpq (by omega),
    ggEndNode_symplectic hp hp2 hpq hl⟩

theorem ne_two_of_dvd_two_pow_sub_one {p n : ℕ} (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1) : p ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2 hpn
  rw [Nat.sub_sub_self h1] at this
  omega

theorem largeEvenLabelAll_tableB_symplectic {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hlab : LargeEvenInLambda2 lab) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_tableB hp hp2 hpn hlab.2.1 hQ

theorem largeEvenSplit_symplectic_iff {p : ℕ} {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    simp [LargeEvenSplit, LargeEvenUntwisted]

theorem largeEvenLabelAll_tableB_symplectic_of_split {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (hlab : LargeEvenInLambda2 lab) (hn : 2 ≤ lab.n)
    {p : ℕ} (hp : p.Prime) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I := by
  rcases (largeEvenSplit_symplectic_iff htag).mp hs with hpn | ⟨h1, -⟩
  · exact largeEvenLabelAll_tableB_symplectic htag hlab hp hpn
  · omega

end CFSG.StandardType

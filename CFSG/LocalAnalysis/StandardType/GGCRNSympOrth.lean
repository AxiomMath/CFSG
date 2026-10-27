module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpLift
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem crnc_symplectic_split {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (h3 : 3 ∣ 2 ^ lab.n - 1) (hl : 1 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 lab.rank R := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with h | h <;> dsimp only at h h3 hl ⊢ <;> subst h <;>
    intro Q hQ <;>
    exact TableBSymp.recipeSymplectic_torusLift Nat.prime_three (by decide) h3 hl hQ

theorem ggCRN_lift_BC_split {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hd : 24 ≤ 2 * lab.rank) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R :=
  (crnc_symplectic_split htag h3 (by omega)).mono fun _ _ _ _ h =>
    ggTorusLift_mono Nat.prime_three h (by omega)

private theorem crnc_recipeSymplectic_ns {l n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) (hl : 9 < l)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ GGTorusLift 3 9 R := by
  obtain ⟨K, i1, i2, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3
  exact ⟨K, i1, i2, hK, hQ,
    TableBSymp.ggTorusLift_symplecticNs_of_lt Nat.prime_three (by decide) hpq hl⟩

private theorem crnc_symplectic_nonsplit {lab : LargeEvenLabel}
    (htag : lab.tag = .B ∨ lab.tag = .C) (h3 : 3 ∣ 2 ^ lab.n + 1) (hl : 9 < lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with h | h <;> dsimp only at h h3 hl ⊢ <;> subst h <;>
    intro Q hQ <;> exact crnc_recipeSymplectic_ns h3 hl hQ

theorem ggCRN_lift_BC_nonsplit {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hd : 24 ≤ 2 * lab.rank) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R :=
  crnc_symplectic_nonsplit htag h3 (by omega)

theorem ggCRN_lift_D_split {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .D) (hd : 24 ≤ 2 * lab.rank) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R :=
  (largeEvenLabelAll_torusLift_D htag hlab (by omega) Nat.prime_three h3).mono
    fun _ _ _ _ h => ggTorusLift_mono Nat.prime_three h (by omega)

theorem ggCRN_lift_twD_split {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twD) (hd : 24 ≤ 2 * lab.rank) (h3 : 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R :=
  (largeEvenLabelAll_torusLift_twD htag hlab (by omega) Nat.prime_three h3).mono
    fun _ _ _ _ h => ggTorusLift_mono Nat.prime_three h (by omega)

theorem ggCRN_lift_twD_nonsplit
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twD) (hd : 24 ≤ 2 * lab.rank) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R :=
  (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three
    ⟨by omega, Or.inl ⟨htag, h3⟩⟩).mono fun _ _ _ _ h =>
      ggTorusLift_mono Nat.prime_three h.2 (by omega)

end CFSG.StandardType

end

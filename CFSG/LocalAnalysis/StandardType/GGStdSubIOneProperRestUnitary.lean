module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRest

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGIOneTwDThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1 ∧ p ≠ 3

theorem largeEvenLabelAll_twDThree_of_twA {n : ℕ} {P : LargeEvenRawCont}
    (h : LargeEvenLabelAll ⟨.twA, 3, n⟩ P) : LargeEvenLabelAll ⟨.twD, 3, n⟩ P := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte, show (3 : ℕ) ≠ 2 by norm_num] at hQ ⊢
  exact h Q hQ

theorem largeEvenLabelAll_endNodeIOne_twDThree
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGIOneTwDThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      ∃ r, GGTorusLift p r R ∧ GGEndNodeIOne p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq, hp3⟩ := h
  dsimp only at ht hl hpq hp3
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hpd : ¬ p ∣ 3 + 1 := by
    intro h4
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  have hlab' : LargeEvenInLambda2 ⟨.twA, 3, n⟩ := ⟨hn, by norm_num, by norm_num⟩
  have hl' : GGIOneUnitaryLabel p ⟨.twA, 3, n⟩ := ⟨rfl, hpq, hpd, hp3, le_rfl⟩
  have h1 := largeEvenLabelAll_torusLift_twA hlab' rfl hp hpq
  have hZ := largeEvenLabelAll_centerPrime_unitary hp hlab' ⟨Or.inl rfl, hpq⟩ hpd
  have h2 := largeEvenLabelAll_endNodeIOne_unitary hp hlab' hl' hZ
  exact largeEvenLabelAll_twDThree_of_twA ((h1.and h2).mono
    fun _ _ _ _ ⟨hlift, hO, hend⟩ => ⟨hO, _, hlift, hend⟩)

theorem ggStdSubIOneProperInputOn_twDThree
    (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneTwDThreeLabel :=
  ggStdSubIOneProperInputOn_of_labels ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_endNodeIOne_twDThree hp hlab h

end CFSG.StandardType

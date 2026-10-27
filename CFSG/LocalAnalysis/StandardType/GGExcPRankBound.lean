module

public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE8RestTorus
public import CFSG.GroupTheory.ElemAbelianRank

public section

namespace CFSG.StandardType.ExcMaxToral

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggR1_not_dvd_sub_one {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf (q : ZMod p) ≠ 1) : ¬ p ∣ q - 1 := by
  intro hdvd
  apply h
  have h0 : (((q - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_sub hq, Nat.cast_one] at h0
  exact orderOf_eq_one_iff.mpr (sub_eq_zero.mp h0)

private theorem ggR1_not_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : orderOf (q : ZMod p) ≠ 2) : ¬ p ∣ q + 1 := by
  intro hdvd
  apply h
  have h0 : (((q + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  push_cast at h0
  have hx : (q : ZMod p) = -1 := by linear_combination h0
  have hsq : (q : ZMod p) ^ 2 = 1 := by rw [hx]; ring
  have hdvd2 : orderOf (q : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hne1 : orderOf (q : ZMod p) ≠ 1 := by
    intro ho
    have hq1 : (q : ZMod p) = 1 := orderOf_eq_one_iff.mp ho
    have htwo : (2 : ZMod p) = 0 := by linear_combination hx - hq1
    have hp2dvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
  rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf (q : ZMod p)) hdvd2 with h1 | h2
  · exact absurd h1 hne1
  · exact h2

theorem excPRankBound
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ 3)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K := CFSG.StandardType.PRankBounds.not_dvd_card_of_charTwo hp hp2
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdne1 : orderOf (Nat.card K : ZMod p) ≠ 1 := by
    intro h
    rcases hτ with rfl | rfl | rfl <;> (rw [h] at hd; exact absurd hd (by decide))
  have hdne2 : orderOf (Nat.card K : ZMod p) ≠ 2 := by
    intro h
    rcases hτ with rfl | rfl | rfl <;> (rw [h] at hd; exact absurd hd (by decide))
  have h1 : ¬ p ∣ Nat.card K - 1 := ggR1_not_dvd_sub_one hq1 hdne1
  have h2 : ¬ p ∣ Nat.card K + 1 := ggR1_not_dvd_add_one hp hp2 hdne2
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hcardE : Nat.card E = p ^ CFSG.Open.pRank p E :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (G := adjointGroup τ K) (E := E) hp hE
  rcases hτ with rfl | rfl | rfl
  · have hlt := CFSG.StandardType.ggExcNonsplitRankInput_E7 K (p := p) hp hp2 h1 h2 E hE
    rw [hcardE] at hlt
    have hle : CFSG.Open.pRank p E ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ CFSG.Open.pRank p E := by omega
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right hp.pos h4))
    calc Nat.card E = p ^ CFSG.Open.pRank p E := hcardE
      _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos hle
  · by_contra hle
    have hle' : p ^ 3 < Nat.card E := Nat.lt_of_not_le hle
    have h4 : p ^ 4 ≤ Nat.card E := by
      rw [hcardE] at hle' ⊢
      have h4' : 4 ≤ CFSG.Open.pRank p E := by
        by_contra h
        have h3 : CFSG.Open.pRank p E ≤ 3 := by omega
        exact absurd (Nat.pow_le_pow_right hp.pos h3) (not_le.mpr hle')
      exact Nat.pow_le_pow_right hp.pos h4'
    have h36 :=
      CFSG.StandardType.ExcFrames.orderOf_mem_of_four_le_card K (p := p) hp hpq h1 h2 (A := E) hE h4
    rcases h36 with h3 | h4' | h6
    · rw [h3] at hd; exact absurd hd (by decide)
    · rw [h4'] at hd; exact absurd hd (by decide)
    · rw [h6] at hd; exact absurd hd (by decide)
  · have hlt := CFSG.StandardType.ggExcNonsplitRankInput_F4 K (p := p) hp hp2 h1 h2 E hE
    rw [hcardE] at hlt
    have hle : CFSG.Open.pRank p E ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ CFSG.Open.pRank p E := by omega
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right hp.pos h4))
    calc Nat.card E = p ^ CFSG.Open.pRank p E := hcardE
      _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos hle

end CFSG.StandardType.ExcMaxToral

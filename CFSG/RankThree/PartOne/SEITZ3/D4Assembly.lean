module

public import CFSG.RankThree.PartOne.SEITZ3.D4Even
public import CFSG.RankThree.PartOne.CTP.SeitzFine

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.RankThree.PartOne.CTP

section Arith

theorem d4_prime_twelve {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (hdvd : p ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1))
    (hq0 : ¬ p ∣ q) (hm : ¬ p ∣ q - 1) (hpl : ¬ p ∣ q + 1)
    (h3 : ¬ p ∣ q ^ 2 + q + 1) (h6 : ¬ p ∣ q ^ 2 - q + 1) : p ∣ q ^ 4 - q ^ 2 + 1 := by
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e2 : q ^ 2 - 1 = (q + 1) * (q - 1) := sq_sub_one_eq_mul h1
  have e6 : q ^ 6 - 1 = (q + 1) * (q - 1) * ((q ^ 2 + q + 1) * (q ^ 2 - q + 1)) := by
    have h6' : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ h1
    zify [h1, h2, h6']
    ring
  have e12 : q ^ 8 + q ^ 4 + 1 = (q ^ 2 + q + 1) * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
    zify [h2, h4]
    ring
  by_contra hnot
  have hq12 : ¬ p ∣ q ^ 12 := fun h => hq0 (hp.dvd_of_dvd_pow h)
  rw [e2, e6, e12] at hdvd
  simp [Nat.Prime.dvd_mul hp, hq12, hm, hpl, h3, h6, hnot] at hdvd

end Arith

section Assembly

@[expose] def Exc3D4NonsplitPhi3Phi6 : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 →
    ExtSeitzAtInnerFor (.trialityD4 q) fun p =>
      p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1

theorem exc3D4Nonsplit_of_narrow
    (h : Max3D4A1A1Big ∧ Exc3D4NonsplitPhi3Phi6) : Exc3D4Nonsplit := by
  intro q hq K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hinner
  by_cases h1 : p ∣ q.card + 1
  · exact extSeitzAtInnerFor_trialityD4_qplus h.1 hq K hnab hiso p hp hp5 hpd h1 E hE hcard hinner
  by_cases h2 : p ∣ q.card ^ 2 + q.card + 1 ∨ p ∣ q.card ^ 2 - q.card + 1
  · exact h.2 q hq K hnab hiso p hp hp5 hpd h2 E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  refine closure_fixUnion_eq_top_of_inner_equiv hnab (MulEquiv.refl K) (p := p) ?_ E hcard
    hinner
  intro E₁ hE₁ hcard₁
  exfalso
  have := hE₁
  have hQ : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have hQ2 : 2 ≤ q.card := by
    rw [hQ]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) q.exponent_pos
  have hq0 : ¬ p ∣ q.card := by
    rw [hQ]
    intro h0
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h0)
    omega
  have hdvd : p ∣ Nat.card K := by
    have h0 := Subgroup.card_subgroup_dvd_card E₁
    rw [hcard₁] at h0
    exact (dvd_pow_self p two_ne_zero).trans h0
  rw [card_isoLie_trialityD4 hq hiso] at hdvd
  have h12 := d4_prime_twelve hp hQ2 hdvd hq0 hP h1 (fun h0 => h2 (Or.inl h0))
    (fun h0 => h2 (Or.inr h0))
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := exists_trialityD4_model hq hiso
  have : Finite (graphFixedRootGroup TwistTag.D4 X σ.toRingHom) := Finite.of_equiv K e.toEquiv
  rw [hQ] at h12
  have h3 := CFSG.RankThree.PartOne.K128.pRank_le_one_D4_twelve Nat.prime_two q.exponent_pos X hX
    σ hσ hp hp5 h12
  have h4 := CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e
  have h5 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt E₁ hE₁ hcard₁
  omega

end Assembly

end CFSG.RankThree.PartOne.SEITZ3

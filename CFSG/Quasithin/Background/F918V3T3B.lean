module

public import CFSG.Quasithin.Background.F918V3T3A
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenRee
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SectionRank.TitsCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint

namespace F918V3T3

theorem three_dvd_two_pow_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 f
  rw [one_pow] at h
  have e : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]
  exact h

theorem three_dvd_two_pow_odd_add_one (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
  have h : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have e : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by rw [pow_succ, pow_mul]; norm_num; ring
  rw [e]
  omega

theorem three_dvd_card_of_G2
    {S : Type} [Group S] {f : ℕ} (h : ChevalleyExceptionalModel S .G2 2 f) :
    3 ∣ Nat.card S := by
  rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h]
  exact Dvd.dvd.mul_left (three_dvd_two_pow_sq_sub_one f) _

theorem three_dvd_card_of_trialityD4
    {S : Type} [Group S] {f : ℕ} (h : ChevalleyExceptionalModel S .trialityD4 2 f) :
    3 ∣ Nat.card S := by
  rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h]
  exact Dvd.dvd.mul_left (three_dvd_two_pow_sq_sub_one f) _

theorem three_dvd_card_of_twistedF4
    {S : Type} [Group S] {p f : ℕ} (h : ReeTitsModel S .twistedF4 p f) : 3 ∣ Nat.card S := by
  obtain ⟨K, _, _, _, a, -, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h
  have hK2 : Nat.card K = 2 ^ (2 * a + 1) := hK
  rw [Nat.card_congr e.toEquiv,
    CFSG.ComponentClassification.ExcSelector.card_reeFixed_F4 hK2]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Dvd.dvd.mul_left (dvd_pow (three_dvd_two_pow_odd_add_one a) two_ne_zero) _) _) _) _) _

theorem three_dvd_card_of_Tits
    {S : Type} [Group S] {p f : ℕ} (h : ReeTitsModel S .Tits p f) : 3 ∣ Nat.card S := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
  obtain ⟨x, y, z, -, -, -, -, -, hc, -⟩ := CFSG.SectionRank.Tits_sylow3_cubic_witness (K := K) hK
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_of_card_eq _ (k := 3) (by norm_num) hc

end F918V3T3

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.Goldschmidt75.TheoremBcN1
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem two_pow_mod_five (m : ℕ) : 2 ^ m % 5 = 2 ^ (m % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem one_le_padicValNat_five_two_pow {n : ℕ} (hn : Odd n) :
    1 ≤ padicValNat 5 (2 ^ (2 * n) + 1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h4 : 2 * n % 4 = 2 := by
    obtain ⟨m, rfl⟩ := hn
    omega
  have hp := two_pow_mod_five (2 * n)
  rw [h4] at hp
  norm_num at hp
  have hdvd : 5 ^ 1 ∣ 2 ^ (2 * n) + 1 := by
    rw [pow_one]
    omega
  exact (padicValNat_dvd_iff_le (by positivity)).mp hdvd

namespace CoreSetup

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

theorem lt_padicValNat_card_normalizer (h : CoreSetup X K L T Y n) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrL : r ∣ Nat.card L)
    (hK : padicValNat r (Nat.card L) < padicValNat r (Nat.card K)) :
    padicValNat r (Nat.card L) < padicValNat r (Nat.card ↥(K ⊓ normalizer (L : Set X))) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  set M : Subgroup X := K ⊓ normalizer (L : Set X) with hM
  have hLM : L ≤ M := le_inf h.le le_normalizer
  obtain ⟨RL, hRL⟩ := CFSG.ABGLocalTools.exists_isSylowOf r L
  have hRLK : RL ≤ K := hRL.le.trans h.le
  obtain ⟨Q, hQ⟩ := (hRL.isPGroup.comap_subtype (K := K)).exists_le_sylow
  set R : Subgroup X := (Q : Subgroup K).map K.subtype with hRdef
  have hR : CFSG.ABGLocalTools.IsSylowOf r R K := ⟨Q, rfl⟩
  have hRLR : RL ≤ R := fun x hx => ⟨⟨x, hRLK hx⟩, hQ hx, rfl⟩
  have hcardRL : Nat.card RL = r ^ padicValNat r (Nat.card L) := by
    rw [hRL.card_eq, Nat.factorization_def _ hr]
  have hcardR : Nat.card R = r ^ padicValNat r (Nat.card K) := by
    rw [hR.card_eq, Nat.factorization_def _ hr]
  have hlt : RL < R := by
    refine lt_of_le_of_ne hRLR fun heq => ?_
    have h1 := hcardRL
    rw [heq, hcardR] at h1
    exact (ne_of_lt hK) (Nat.pow_right_injective hr.two_le h1).symm
  set S : Subgroup X := R ⊓ normalizer (RL : Set X) with hSdef
  have hSgt : RL < S := CFSG.Goldschmidt75.lt_inf_normalizer hR.isPGroup hlt
  have hSp : IsPGroup r S := hR.isPGroup.to_le inf_le_left
  have hRL1 : RL ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card RL = 1 := by rw [hbot]; exact Subgroup.card_bot
    have hv : 1 ≤ padicValNat r (Nat.card L) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (by rwa [pow_one])
    have h2 : r ^ 1 ≤ r ^ padicValNat r (Nat.card L) := Nat.pow_le_pow_right hr.pos hv
    rw [← hcardRL, h1, pow_one] at h2
    exact absurd h2 (by have := hr.two_le; omega)
  have hE := CFSG.Goldschmidt75.inf_centralizer_ne_bot hSp hSgt.le inf_le_right hRL1
  set E : Subgroup X := RL ⊓ centralizer (S : Set X) with hEdef
  have hEp : IsPGroup r E := hRL.isPGroup.to_le inf_le_left
  have hEdvd : r ∣ Nat.card E := by
    rcases hEp.card_eq_or_dvd with h1 | h1
    · exact absurd ((Subgroup.card_eq_one).mp h1) hE
    · exact h1
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) r hEdvd
  have haE : (a : X) ∈ E := a.2
  set A : Subgroup X := zpowers (a : X) with hAdef
  have hAL : A ≤ L := (zpowers_le_of_mem haE.1).trans hRL.le
  have hAcard : Nat.card A = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
  have hNA := h.normalizer_le_normalizer hAL (hAcard ▸ hr) (hAcard ▸ hr2)
  have hSA : S ≤ normalizer (A : Set X) := by
    intro s hs
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hc : Commute s (a : X) := (mem_centralizer_iff.mp haE.2) s hs
    exact (hc.zpow_right k).symm.eq
  have hSM : S ≤ M := le_inf (inf_le_left.trans hR.le) (hSA.trans hNA)
  by_contra hcon
  have hcon' := not_lt.mp hcon
  have hle : padicValNat r (Nat.card L) ≤ padicValNat r (Nat.card M) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp
      (pow_padicValNat_dvd.trans (Subgroup.card_dvd_of_le hLM))
  have hRLM : CFSG.ABGLocalTools.IsSylowOf r RL M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (hRL.le.trans hLM) ?_
    rw [hcardRL, Nat.factorization_def _ hr, le_antisymm hcon' hle]
  exact hSgt.ne' (hRLM.eq_of_le hSgt.le hSM hSp)

theorem padicValNat_five_card_L (h : CoreSetup X K L T Y n) :
    padicValNat 5 (Nat.card L) = padicValNat 5 (2 ^ (2 * n) + 1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hodd, hn3⟩ := h.odd_three_le
  have hSz : Nat.card (Bar2 L) = (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 h.sz
  have h2n : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  rw [h2n] at hSz
  have hL : Nat.card L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have hpow : ∀ m : ℕ, ¬ 5 ∣ 2 ^ m := fun m hd =>
    absurd (Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow (by norm_num) hd))
      (by norm_num)
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : ¬ 5 ∣ 2 ^ n - 1 := by
    obtain ⟨m, hm⟩ := hodd
    have hp := two_pow_mod_five n
    rcases (show n % 4 = 1 ∨ n % 4 = 3 by omega) with h4 | h4 <;>
      · rw [h4] at hp
        norm_num at hp
        omega
  have hA : 2 ^ (2 * n) ≠ 0 := by positivity
  have hB : 2 ^ (2 * n) + 1 ≠ 0 := by positivity
  have hC : 2 ^ n - 1 ≠ 0 := by omega
  have hD : 2 ^ k ≠ 0 := by positivity
  rw [hL, hSz, hk, padicValNat.mul (mul_ne_zero (mul_ne_zero hA hB) hC) hD,
    padicValNat.mul (mul_ne_zero hA hB) hC, padicValNat.mul hA hB,
    padicValNat.eq_zero_of_not_dvd (hpow _), padicValNat.eq_zero_of_not_dvd (hpow _),
    padicValNat.eq_zero_of_not_dvd hq1]
  simp

end CoreSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

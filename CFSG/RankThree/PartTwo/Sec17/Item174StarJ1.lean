module

public import CFSG.RankThree.PartTwo.Sec17.Item174StarL2
import CFSG.Walter.Models
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Small
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoFiveJ1

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG

private theorem starCore_walterJ1 : StarCore CFSG.Open.walterJ1 := by
  intro _ t ht I hI D hDI hD hID hc
  exfalso
  apply hc
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have htI : t ∈ I := hI (Subgroup.le_normalizer (Subgroup.mem_zpowers t))
  have htD : t ∈ Subgroup.normalizer (D : Set CFSG.Open.walterJ1) := hID htI
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5
    (CFSG.EvenSporadicStandard.RuStd.S2.walterJ1_three_five t ht)
  have hut : (u : CFSG.Open.walterJ1) * t = t * u :=
    (Subgroup.mem_centralizer_singleton_iff.mp u.2)
  have hu5 : orderOf (u : CFSG.Open.walterJ1) = 5 := by rw [← Subgroup.orderOf_coe] at hu; exact hu
  have huI : (u : CFSG.Open.walterJ1) ∈ I := by
    refine hI (mem_normalizer_zpowers_of ?_ ?_)
    · rw [hut, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers t
    · have : (u : CFSG.Open.walterJ1)⁻¹ * t * u = t := by
        rw [mul_assoc, ← hut, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.mem_zpowers t
  have hD8 : Nat.card D ≤ 8 := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    have hdvd : 2 ^ n ∣ 175560 := by
      rw [← hn, ← CFSG.Walter.J1Props.card_walterJ1]
      exact Subgroup.card_subgroup_dvd_card D
    have hn3 : n ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ∣ 175560 := (pow_dvd_pow 2 (by omega)).trans hdvd
      omega
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 8 := by norm_num
  have huD := CFSG.QuasithinUnique.A5.Kc3J4.pow_centralizer_of_orderOf_five hD hD8 hu5 (hID huI)
  have hDC : D ≤ Subgroup.centralizer (Subgroup.zpowers (u : CFSG.Open.walterJ1) : Set _) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hdu : d * u = u * d := Subgroup.mem_centralizer_iff.mp huD d hd
    exact ((show Commute (u : CFSG.Open.walterJ1) d from hdu.symm).zpow_left k).eq
  have hcC := CFSG.Walter.J1.JankoHyp.card_centralizer_odd CFSG.Walter.J1Props.jankoHyp
    (Or.inr rfl) (X := Subgroup.zpowers (u : CFSG.Open.walterJ1)) (by rw [Nat.card_zpowers, hu5])
  have hdvd : Nat.card D ∣ 30 := by
    have h1 := Subgroup.card_dvd_of_le hDC
    rcases hcC with h | h
    · rw [h] at h1
      exact h1.trans (by norm_num)
    · rwa [h] at h1
  refine commutator_eq_bot_of_card_le_two ?_ htD
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  rw [hn] at hdvd ⊢
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · exfalso
    have : 4 ∣ 30 := (pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans hdvd
    omega

theorem starJ1_proved : StarJ1 := by
  intro H _ _ ⟨e⟩
  obtain ⟨eN⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have e' : H ≃* TauCeti.SporadicName.J1.Group := e
  exact starFor_of_starCore (starCore_of_mulEquiv
    ((e'.trans eN.symm).trans CFSG.Walter.walterJ1EquivNative.symm) starCore_walterJ1)

theorem kfactStar_of_L3U3
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple) (hL3 : StarL3Odd)
    (hU3 : StarU3) : KFactStar :=
  kfactStar_of_families hS starL2_proved hL3 hU3 starJ1_proved starA5_proved

end CFSG.RankThree.PartTwo.Sec17.Proof174Host

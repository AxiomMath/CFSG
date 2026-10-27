module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsLiftOmega
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRowPRankLeTwo_smallPlus :
    GGRowPRankLeTwo fun p lab => ((lab.tag = .A ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
      (lab.tag = .D ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1 := by
  intro p hp hp2 lab _ hcell
  obtain ⟨hl, hdvd⟩ := hcell
  have hpe : ∀ j, 0 < j → 3 * j ≤ (if lab.tag = .D then 4 else lab.rank + 1) →
      ¬ p ∣ (2 ^ lab.n) ^ j - 1 := by
    intro j hj hj3 hdiv
    have hj1 : j = 1 := by
      rcases hl with ⟨ht, hr⟩ | ⟨ht, hr⟩
      · rw [if_neg (by rw [ht]; decide)] at hj3
        omega
      · rw [if_pos ht] at hj3
        omega
    subst hj1
    rw [pow_one] at hdiv
    have h2 : p ∣ 2 := by
      have h := Nat.dvd_sub hdvd hdiv
      have e : 2 ^ lab.n + 1 - (2 ^ lab.n - 1) = 2 := by
        have := Nat.one_le_two_pow (n := lab.n)
        omega
      rwa [e] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have h : (lab.tag = .A ∧ 2 ≤ lab.rank) ∨ (lab.tag = .D ∧ lab.rank = 3) := by
    rcases hl with ⟨ht, hr⟩ | ⟨ht, hr⟩
    · exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr ⟨ht, hr⟩
  exact (largeEvenLabelAll_card_lt_linear_of_ord hp hp2 h hpe).mono fun _ _ _ _ hX _ _ => hX

theorem largeEvenLabelAll_frame_omegaMinusNs
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Even lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨htag, hl, hle, hpn⟩ := h
  dsimp only at htag hl hle hpn ⊢
  subst htag
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hm : 3 ≤ l - 1 := by omega
    have hmo : Odd (l - 1) := by
      obtain ⟨k, hk⟩ := hle
      exact ⟨k - 1, by omega⟩
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpn
    obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 hm hbc
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', l - 1,
      ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK hm hp hpn hbc, ?_⟩
    exact ggTorusFrame_of_frameEltSC hp hp2 hZ (fun φ hφ _ => hφ) hcp
      (ggTorusFrameEltSC_of_signedEltSC hp
        (ggOrthSignedTorusInput_holds.2 K (l - 1) p b c hm hbc hp (Or.inr ⟨hmo, hpK⟩)))

theorem largeEvenLabelAll_frame_omegaPlusNs
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨htag, hl, hlo, hpn⟩ := h
  dsimp only at htag hl hlo hpn ⊢
  subst htag
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpn
    obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
    have hlift : ∃ r, GGTorusLift p r (OrthRest.RPlus K l) := by
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · obtain rfl : n = 1 := by omega
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpn)
        subst hp3
        exact ⟨l - 1, ggOrthRestTorusLiftInput_holds.2 K l (by rw [hK]; norm_num) (by omega)⟩
      · have hK4 : 4 ≤ Nat.card K := by
          rw [hK]
          exact (Nat.pow_le_pow_right (by norm_num) hn2 : 2 ^ 2 ≤ 2 ^ n)
        exact ⟨3, TableBSymp.ggTorusLift_omegaPlusNs hp hp2 hpK hK4 (by omega)⟩
    obtain ⟨r, hr⟩ := hlift
    refine ⟨K, inferInstance, inferInstance, hK, hQ', r, hr, ?_⟩
    exact ggTorusFrame_of_frameEltSC hp hp2 hZ (fun φ hφ _ => hφ) hcp
      (ggTorusFrameEltSC_of_signedEltSC hp (ggOrthSignedTorusInput_holds.1 K l p hl hlo hp hpK))

end CFSG.StandardType

end

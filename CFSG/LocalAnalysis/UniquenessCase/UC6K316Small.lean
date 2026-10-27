module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Frame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoL28
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicTits
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

theorem coprime_card_of_isPGroup_two {X : Type*} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {W : Subgroup X} (hW : IsPGroup 2 W) : Nat.Coprime r (Nat.card W) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)

theorem twoSigTriv_l28 {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : TwoSigTriv 3 K := by
  intro S W hW hnorm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : AGLEmbedding.IsCaseTwoGroup 3 K := ⟨d, Or.inl ⟨rfl, hd⟩, ⟨e⟩⟩
  obtain ⟨ε⟩ := AGLEmbedding.KFactProofs.L28Local.nonempty_equiv_G8 hK
  have hcard : Nat.card K = 504 := by
    rw [Nat.card_congr ε.toEquiv]
    exact CFSG.Quasithin.F6.L28Res.card_G8
  have h3S : 3 ∣ Nat.card (S : Subgroup K) := S.dvd_card_of_dvd_card (by rw [hcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup K)) 3 h3S
  exact AGLEmbedding.kFactCaseTwoNoTwoL28 3 K ⟨rfl, d, hd, ⟨e⟩⟩ (t : K)
    (by rw [Subgroup.orderOf_coe]; exact ht) W hW (hnorm t t.2)

theorem twoSigTriv_sz32 {K : Type} [Group K]
    [Finite K] (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : TwoSigTriv 5 K := by
  intro S W hW hnorm
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, ⟨e⟩⟩
  have hcard : Nat.card K = 32537600 := (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso).card
  have h5S : 5 ∣ Nat.card (S : Subgroup K) := S.dvd_card_of_dvd_card (by rw [hcard]; norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup K)) 5 h5S
  exact AGLEmbedding.kFactCaseTwoNoTwoSz32 5 K ⟨rfl, ⟨_, hv⟩, rfl, ⟨e⟩⟩ (t : K)
    (by rw [Subgroup.orderOf_coe]; exact ht) W hW (hnorm t t.2)

section Tits


theorem twoSigTriv_tits_five {K : Type} [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : TwoSigTriv 5 K := by
  intro S W hW hnorm
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  refine RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial.signalizerTrivialTits_holds K ⟨hv, ⟨e⟩⟩ S W
    (coprime_card_of_isPGroup_two (by norm_num) (by norm_num) hW) fun g hg w hw => ?_
  exact (Subgroup.mem_normalizer_iff.1 (hnorm g hg) w).1 hw

end Tits

end CFSG.LocalAnalysis.UniquenessCase.UCK

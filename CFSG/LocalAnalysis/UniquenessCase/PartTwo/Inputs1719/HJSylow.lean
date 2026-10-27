module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12T1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatHolds

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup

theorem exists_conj_hjT1_of_sylow
    {Y T : Subgroup (MulAut W12)}
    (hLY : hjL0 ≤ Y) (hN : (hjL0.subgroupOf Y).Normal) (hTY : T ≤ Y)
    (hT : IsSylowIn 2 T Y) :
    ∃ g ∈ Subgroup.normalizer (hjL0 : Set (MulAut W12)),
      T = hjT1.map (MulAut.conj g).toMonoidHom ∨
        T = (hjT1 ⊓ hjL0).map (MulAut.conj g).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (MulAut W12) := MulEquiv.finite_left
  obtain ⟨-, hT0L, hT0T1, hT1N, hcardT0, hcardT1, -, -, -, -⟩ := hjT1_facts
  have hLcard : Nat.card hjL0 = 604800 := by
    obtain ⟨e⟩ := hjL0_isSpor
    exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hfac2 : (Nat.card hjL0).factorization 2 = 7 := by
    rw [hLcard]
    have h1 : 7 ≤ (604800 : ℕ).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).1
        (by norm_num : 2 ^ 7 ∣ (604800 : ℕ))
    have h2 : ¬ 8 ≤ (604800 : ℕ).factorization 2 := by
      intro h2
      exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (by norm_num)).2 h2) (by norm_num)
    omega
  let N : Subgroup (MulAut W12) := Subgroup.normalizer (hjL0 : Set (MulAut W12))
  have hLN : hjL0 ≤ N := Subgroup.le_normalizer
  have hT1N' : hjT1 ≤ N := hT1N
  have hNj : (hjL0.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2 le_rfl
  have hNcard : Nat.card N ∣ 6 * Nat.card hjL0 :=
    card_dvd_six_mul_of_normal hLN hNj
  have : Nonempty ↥N := ⟨1⟩
  have h2dvd : 2 ^ 8 ∣ Nat.card N := by
    rw [← hcardT1]
    exact Subgroup.card_dvd_of_le hT1N'
  have h2ndvd : ¬ 2 ^ 9 ∣ Nat.card N := by
    intro h
    have h' : 2 ^ 9 ∣ 6 * Nat.card hjL0 := h.trans hNcard
    rw [hLcard] at h'
    exact (by norm_num : ¬ 2 ^ 9 ∣ 6 * (604800 : ℕ)) h'
  have hfacN : (Nat.card N).factorization 2 = 8 := by
    have hge : 8 ≤ (Nat.card N).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h2dvd
    have hlt : (Nat.card N).factorization 2 < 9 := by
      by_contra h
      push Not at h
      exact h2ndvd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        Nat.card_pos.ne').2 h)
    omega
  have hT1sylN : IsSylowIn 2 hjT1 N :=
    isSylowIn_of_card_eq hT1N' (by rw [hcardT1, hfacN])
  have hYN : Y ≤ N := (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hN
  have hTN : T ≤ N := hTY.trans hYN
  have hTpg : IsPGroup 2 T := hT.isPGroup
  obtain ⟨S, hSsyl, hTS⟩ := exists_isSylowIn_ge 2 hTN hTpg
  obtain ⟨g, hgN, hSg⟩ := isSylowIn_exists_conj hT1sylN hSsyl
  have hcardS : Nat.card S = 2 ^ 8 := by
    rw [hSg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardT1]
  by_cases hbig : Nat.card T = 2 ^ 8
  · refine ⟨g, hgN, Or.inl ?_⟩
    have hTS' : T = S :=
      Subgroup.eq_of_le_of_card_ge hTS (by rw [hcardS, hbig])
    exact hTS'.trans hSg
  · refine ⟨g, hgN, Or.inr ?_⟩
    have hTsylL : IsSylowIn 2 (T ⊓ hjL0) hjL0 :=
      IsSylowIn.inf_normal hT hLY hN
    have hcard_infL : Nat.card ↥(T ⊓ hjL0) = 2 ^ 7 := by
      rw [IsSylowIn.card_eq hTsylL, hfac2]
    have hgeT : 2 ^ 7 ≤ Nat.card T := by
      rw [← hcard_infL]
      exact Subgroup.card_le_of_le inf_le_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hTpg
    have hcardT_le : Nat.card T ≤ 2 ^ 8 := by
      rw [← hcardS]
      exact Subgroup.card_le_of_le hTS
    have hn7 : n = 7 := by
      have hpow1 : 2 ^ 7 ≤ 2 ^ n := by
        rw [← hn]
        exact hgeT
      have hpow2 : 2 ^ n ≤ 2 ^ 8 := by
        rw [← hn]
        exact hcardT_le
      have h1 : 7 ≤ n :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 hpow1
      have h2 : n ≤ 8 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 hpow2
      have hne : n ≠ 8 := by
        intro h8
        exact hbig (by rw [hn, h8])
      omega
    have hTL : T ≤ hjL0 := by
      have heq : T ⊓ hjL0 = T :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hn, hn7, hcard_infL])
      exact heq ▸ inf_le_right
    have hT1pg : IsPGroup 2 hjT1 := hT1sylN.isPGroup
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 (hT1pg.to_inf_left (K := hjL0))
    have hupper : Nat.card ↥(hjT1 ⊓ hjL0) ≤ 2 ^ 7 := by
      have hdvd : 2 ^ m ∣ Nat.card hjL0 := by
        rw [← hm]
        exact Subgroup.card_dvd_of_le inf_le_right
      have hm7 : m ≤ 7 := by
        have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
          (by rw [hLcard]; norm_num)).1 hdvd
        rwa [hfac2] at h
      rw [hm]
      exact Nat.pow_le_pow_right (by norm_num) hm7
    have hlower : 2 ^ 7 ≤ Nat.card ↥(hjT1 ⊓ hjL0) := by
      rw [← hcardT0]
      exact Subgroup.card_le_of_le (le_inf hT0T1 hT0L)
    have hcardT1inf : Nat.card ↥(hjT1 ⊓ hjL0) = 2 ^ 7 :=
      le_antisymm hupper hlower
    have hconjL : hjL0.map (MulEquiv.toMonoidHom (MulAut.conj g)) = hjL0 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hgN
    have hmap_conj : (hjT1 ⊓ hjL0).map (MulAut.conj g).toMonoidHom =
        hjT1.map (MulAut.conj g).toMonoidHom ⊓ hjL0 := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hconjL]
    have hle_conj : T ≤ (hjT1 ⊓ hjL0).map (MulAut.conj g).toMonoidHom := by
      rw [hmap_conj]
      exact le_inf (hSg ▸ hTS) hTL
    have hcard_conj :
        Nat.card ↥((hjT1 ⊓ hjL0).map (MulAut.conj g).toMonoidHom) = 2 ^ 7 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcardT1inf]
    exact Subgroup.eq_of_le_of_card_ge hle_conj (by rw [hcard_conj, hn, hn7])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end

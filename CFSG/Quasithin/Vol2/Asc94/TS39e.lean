module

public import CFSG.Quasithin.Vol2.Asc94.TS39d

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_orbit_eq_ncard (L : Subgroup G) (s : G) (O : Set G)
    (hO : {x : G | ∃ l ∈ L, x = l⁻¹ * s * l} = O) :
    O.ncard * Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = Nat.card L := by
  have h := Gen.card_conjOrbit_mul_card_stab L s
  rw [← hO, ← Nat.card_coe_set_eq]
  exact h

theorem exists_normal_over {L : Type} [Group L] [Finite L] (A : Subgroup L) [A.Normal] {m : ℕ}
    (hm0 : 0 < m) (hpm : ¬ 31 ∣ m) (hdiv : ∀ d : ℕ, d ∣ m → d % 31 = 1 → d = 1)
    (hA : Nat.card A = 64) (hL : Nat.card L = 31 * 64 * m) :
    ∃ R : Subgroup L, R.Normal ∧ A ≤ R ∧ Nat.card R = 31 * 64 := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hq : Nat.card (L ⧸ A) * 64 = Nat.card L := by
    rw [← hA]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup A).symm
  have hq' : Nat.card (L ⧸ A) = 31 * m := by
    have : Nat.card (L ⧸ A) * 64 = 31 * m * 64 := by
      rw [hq, hL]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
  obtain ⟨P, hPn, hPc⟩ := Gen.exists_normal_of_card_mul hpm hq' hdiv
  refine ⟨P.comap (QuotientGroup.mk' A), hPn.comap _, ?_, ?_⟩
  · intro a ha
    show QuotientGroup.mk' A a ∈ P
    rw [show QuotientGroup.mk' A a = 1 from (QuotientGroup.eq_one_iff a).2 ha]
    exact P.one_mem
  · have h1 := Subgroup.card_mul_index (P.comap (QuotientGroup.mk' A))
    have h2 : (P.comap (QuotientGroup.mk' A)).index = P.index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective A)
    have h3 := Subgroup.card_mul_index P
    rw [hPc, hq'] at h3
    have h4 : P.index = m := Nat.eq_of_mul_eq_mul_left (by norm_num) h3
    rw [h2, h4, hL] at h1
    exact Nat.eq_of_mul_eq_mul_right hm0 h1

theorem Frame2.T_le_NA (F : Frame2 G z) : F.T ≤ F.NA := by
  haveI := Gen.normal_subgroupOf_of_conj F.A_normal
  exact fun t ht => ⟨F.T_le_H ht, Subgroup.le_normalizer_of_normal_subgroupOf F.A_le_T ht⟩

theorem Frame2.A_le_normalizer (F : Frame2 G z) : F.A ≤ Subgroup.normalizer (F.A : Set G) :=
  Subgroup.le_normalizer

theorem Frame2.card_NA (F : Frame2 G z) : ∃ k : ℕ, Nat.card ↥F.NA = 1024 * k ∧ k ∣ 21 := by
  have hdvd : Nat.card ↥F.NA ∣ 21504 := by
    rw [← F.card_H]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk⟩ : 1024 ∣ Nat.card ↥F.NA := by
    rw [← F.card_T]
    exact Subgroup.card_dvd_of_le F.T_le_NA
  refine ⟨k, hk, ?_⟩
  rw [hk] at hdvd
  have : 1024 * k ∣ 1024 * 21 := hdvd
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this

theorem Frame3.exists_R (F : Frame3 G z) (h31 : F.Sz.ncard = 31) :
    ∃ R : Subgroup G, R ≤ Subgroup.normalizer (F.A : Set G) ∧ F.A ≤ R ∧
      (∀ l ∈ Subgroup.normalizer (F.A : Set G), ∀ r ∈ R, l⁻¹ * r * l ∈ R) ∧
      Nat.card R = 31 * 64 := by
  obtain ⟨k, hk, hk21⟩ := F.card_NA
  set L : Subgroup G := Subgroup.normalizer (F.A : Set G) with hL
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have := Nat.card_pos (α := ↥F.NA)
      rw [hk, h] at this
      omega
    · exact h
  have hk21' : k ≤ 21 := Nat.le_of_dvd (by norm_num) hk21
  have hLc : Nat.card L = 31 * 64 * (16 * k) := by
    rw [hL, F.card_normalizer_A, h31, hk]
    ring
  haveI hAn : (F.A.subgroupOf L).Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ F.A := hn
    show ((g * n * g⁻¹ : ↥L) : G) ∈ F.A
    have := (Subgroup.mem_normalizer_iff.1 g.2 (n : G)).1 hn'
    simpa using this⟩
  have hAc : Nat.card (F.A.subgroupOf L) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe F.A_le_normalizer).toEquiv, F.card_A]
  have hpm : ¬ 31 ∣ 16 * k := by omega
  have hdiv : ∀ d : ℕ, d ∣ 16 * k → d % 31 = 1 → d = 1 := by
    intro d hd hmod
    have h336 : d ∣ 336 := hd.trans (by simpa using Nat.mul_dvd_mul_left 16 hk21)
    have hmem : d ∈ Nat.divisors 336 := Nat.mem_divisors.2 ⟨h336, by norm_num⟩
    have key : ∀ d ∈ Nat.divisors 336, d % 31 = 1 → d = 1 := by decide
    exact key d hmem hmod
  obtain ⟨R', hRn, hAR, hRc⟩ := exists_normal_over (F.A.subgroupOf L) (by omega) hpm hdiv hAc hLc
  refine ⟨R'.map L.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · intro a ha
    exact ⟨⟨a, F.A_le_normalizer ha⟩, hAR (by exact ha), rfl⟩
  · rintro l hl _ ⟨r, hr, rfl⟩
    refine ⟨⟨l, hl⟩⁻¹ * r * ⟨l, hl⟩, ?_, rfl⟩
    have := hRn.conj_mem r hr ⟨l, hl⟩⁻¹
    simpa using this
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hRc]

end CFSG.Quasithin.A94

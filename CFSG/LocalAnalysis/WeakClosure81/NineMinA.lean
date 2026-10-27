module

public import CFSG.Quasithin.Background.E1Sec3
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem oTwoPTwo_eq_top_of_unique_max {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X T N : Subgroup Q} (hX : IsPGroup p X) (hT : IsPGroup 2 T)
    (hXT : (X : Set Q) * (T : Set Q) = Set.univ) (hTN : T ≤ N) (hN : N ≠ ⊤)
    (hmax : ∀ L : Subgroup Q, T ≤ L → L ≠ ⊤ → L ≤ N) :
    E1.oTwoPTwo Q p = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype Q := Fintype.ofFinite Q
  have hdisj : Disjoint X T := IsPGroup.disjoint_of_ne p 2 hp2 X T hX hT
  have hcomp : X.IsComplement' T :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hXT
  have hcard : Nat.card X * Nat.card T = Nat.card Q := hcomp.card_mul_card
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  have hcardQ : Nat.card Q = p ^ a * 2 ^ b := by rw [← hcard, ha, hb]
  have hcardF : Fintype.card Q = p ^ a * 2 ^ b := by
    rw [← Nat.card_eq_fintype_card]
    exact hcardQ
  have hsolv : Group.IsSolvable Q :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp Nat.prime_two
      hp2 hcardF
  haveI : Group.IsSolvable Q := hsolv
  have hTsyl : IsSylowIn 2 T (⊤ : Subgroup Q) := by
    refine ⟨le_top, hT, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h2dvd
    have h := Subgroup.index_mul_card T
    rw [hb, hcardQ] at h
    have hTi : T.index = p ^ a :=
      Nat.mul_right_cancel (pow_pos (by norm_num) b) h
    have h2pa : 2 ∣ p ^ a := by rwa [hTi] at h2dvd
    have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2pa
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  haveI : Fintype (Subgroup Q) := Fintype.ofFinite _
  obtain ⟨F, -, hFmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun F : Subgroup Q => F.Normal ∧ ¬ F ≤ N) ⊤
    ⟨inferInstance, by simpa [top_le_iff] using hN⟩
  have hFnorm : F.Normal := hFmin.1.1
  have hFnotN : ¬ F ≤ N := hFmin.1.2
  haveI : F.Normal := hFnorm
  have hFmin_le : ∀ F' : Subgroup Q, F' < F → F'.Normal → F' ≤ N := by
    intro F' hlt hF'norm
    by_contra hne
    have hle : F' ≤ F := le_of_lt hlt
    exact (ne_of_lt hlt) (le_antisymm hle (hFmin.2 ⟨hF'norm, hne⟩ hle))
  have hFT : F ⊔ T = ⊤ := by
    by_contra hne
    have hle : F ⊔ T ≤ N := hmax (F ⊔ T) le_sup_right hne
    exact hFnotN (le_sup_left.trans hle)
  have hq : ∀ q : Q, ∃ k : ℕ, q ^ 2 ^ k ∈ F := by
    intro q
    have hqF : q ∈ F ⊔ T := by rw [hFT]; trivial
    rw [Subgroup.mem_sup_of_normal_left] at hqF
    obtain ⟨f, hf, t, ht, hft⟩ := hqF
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hf1 : QuotientGroup.mk' F f = 1 := (QuotientGroup.eq_one_iff (N := F) f).mpr hf
    have hqeq : QuotientGroup.mk' F q = QuotientGroup.mk' F t := by
      rw [← hft, map_mul, hf1, one_mul]
    have hmk : QuotientGroup.mk' F (q ^ 2 ^ k) = 1 := by
      rw [map_pow, hqeq, ← map_pow, hk', map_one]
    exact (QuotientGroup.eq_one_iff (N := F) (q ^ 2 ^ k)).mp hmk
  let Φ : Subgroup Q := sSup {F' : Subgroup Q | F' < F ∧ F'.Normal}
  have hΦmem : ∀ F' : Subgroup Q, F' < F → F'.Normal → F' ≤ Φ :=
    fun F' hlt hnorm => le_sSup ⟨hlt, hnorm⟩
  have hΦnorm : Φ.Normal := by
    apply Subgroup.sSup_normal
    rintro F' ⟨-, hnorm⟩
    exact hnorm
  haveI : Φ.Normal := hΦnorm
  have hΦleF : Φ ≤ F := by
    apply sSup_le
    rintro F' ⟨hlt, -⟩
    exact le_of_lt hlt
  have hΦleN : Φ ≤ N := by
    apply sSup_le
    rintro F' ⟨hlt, hnorm⟩
    exact hFmin_le F' hlt hnorm
  have hΦneF : Φ ≠ F := by
    intro h
    exact hFnotN (h ▸ hΦleN)
  have hΦltF : Φ < F := lt_of_le_of_ne hΦleF hΦneF
  have hchief : CFSG.IsChiefFactor Φ F :=
    { normal_K := hΦnorm
      normal_H := hFnorm
      lt := hΦltF
      is_maximal := by
        intro N' hN'norm hΦN' hN'F
        by_cases hN'F' : N' = F
        · exact Or.inr hN'F'
        · exact Or.inl
            (le_antisymm (hΦmem N' (lt_of_le_of_ne hN'F hN'F') hN'norm) hΦN') }
  let cf : CFSG.ChiefFactor Q := { V := Φ, U := F, isChief := hchief }
  obtain ⟨r, hrprime, hrEA⟩ :=
    CFSG.chiefFactor_quotient_exists_isElementaryAbelian (G := Q) hsolv cf
  haveI : Fact r.Prime := ⟨hrprime⟩
  haveI : CFSG.IsElementaryAbelian r (↥(F.map (QuotientGroup.mk' (Φ : Subgroup Q)))) := hrEA
  have hpow : ∀ x ∈ F, x ^ r ∈ Φ := by
    intro x hx
    have hxUq : QuotientGroup.mk' Φ x ∈ F.map (QuotientGroup.mk' (Φ : Subgroup Q)) :=
      Subgroup.mem_map_of_mem _ hx
    have h1 : QuotientGroup.mk' (Φ : Subgroup Q) (x ^ r) = 1 := by
      rw [map_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := r)
        (A := F.map (QuotientGroup.mk' (Φ : Subgroup Q)))
        (QuotientGroup.mk' Φ x) hxUq
    exact (QuotientGroup.eq_one_iff (N := Φ) (x ^ r)).mp h1
  have hUq_ne_bot : F.map (QuotientGroup.mk' Φ) ≠ ⊥ := by
    obtain ⟨x, hxF, hxnotΦ⟩ := SetLike.exists_of_lt hΦltF
    intro hbot
    have hxUq : QuotientGroup.mk' Φ x ∈ F.map (QuotientGroup.mk' Φ) :=
      Subgroup.mem_map_of_mem _ hxF
    rw [hbot, Subgroup.mem_bot] at hxUq
    exact hxnotΦ ((QuotientGroup.eq_one_iff (N := Φ) x).mp hxUq)
  have hrdvd : r ∣ p ^ a * 2 ^ b := by
    have h1 : Nat.card (F.map (QuotientGroup.mk' Φ)) ∣ Nat.card (Q ⧸ Φ) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (F.map (QuotientGroup.mk' Φ)) ∣ Nat.card Q :=
      h1.trans (Subgroup.index_dvd_card Φ)
    have hcard_ne : Nat.card (F.map (QuotientGroup.mk' Φ)) ≠ 1 :=
      fun h1c => hUq_ne_bot (Subgroup.card_eq_one.mp h1c)
    have hpgrp : IsPGroup r (F.map (QuotientGroup.mk' Φ)) :=
      CFSG.IsElementaryAbelian.isPGroup r ↥(F.map (QuotientGroup.mk' Φ))
    rcases hpgrp.card_eq_or_dvd with h | h
    · exact absurd h hcard_ne
    · rw [← hcardQ]
      exact h.trans h2
  have hr_eq : r = 2 ∨ r = p := by
    rcases hrprime.dvd_mul.mp hrdvd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hrprime hp).mp (hrprime.dvd_of_dvd_pow h))
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).mp
        (hrprime.dvd_of_dvd_pow h))
  have hrne2 : r ≠ 2 := by
    intro hr2
    have hpow2 : ∀ x ∈ F, x ^ 2 ∈ Φ := by
      intro x hx
      have := hpow x hx
      rwa [hr2] at this
    have hSF : IsSylowIn 2 (T ⊓ F) F := hTsyl.inf_normal le_top (inferInstance)
    have hmul : ∀ x ∈ F, ∃ s ∈ T ⊓ F, ∃ n ∈ Φ, x = s * n :=
      exists_mul_eq_of_pow_mem (p := 2) (D := F) (N := Φ) (S := T ⊓ F)
        (inferInstance : (Φ.subgroupOf F).Normal)
        (fun x hx => ⟨1, by simpa using hpow2 x hx⟩) hSF
    exact hFnotN (fun x hx => by
      obtain ⟨s, hs, n, hn, rfl⟩ := hmul x hx
      exact N.mul_mem (hTN hs.1) (hΦleN hn))
  have hrp : r = p := by
    rcases hr_eq with h | h
    · exact absurd h hrne2
    · exact h
  have hpowp : ∀ x ∈ F, x ^ p ∈ Φ := by
    intro x hx
    have := hpow x hx
    rwa [hrp] at this
  have hDΦ : IsSylowIn 2 (T ⊓ Φ) Φ := hTsyl.inf_normal le_top (inferInstance)
  have hfratt : Subgroup.normalizer ((T ⊓ Φ : Subgroup Q) : Set Q) ⊔ Φ = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (p := 2) hDΦ.toSylow
    rw [IsSylowIn.coe_toSylow, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_right] at h
    exact h
  have hTleNorm : T ≤ Subgroup.normalizer ((T ⊓ Φ : Subgroup Q) : Set Q) :=
    E1.le_normalizer_inf_of_le_normalizer (K := T) (N := Φ) (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hΦnorm]
      exact le_top)
  have hDnorm : (T ⊓ Φ).Normal := by
    by_contra hnot
    have hne : Subgroup.normalizer ((T ⊓ Φ : Subgroup Q) : Set Q) ≠ ⊤ :=
      fun h => hnot (Subgroup.normalizer_eq_top_iff.mp h)
    have hleN : Subgroup.normalizer ((T ⊓ Φ : Subgroup Q) : Set Q) ≤ N :=
      hmax _ hTleNorm hne
    have htop : (⊤ : Subgroup Q) ≤ N := by
      rw [← hfratt]
      exact sup_le hleN hΦleN
    exact hN (top_le_iff.mp htop)
  haveI : (T ⊓ Φ).Normal := hDnorm
  have hDindex_dvd : (T ⊓ Φ).relIndex Φ ∣ p ^ a * 2 ^ b := by
    rw [← hcardQ]
    exact (Subgroup.relIndex_dvd_index_of_le (inf_le_right : T ⊓ Φ ≤ Φ)).trans
      (Subgroup.index_dvd_card (T ⊓ Φ))
  have hDindex_odd : ¬ 2 ∣ (T ⊓ Φ).relIndex Φ := hDΦ.not_dvd_relIndex
  have hcop : Nat.Coprime ((T ⊓ Φ).relIndex Φ) (2 ^ b) :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hDindex_odd).symm.pow_right b
  have hDindex_dvd_p : (T ⊓ Φ).relIndex Φ ∣ p ^ a :=
    hcop.dvd_of_dvd_mul_right hDindex_dvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hDindex_dvd_p
  have hpowD : ∀ y ∈ Φ, ∃ j, y ^ p ^ j ∈ (T ⊓ Φ : Subgroup Q) := by
    intro y hy
    have hmem := E1.pow_relIndex_mem (P := T ⊓ Φ) (Z := Φ)
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hDnorm]; exact le_top) hy
    refine ⟨k, ?_⟩
    rwa [hk] at hmem
  have hp_series : ∀ x ∈ F, ∃ n, x ^ p ^ n ∈ (T ⊓ Φ : Subgroup Q) := by
    intro x hx
    obtain ⟨j, hj⟩ := hpowD (x ^ p) (hpowp x hx)
    refine ⟨j + 1, ?_⟩
    have hpow_eq : (x ^ p) ^ p ^ j = x ^ p ^ (j + 1) := by
      rw [← pow_mul, ← pow_succ']
    rw [← hpow_eq]
    exact hj
  exact E1.oTwoPTwo_eq_top_of_series (N₂ := T ⊓ Φ) (N₂p := F)
    (hT.to_le inf_le_left) hp_series hq

end CFSG.LocalAnalysis.WeakClosure81

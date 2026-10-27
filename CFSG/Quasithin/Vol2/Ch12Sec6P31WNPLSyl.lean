module

public import CFSG.Open.QuasithinDefs

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.NPLSyl

theorem not_two_dvd_index_inf {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.Open.quasithinIsSylowTwo T) :
    ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := by
  have hTodd : ¬ 2 ∣ T.index := hT.2
  have h1 : T.relIndex (T ⊔ L) * (T ⊔ L).index = T.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h2 : L.relIndex (T ⊔ L) * (T ⊔ L).index = L.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have h3 : (T ⊓ L).relIndex T * T.index = (T ⊓ L).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h4 : (T ⊓ L).relIndex L * L.index = (T ⊓ L).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have h5 : (T ⊓ L).relIndex T = L.relIndex T := by
    unfold Subgroup.relIndex
    rw [Subgroup.inf_subgroupOf_left]
  have h6 : L.relIndex T = L.relIndex (T ⊔ L) := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer hTL
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hTL
    unfold Subgroup.relIndex Subgroup.index
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T L hTL).toEquiv
  have hL : 0 < L.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := L))
  have key : (T ⊓ L).relIndex L = T.relIndex (T ⊔ L) := by
    apply Nat.eq_of_mul_eq_mul_right hL
    calc (T ⊓ L).relIndex L * L.index = (T ⊓ L).index := h4
      _ = (T ⊓ L).relIndex T * T.index := h3.symm
      _ = L.relIndex T * T.index := by rw [h5]
      _ = L.relIndex (T ⊔ L) * T.index := by rw [h6]
      _ = L.relIndex (T ⊔ L) * (T.relIndex (T ⊔ L) * (T ⊔ L).index) := by rw [h1]
      _ = T.relIndex (T ⊔ L) * (L.relIndex (T ⊔ L) * (T ⊔ L).index) := by ring
      _ = T.relIndex (T ⊔ L) * L.index := by rw [h2]
  have ha : ¬ 2 ∣ T.relIndex (T ⊔ L) := by
    intro h2a
    apply hTodd
    rw [← h1]
    exact h2a.mul_right _
  show ¬ 2 ∣ (T ⊓ L).relIndex L
  rw [key]
  exact ha

theorem two_pow_eq_64_of_mul {k m : ℕ} (h : 2 ^ k * m = 20160) (hm : ¬ 2 ∣ m) :
    2 ^ k = 64 := by
  have hk : k < 15 := by
    by_contra hk
    have h1 : (32768 : ℕ) ≤ 2 ^ k :=
      calc (32768 : ℕ) = 2 ^ 15 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ k ≤ 20160 := Nat.le_of_dvd (by norm_num) ⟨m, h.symm⟩
    omega
  interval_cases k <;> (try norm_num at h) <;> (try norm_num) <;> omega

theorem card_map_sylow {G A : Type} [Group G] [Finite G] [Group A] [Finite A] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.Open.quasithinIsSylowTwo T)
    (ψ : ↥L →* A) (hψ : Function.Surjective ψ) (hA : Nat.card A = 20160) :
    Nat.card (((T ⊓ L).subgroupOf L).map ψ) = 64 := by
  have hodd := not_two_dvd_index_inf hTL hT
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hT.1
  have hK : Nat.card ↥((T ⊓ L).subgroupOf L) ∣ 2 ^ n := by
    refine dvd_trans ?_ hn
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ L ≤ L)).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hS : Nat.card ↥(((T ⊓ L).subgroupOf L).map ψ) ∣ 2 ^ n :=
    dvd_trans (Subgroup.card_map_dvd (H := (T ⊓ L).subgroupOf L) ψ) hK
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hS
  have hmul := Subgroup.card_mul_index (H := ((T ⊓ L).subgroupOf L).map ψ)
  have hodd' : ¬ 2 ∣ (((T ⊓ L).subgroupOf L).map ψ).index := fun h =>
    hodd (dvd_trans h (Subgroup.index_map_dvd (H := (T ⊓ L).subgroupOf L) hψ))
  rw [hk, hA] at hmul
  rw [hk]
  exact two_pow_eq_64_of_mul hmul hodd'

theorem card_map_sup_le {G A : Type} [Group G] [Group A] [Finite G] {L P T : Subgroup G}
    (hPL : P ≤ L) (hPT : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G))
    (ψ : ↥L →* A) [Finite ↥L] [Finite A] :
    Nat.card ↥(((P.subgroupOf L) ⊔ ((T ⊓ L).subgroupOf L)).map ψ) ≤
      Nat.card ↥((P.subgroupOf L).map ψ) * Nat.card ↥(((T ⊓ L).subgroupOf L).map ψ) := by
  have hswap : ∀ t p : ↥L, t ∈ (T ⊓ L).subgroupOf L → p ∈ P.subgroupOf L →
      ∃ p' ∈ P.subgroupOf L, ∃ t' ∈ (T ⊓ L).subgroupOf L, t * p = p' * t' := by
    intro t p ht hp
    rw [Subgroup.mem_subgroupOf] at ht hp
    obtain ⟨htT, htL⟩ := Subgroup.mem_inf.1 ht
    have hmem : (t : G) * (p : G) ∈ (P : Set G) * (T : Set G) := by
      rw [hPT]
      exact Set.mul_mem_mul htT hp
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hmem
    have hyL : y ∈ L := by
      have hy' : y = x⁻¹ * ((t : G) * (p : G)) := by
        rw [← hxy, inv_mul_cancel_left]
      rw [hy']
      exact mul_mem (inv_mem (hPL hx)) (mul_mem htL p.2)
    refine ⟨⟨x, hPL hx⟩, ?_, ⟨y, hyL⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hx
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.2 ⟨hy, hyL⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hxy.symm
  let M : Subgroup ↥L :=
    { carrier := {z | ∃ p ∈ P.subgroupOf L, ∃ t ∈ (T ⊓ L).subgroupOf L, z = p * t}
      mul_mem' := by
        rintro _ _ ⟨p1, hp1, t1, ht1, rfl⟩ ⟨p2, hp2, t2, ht2, rfl⟩
        obtain ⟨p', hp', t', ht', heq⟩ := hswap t1 p2 ht1 hp2
        refine ⟨p1 * p', mul_mem hp1 hp', t' * t2, mul_mem ht' ht2, ?_⟩
        rw [show p1 * t1 * (p2 * t2) = p1 * (t1 * p2) * t2 by simp only [mul_assoc], heq]
        simp only [mul_assoc]
      one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨p, hp, t, ht, rfl⟩
        obtain ⟨p', hp', t', ht', heq⟩ := hswap t⁻¹ p⁻¹ (inv_mem ht) (inv_mem hp)
        exact ⟨p', hp', t', ht', by rw [mul_inv_rev]; exact heq⟩ }
  have hPM : P.subgroupOf L ≤ M := by
    intro p hp
    exact ⟨p, hp, 1, one_mem _, (mul_one p).symm⟩
  have hTM : (T ⊓ L).subgroupOf L ≤ M := by
    intro t ht
    exact ⟨1, one_mem _, t, ht, (one_mul t).symm⟩
  have hsup : P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L ≤ M := sup_le hPM hTM
  have hQ : (P.subgroupOf L).map ψ ≤ (P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ :=
    Subgroup.map_mono le_sup_left
  have hR : ((T ⊓ L).subgroupOf L).map ψ ≤ (P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ :=
    Subgroup.map_mono le_sup_right
  let f : ↥((P.subgroupOf L).map ψ) × ↥(((T ⊓ L).subgroupOf L).map ψ) →
      ↥((P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ) :=
    fun z => ⟨z.1.1 * z.2.1, mul_mem (hQ z.1.2) (hR z.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨p, hp, t, ht, rfl⟩ := hsup hx
    refine ⟨(⟨ψ p, Subgroup.mem_map.2 ⟨p, hp, rfl⟩⟩, ⟨ψ t, Subgroup.mem_map.2 ⟨t, ht, rfl⟩⟩), ?_⟩
    apply Subtype.ext
    simp [f, map_mul]
  calc Nat.card ↥((P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ)
      ≤ Nat.card (↥((P.subgroupOf L).map ψ) × ↥(((T ⊓ L).subgroupOf L).map ψ)) :=
        Nat.card_le_card_of_surjective f hf
    _ = Nat.card ↥((P.subgroupOf L).map ψ) * Nat.card ↥(((T ⊓ L).subgroupOf L).map ψ) :=
        Nat.card_prod _ _

theorem prime_dvd_20160 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hd : p ∣ 20160) :
    p = 5 ∨ p = 7 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [h] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1
    omega

theorem card_le_of_isPGroup {A : Type} [Group A] [Finite A] (hA : Nat.card A = 20160)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (H : Subgroup A) (hH : IsPGroup p H) :
    Nat.card H ≤ p := by
  haveI := Fact.mk hp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hH
  have hdvd : Nat.card H ∣ 20160 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [hA] at this
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · simp only [pow_zero] at hn
      omega
    · simp only [pow_one] at hn
      omega
  · exfalso
    have hpn : p ^ n ∣ 20160 := by
      rw [← hn]
      exact hdvd
    have h2 : p ^ 2 ∣ 20160 := dvd_trans (pow_dvd_pow p hn2) hpn
    have hp20 : p ∣ 20160 := dvd_trans (dvd_pow_self p two_ne_zero) h2
    rcases prime_dvd_20160 hp h5 hp20 with rfl | rfl <;> norm_num at h2

theorem closure_card_le {G A : Type} [Group G] [Finite G] [Group A] [Finite A] {L P T : Subgroup G}
    (hPL : P ≤ L) (hPT : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G))
    (hT : CFSG.Open.quasithinIsSylowTwo T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ψ : ↥L →* A) (hψ : Function.Surjective ψ) (hA : Nat.card A = 20160)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hPp : IsPGroup p (P.subgroupOf L))
    (x : ↥L) (hx : x ∈ P.subgroupOf L) :
    Nat.card ↥(Subgroup.closure (insert (ψ x) ((((T ⊓ L).subgroupOf L).map ψ : Subgroup A) : Set A)))
      ≤ p * 64 := by
  have hPpsub : IsPGroup p ↥((P.subgroupOf L).map ψ) := by
    obtain ⟨m, hm⟩ := isPGroup_iff_card_dvd_pow.1 hPp
    exact IsPGroup.of_card_dvd_pow (dvd_trans (Subgroup.card_map_dvd (H := P.subgroupOf L) ψ) hm)
  have hP : Nat.card ↥((P.subgroupOf L).map ψ) ≤ p := card_le_of_isPGroup hA hp h5 _ hPpsub
  have hS : Nat.card ↥(((T ⊓ L).subgroupOf L).map ψ) = 64 := card_map_sylow hTL hT ψ hψ hA
  have hZ := card_map_sup_le hPL hPT ψ
  have hcl : Subgroup.closure (insert (ψ x) ((((T ⊓ L).subgroupOf L).map ψ : Subgroup A) : Set A))
      ≤ (P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_sup_left hx, rfl⟩
    · rw [SetLike.mem_coe] at hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.mem_map.2 ⟨z, Subgroup.mem_sup_right hz, rfl⟩
  calc Nat.card ↥(Subgroup.closure (insert (ψ x) ((((T ⊓ L).subgroupOf L).map ψ : Subgroup A) : Set A)))
      ≤ Nat.card ↥((P.subgroupOf L ⊔ (T ⊓ L).subgroupOf L).map ψ) := Subgroup.card_le_of_le hcl
    _ ≤ Nat.card ↥((P.subgroupOf L).map ψ) * Nat.card ↥(((T ⊓ L).subgroupOf L).map ψ) := hZ
    _ = Nat.card ↥((P.subgroupOf L).map ψ) * 64 := by rw [hS]
    _ ≤ p * 64 := Nat.mul_le_mul hP le_rfl

end CFSG.Quasithin.H13.NPLSyl

end

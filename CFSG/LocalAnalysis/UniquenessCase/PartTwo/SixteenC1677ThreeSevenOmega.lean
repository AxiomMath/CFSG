module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214f
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_seven_omega_eq {M K T Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKM : K ≤ M) (hK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hTM : T ≤ M) (hYM : Y ≤ M)
    (hT2 : IsPGroup 2 T) (hYp : IsPGroup p Y) (hperm : Permutes Y T) (hYK : Y ⊓ K = ⊥)
    (hidx : Nat.card T ≤ 2 * Nat.card ↥(T ⊓ K)) :
    ∃ a ∈ F11.Omega1p 2 T,
      F11.Omega1p 2 T = Subgroup.zpowers a ⊔ (F11.Omega1p 2 T ⊓ pCoreOf 2 (Y ⊔ T)) := by
  let Ω := F11.Omega1p 2 T
  let N := Ω ⊓ pCoreOf 2 (Y ⊔ T)
  have hsup : (Y ⊔ T) ⊓ K = T ⊓ K := by
    apply le_antisymm
    · intro g hg
      have hg_sup : g ∈ Y ⊔ T := hg.1
      have hgK : g ∈ K := hg.2
      obtain ⟨y, hyY, t, htT, hg_eq⟩ := uc22p2214_mem_sup_of_permutes hperm hg_sup
      have hyM : y ∈ M := hYM hyY
      have htM : t ∈ M := hTM htT
      have hgM : g ∈ M := hKM hgK
      haveI : (K.subgroupOf M).Normal := ⟨by
        intro n hn m
        exact hK m.1 m.2 n.1 hn⟩
      let φ := QuotientGroup.mk' (K.subgroupOf M)
      have hφg : φ ⟨g, hgM⟩ = 1 := by
        exact (QuotientGroup.eq_one_iff (N := K.subgroupOf M) _).mpr hgK
      have hmul : φ ⟨y, hyM⟩ * φ ⟨t, htM⟩ = 1 := by
        have h_eq_m : (⟨y, hyM⟩ * ⟨t, htM⟩ : ↥M) = ⟨g, hgM⟩ := by
          ext
          simp [hg_eq]
        rw [← map_mul, h_eq_m, hφg]
      have hy_dvd : orderOf (φ ⟨y, hyM⟩) ∣ orderOf (⟨y, hyM⟩ : ↥M) :=
        orderOf_map_dvd φ _
      have ht_dvd : orderOf (φ ⟨t, htM⟩) ∣ orderOf (⟨t, htM⟩ : ↥M) :=
        orderOf_map_dvd φ _
      obtain ⟨k, hk⟩ := hYp ⟨y, hyY⟩
      obtain ⟨l, hl⟩ := hT2 ⟨t, htT⟩
      have hy_pow : orderOf (⟨y, hyM⟩ : ↥M) ∣ p ^ k := by
        have h1 : orderOf (⟨y, hyY⟩ : ↥Y) ∣ p ^ k :=
          orderOf_dvd_iff_pow_eq_one.mpr hk
        rw [Subgroup.orderOf_mk y hyY] at h1
        rwa [Subgroup.orderOf_mk y hyM]
      have ht_pow : orderOf (⟨t, htM⟩ : ↥M) ∣ 2 ^ l := by
        have h1 : orderOf (⟨t, htT⟩ : ↥T) ∣ 2 ^ l :=
          orderOf_dvd_iff_pow_eq_one.mpr hl
        rw [Subgroup.orderOf_mk t htT] at h1
        rwa [Subgroup.orderOf_mk t htM]
      have hp2cop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
      have hcop_pow : Nat.Coprime (p ^ k) (2 ^ l) := hp2cop.pow k l
      have hcop : Nat.Coprime (orderOf (φ ⟨y, hyM⟩)) (orderOf (φ ⟨t, htM⟩)) :=
        (hcop_pow.coprime_dvd_left (hy_dvd.trans hy_pow)).coprime_dvd_right
          (ht_dvd.trans ht_pow)
      have h_eq_inv : φ ⟨y, hyM⟩ = (φ ⟨t, htM⟩)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        exact hmul
      have horder_eq : orderOf (φ ⟨y, hyM⟩) = orderOf (φ ⟨t, htM⟩) := by
        rw [h_eq_inv, orderOf_inv]
      have hcop_self : Nat.Coprime (orderOf (φ ⟨y, hyM⟩))
          (orderOf (φ ⟨y, hyM⟩)) := by
        simpa [horder_eq] using hcop
      have horder_y : orderOf (φ ⟨y, hyM⟩) = 1 := by
        have hgcd : Nat.gcd (orderOf (φ ⟨y, hyM⟩))
            (orderOf (φ ⟨y, hyM⟩)) = 1 :=
          Nat.coprime_iff_gcd_eq_one.mp hcop_self
        rwa [Nat.gcd_self] at hgcd
      have hyK : y ∈ K := by
        have h1 : φ ⟨y, hyM⟩ = 1 := orderOf_eq_one_iff.mp horder_y
        exact (QuotientGroup.eq_one_iff (N := K.subgroupOf M) _).mp h1
      have htK : t ∈ K := by
        have hy1 : φ ⟨y, hyM⟩ = 1 := orderOf_eq_one_iff.mp horder_y
        have h1 : φ ⟨t, htM⟩ = 1 := by
          rw [← hmul, hy1, one_mul]
        exact (QuotientGroup.eq_one_iff (N := K.subgroupOf M) _).mp h1
      have hy_bot : y ∈ (⊥ : Subgroup G) := by
        rw [← hYK]
        exact ⟨hyY, hyK⟩
      have hy_eq_one : y = 1 := Subgroup.mem_bot.mp hy_bot
      have hg_eq_t : g = t := by
        rw [hg_eq, hy_eq_one, one_mul]
      rw [hg_eq_t]
      exact ⟨htT, htK⟩
    · intro x hx
      exact ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
  have hle : T ⊓ K ≤ pCoreOf 2 (Y ⊔ T) := by
    have hTKin : T ⊓ K ≤ Y ⊔ T := by
      intro x hx
      exact Subgroup.mem_sup_right hx.1
    have h2 : IsPGroup 2 ↥(T ⊓ K) := hT2.to_le inf_le_left
    have hnorm : ∀ x ∈ Y ⊔ T, ∀ y ∈ T ⊓ K, x * y * x⁻¹ ∈ T ⊓ K := by
      intro x hx y hy
      have hxM : x ∈ M := (sup_le hYM hTM) hx
      have hyK : y ∈ K := hy.2
      have hy_sup : y ∈ Y ⊔ T := Subgroup.mem_sup_right hy.1
      have hmem : x * y * x⁻¹ ∈ (Y ⊔ T) ⊓ K :=
        ⟨(Y ⊔ T).mul_mem ((Y ⊔ T).mul_mem hx hy_sup) ((Y ⊔ T).inv_mem hx),
          hK x hxM y hyK⟩
      rwa [hsup] at hmem
    exact uc22p21c_le_pCoreOf hTKin h2 hnorm
  have hΩ : Ω ≤ T := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    exact hx.1
  have hindex : (Ω ⊓ K).relIndex Ω ≤ 2 := by
    have h1 : (T ⊓ K).relIndex T ≤ 2 := by
      have hrel := Subgroup.relIndex_mul_card (H := T ⊓ K) (K := T)
      have hrel' : (T ⊓ K).relIndex T * Nat.card ↥(T ⊓ K) = Nat.card ↥T := by
        simpa only [inf_eq_left.mpr inf_le_left] using hrel
      have hpos : 0 < Nat.card ↥(T ⊓ K) := Nat.card_pos
      have hle2 : (T ⊓ K).relIndex T * Nat.card ↥(T ⊓ K) ≤
          2 * Nat.card ↥(T ⊓ K) := by
        rw [hrel']
        exact hidx
      exact Nat.le_of_mul_le_mul_right hle2 hpos
    have heq : (Ω ⊓ K).relIndex Ω = (T ⊓ K).relIndex Ω := by
      have h_eq_sub : Ω ⊓ K = (T ⊓ K) ⊓ Ω := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · intro hx; exact ⟨⟨hΩ hx.1, hx.2⟩, hx.1⟩
        · intro hx; exact ⟨hx.2, hx.1.2⟩
      rw [h_eq_sub, Subgroup.inf_relIndex_right]
    rw [heq]
    exact le_trans (Subgroup.relIndex_le_of_le_right (H := T ⊓ K) hΩ
      (Subgroup.index_ne_zero_of_finite)) h1
  have hcard : Nat.card Ω ≤ 2 * Nat.card N := by
    have h1 : (Ω ⊓ K).relIndex Ω * Nat.card ↥(Ω ⊓ K) = Nat.card Ω := by
      simpa only [inf_eq_left.mpr inf_le_left] using
        Subgroup.relIndex_mul_card (H := Ω ⊓ K) (K := Ω)
    have h2 : Nat.card ↥(Ω ⊓ K) ≤ Nat.card N := by
      apply Subgroup.card_le_of_le
      intro x hx
      exact ⟨hx.1, hle ⟨hΩ hx.1, hx.2⟩⟩
    calc
      Nat.card Ω = (Ω ⊓ K).relIndex Ω * Nat.card ↥(Ω ⊓ K) := h1.symm
      _ ≤ 2 * Nat.card ↥(Ω ⊓ K) := Nat.mul_le_mul_right _ hindex
      _ ≤ 2 * Nat.card N := Nat.mul_le_mul_left 2 h2
  by_cases hN : N = Ω
  · refine ⟨1, Ω.one_mem, ?_⟩
    change Ω = Subgroup.zpowers (1 : G) ⊔ N
    rw [hN]
    simp
  · have hnot_le : ¬ Ω ≤ N := by
      intro h
      exact hN (le_antisymm inf_le_left h)
    have hlt : N < Ω := lt_of_le_of_ne inf_le_left hN
    obtain ⟨a, haΩ, haN⟩ := SetLike.exists_of_lt hlt
    refine ⟨a, haΩ, ?_⟩
    have hQ_le : Subgroup.zpowers a ⊔ N ≤ Ω :=
      sup_le (Subgroup.zpowers_le_of_mem haΩ) inf_le_left
    have hQ_lt : N < Subgroup.zpowers a ⊔ N := by
      refine lt_of_le_of_ne le_sup_right ?_
      intro h
      have ha_sup : a ∈ Subgroup.zpowers a ⊔ N :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
      rw [← h] at ha_sup
      exact haN ha_sup
    have hcardQ : Nat.card N < Nat.card ↥(Subgroup.zpowers a ⊔ N) :=
      Subgroup.card_lt_of_lt hQ_lt
    have hdvd : Nat.card N ∣ Nat.card ↥(Subgroup.zpowers a ⊔ N) :=
      Subgroup.card_dvd_of_le le_sup_right
    obtain ⟨k, hk⟩ := hdvd
    have hk_ge : 2 ≤ k := by
      have h1 : 1 < k := by
        have h3 : Nat.card N * 1 < Nat.card N * k := by
          calc Nat.card N * 1 = Nat.card N := Nat.mul_one _
            _ < Nat.card ↥(Subgroup.zpowers a ⊔ N) := hcardQ
            _ = Nat.card N * k := hk
        exact Nat.lt_of_mul_lt_mul_left h3
      omega
    have hQ_eq : Nat.card ↥(Subgroup.zpowers a ⊔ N) = 2 * Nat.card N := by
      have h2N_le : 2 * Nat.card N ≤ Nat.card ↥(Subgroup.zpowers a ⊔ N) := by
        rw [hk, mul_comm 2 (Nat.card N)]
        exact Nat.mul_le_mul_left _ hk_ge
      have hle_Ω : Nat.card ↥(Subgroup.zpowers a ⊔ N) ≤ Nat.card Ω :=
        Subgroup.card_le_of_le hQ_le
      omega
    have hΩ_eq : Nat.card Ω = 2 * Nat.card N := by
      have h2N_le : 2 * Nat.card N ≤ Nat.card Ω := hQ_eq ▸ Subgroup.card_le_of_le hQ_le
      omega
    have hQ_eq_Ω : Subgroup.zpowers a ⊔ N = Ω := by
      apply Subgroup.eq_of_le_of_card_ge hQ_le
      rw [hΩ_eq, hQ_eq]
    exact hQ_eq_Ω.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

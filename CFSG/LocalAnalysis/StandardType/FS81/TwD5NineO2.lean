module

public import CFSG.GroupTheory.TwoReflections
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L5Iii
public import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.StandardType.FrameRoute.FS81

private lemma conj_decomp {G : Type} [Group G] {n α β j τ m : G}
    (hτ : τ * m * τ⁻¹ = m)
    (hα : Commute α (j * m * j⁻¹)) (hβ : Commute β (j * m * j⁻¹)) :
    (n * α * β * j * τ) * m * (n * α * β * j * τ)⁻¹ = n * (j * m * j⁻¹) * n⁻¹ := by
  have hαβ : Commute (α * β) (j * m * j⁻¹) := hα.mul_left hβ
  calc (n * α * β * j * τ) * m * (n * α * β * j * τ)⁻¹
      = n * (α * β) * (j * (τ * m * τ⁻¹) * j⁻¹) * (α * β)⁻¹ * n⁻¹ := by group
    _ = n * (α * β) * (j * m * j⁻¹) * (α * β)⁻¹ * n⁻¹ := by rw [hτ]
    _ = n * ((α * β) * (j * m * j⁻¹)) * (α * β)⁻¹ * n⁻¹ := by group
    _ = n * ((j * m * j⁻¹) * (α * β)) * (α * β)⁻¹ * n⁻¹ := by rw [hαβ.eq]
    _ = n * (j * m * j⁻¹) * n⁻¹ := by group

private theorem mem_normal_of_mul_mem_normal_of_two_pow {G : Type} [Group G]
    {N Y : Subgroup G} (hNY : N ≤ Y) (hYnorm : Y ≤ Subgroup.normalizer (N : Set G))
    {q n b t : G} (hn : n ∈ N) (hqY : q ∈ Y) (hbY : b ∈ Y) (htY : t ∈ Y)
    (hq : q = n * b * t) (hb3 : b ^ 3 = 1) (ht2 : t ^ 2 = 1) (hbt : b * t = t * b)
    (hq2 : ∃ s : ℕ, orderOf q ∣ 2 ^ s) : b ∈ N := by
  let Nsub : Subgroup Y := N.subgroupOf Y
  have hNsub : Nsub.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYnorm
  let φ : Y →* Y ⧸ Nsub := QuotientGroup.mk' Nsub
  let y : Y ⧸ Nsub := φ ⟨b, hbY⟩
  let z : Y ⧸ Nsub := φ ⟨t, htY⟩
  let x : Y ⧸ Nsub := φ ⟨q, hqY⟩
  have hqY_eq : (⟨q, hqY⟩ : Y) = ⟨n, hNY hn⟩ * ⟨b, hbY⟩ * ⟨t, htY⟩ := by
    ext
    exact hq
  have hn1 : φ ⟨n, hNY hn⟩ = 1 := by
    refine (QuotientGroup.eq_one_iff (N := Nsub) ⟨n, hNY hn⟩).mpr ?_
    exact Subgroup.mem_subgroupOf.mpr hn
  have hx_eq : x = y * z := by
    calc x = φ ⟨q, hqY⟩ := rfl
      _ = φ (⟨n, hNY hn⟩ * ⟨b, hbY⟩ * ⟨t, htY⟩) := by rw [hqY_eq]
      _ = φ ⟨n, hNY hn⟩ * φ ⟨b, hbY⟩ * φ ⟨t, htY⟩ := by rw [map_mul, map_mul]
      _ = y * z := by rw [hn1, one_mul]
  have hy3 : y ^ 3 = 1 := by
    have hbY3 : (⟨b, hbY⟩ : Y) ^ 3 = 1 := by
      ext
      simpa using hb3
    dsimp [y]
    rw [← map_pow, hbY3, map_one]
  have hz2 : z ^ 2 = 1 := by
    have htY2 : (⟨t, htY⟩ : Y) ^ 2 = 1 := by
      ext
      simpa using ht2
    dsimp [z]
    rw [← map_pow, htY2, map_one]
  have hyz : y * z = z * y := by
    have hbtY : (⟨b, hbY⟩ : Y) * ⟨t, htY⟩ = ⟨t, htY⟩ * ⟨b, hbY⟩ := by
      ext
      simpa using hbt
    dsimp [y, z]
    rw [← map_mul, ← map_mul, hbtY]
  obtain ⟨s, hs⟩ := hq2
  have hx2pow : ∃ k, orderOf x ∣ 2 ^ k := by
    refine ⟨s, ?_⟩
    have h1 : orderOf x ∣ orderOf (⟨q, hqY⟩ : Y) := by
      exact orderOf_map_dvd φ ⟨q, hqY⟩
    have h2 : orderOf (⟨q, hqY⟩ : Y) = orderOf q := (Subgroup.orderOf_coe _).symm
    exact h1.trans (by rw [h2]; exact hs)
  obtain ⟨s, hs⟩ := hx2pow
  have hx2 : x ^ 2 = y ^ 2 := by
    have hc : Commute y z := hyz
    rw [hx_eq, hc.mul_pow 2, hz2, mul_one]
  have hy2_pow : orderOf (y ^ 2) ∣ 2 ^ s := by
    rw [← hx2]
    exact (orderOf_pow_dvd (x := x) 2).trans hs
  have hy2_dvd3 : orderOf (y ^ 2) ∣ 3 :=
    (orderOf_pow_dvd (x := y) 2).trans (orderOf_dvd_of_pow_eq_one hy3)
  have hcop : Nat.Coprime 3 (2 ^ s) := by
    have h32 : Nat.Coprime 3 2 := by norm_num
    exact h32.pow_right s
  have hy2_order : orderOf (y ^ 2) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hy2_dvd3 hy2_pow
  have hy2 : y ^ 2 = 1 := orderOf_eq_one_iff.mp hy2_order
  have hy1 : y = 1 := by
    have h : y ^ 3 = y := by
      calc y ^ 3 = y ^ 2 * y := by rw [pow_succ]
        _ = 1 * y := by rw [hy2]
        _ = y := one_mul y
    rw [h] at hy3
    exact hy3
  have hbNsub : (⟨b, hbY⟩ : Y) ∈ Nsub := by
    refine (QuotientGroup.eq_one_iff (N := Nsub) ⟨b, hbY⟩).mp ?_
    simpa [y, φ] using hy1
  exact Subgroup.mem_subgroupOf.mp hbNsub

theorem le_zpowers_of_le_sup_simple {G : Type} [Group G] [Finite G] {t a b : G}
    {N J Q : Subgroup G} (ht : t ^ 2 = 1) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hN : Odd (Nat.card N)) (haN : a ∈ Subgroup.normalizer (N : Set G))
    (hbN : b ∈ Subgroup.normalizer (N : Set G)) (hJN : J ≤ Subgroup.normalizer (N : Set G))
    (htN : t ∈ Subgroup.normalizer (N : Set G)) (hab : a * b = b * a)
    (hJa : J ≤ Subgroup.centralizer ({a} : Set G)) (hJb : J ≤ Subgroup.centralizer ({b} : Set G))
    (hta : t * a * t⁻¹ = a⁻¹) (htb : t * b = b * t) (htJ : t ∈ Subgroup.normalizer (J : Set G))
    (hJ : IsSimpleGroup J) (hM : IsSimpleGroup ↥(J ⊓ Subgroup.centralizer ({t} : Set G)))
    (hM6 : 6 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({t} : Set G)))
    (hJM : J ⊓ Subgroup.centralizer
      ((J ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥)
    (hQ : IsPGroup 2 Q)
    (hQH : Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    (hHQ : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer (Q : Set G))
    (hH : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ≤
      N ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ J ⊔ Subgroup.zpowers t) :
    Q ≤ Subgroup.zpowers t := by
  let A : Subgroup G := Subgroup.zpowers a
  let B : Subgroup G := Subgroup.zpowers b
  let Tz : Subgroup G := Subgroup.zpowers t
  let Hsub : Subgroup G :=
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)
  let M : Subgroup G := J ⊓ Subgroup.centralizer ({t} : Set G)
  let L0 : Subgroup G := N ⊔ A
  let L1 : Subgroup G := L0 ⊔ B
  let K : Subgroup G := L1 ⊔ J
  let Y : Subgroup G := K ⊔ Tz
  have hH' : Hsub ≤ Y := hH
  have hA_normN : A ≤ Subgroup.normalizer (N : Set G) := by
    simpa [A] using (Subgroup.zpowers_le (g := a)
      (H := Subgroup.normalizer (N : Set G))).mpr haN
  have hB_normN : B ≤ Subgroup.normalizer (N : Set G) := by
    simpa [B] using (Subgroup.zpowers_le (g := b)
      (H := Subgroup.normalizer (N : Set G))).mpr hbN
  have hTz_normN : Tz ≤ Subgroup.normalizer (N : Set G) := by
    simpa [Tz] using (Subgroup.zpowers_le (g := t)
      (H := Subgroup.normalizer (N : Set G))).mpr htN
  have hb_normA : b ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq (x := b) (y := a) (by
      rw [← hab]
      group)
  have hB_normA : B ≤ Subgroup.normalizer (A : Set G) := by
    simpa [A, B] using (Subgroup.zpowers_le (g := b)
      (H := Subgroup.normalizer (A : Set G))).mpr hb_normA
  have hJ_normA : J ≤ Subgroup.normalizer (A : Set G) := by
    intro j hj
    have hcomm : j * a = a * j :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJa hj)
    simpa [A] using CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq (x := j) (y := a) (by
      rw [hcomm]
      group)
  have hJ_normB : J ≤ Subgroup.normalizer (B : Set G) := by
    intro j hj
    have hcomm : j * b = b * j :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJb hj)
    simpa [B] using CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq (x := j) (y := b) (by
      rw [hcomm]
      group)
  have htb' : t * b * t⁻¹ = b := by
    rw [htb]
    group
  have ht_normA : t ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
    CFSG.GroupTheory.mem_normalizer_zpowers_of_inv (x := t) (y := a) hta
  have ht_normB : t ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    CFSG.GroupTheory.mem_normalizer_zpowers_of_conj_eq (x := t) (y := b) htb'
  have hTz_normA : Tz ≤ Subgroup.normalizer (A : Set G) := by
    simpa [A, Tz] using (Subgroup.zpowers_le (g := t)
      (H := Subgroup.normalizer (A : Set G))).mpr ht_normA
  have hTz_normB : Tz ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B, Tz] using (Subgroup.zpowers_le (g := t)
      (H := Subgroup.normalizer (B : Set G))).mpr ht_normB
  have hTz_normJ : Tz ≤ Subgroup.normalizer (J : Set G) := by
    simpa [Tz] using (Subgroup.zpowers_le (g := t)
      (H := Subgroup.normalizer (J : Set G))).mpr htJ
  have hB_normL0 : B ≤ Subgroup.normalizer (L0 : Set G) := by
    have h := (le_inf hB_normN hB_normA).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N A)
    simpa [L0] using h
  have hJ_normL0 : J ≤ Subgroup.normalizer (L0 : Set G) := by
    have h := (le_inf hJN hJ_normA).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N A)
    simpa [L0] using h
  have hJ_normL1 : J ≤ Subgroup.normalizer (L1 : Set G) := by
    have h := (le_inf hJ_normL0 hJ_normB).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L0 B)
    simpa [L1] using h
  have hTz_normL0 : Tz ≤ Subgroup.normalizer (L0 : Set G) := by
    have h := (le_inf hTz_normN hTz_normA).trans
      (Subgroup.inf_normalizer_le_normalizer_sup N A)
    simpa [L0] using h
  have hTz_normL1 : Tz ≤ Subgroup.normalizer (L1 : Set G) := by
    have h := (le_inf hTz_normL0 hTz_normB).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L0 B)
    simpa [L1] using h
  have hTz_normK : Tz ≤ Subgroup.normalizer (K : Set G) := by
    have h := (le_inf hTz_normL1 hTz_normJ).trans
      (Subgroup.inf_normalizer_le_normalizer_sup L1 J)
    simpa [K] using h
  have hN_le_norm : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  have hL0_normN : L0 ≤ Subgroup.normalizer (N : Set G) := by
    simpa [L0] using (sup_le hN_le_norm hA_normN)
  have hL1_normN : L1 ≤ Subgroup.normalizer (N : Set G) := by
    simpa [L1] using (sup_le hL0_normN hB_normN)
  have hK_normN : K ≤ Subgroup.normalizer (N : Set G) := by
    simpa [K] using (sup_le hL1_normN hJN)
  have hY_normN : Y ≤ Subgroup.normalizer (N : Set G) := by
    simpa [Y] using (sup_le hK_normN hTz_normN)
  have hN_le_Y : N ≤ Y := by
    intro n hn
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hn)))
  have hA_le_Y : A ≤ Y := by
    intro x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)))
  have hB_le_Y : B ≤ Y := by
    intro x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  have hJ_le_Y : J ≤ Y := by
    intro x hx
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
  have hTz_le_Y : Tz ≤ Y := le_sup_right
  have hNnorm : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_Y).mpr hY_normN
  have hM_le_J : M ≤ J := inf_le_left
  have hM_le_H : M ≤ Hsub := by
    intro m hm
    rw [Subgroup.mem_inf] at hm ⊢
    exact ⟨hm.2, hJb hm.1⟩
  have hM_le_Y : M ≤ Y := hM_le_J.trans hJ_le_Y
  have hM_norm_N : M ≤ Subgroup.normalizer (N : Set G) := hM_le_J.trans hJN
  have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) := hM_le_H.trans hHQ
  have hJ_even : Even (Nat.card J) := by
    have h2M : 2 ∣ Nat.card M := dvd_trans (by norm_num : 2 ∣ 6) hM6
    exact even_iff_two_dvd.mpr (dvd_trans h2M (Subgroup.card_dvd_of_le hM_le_J))
  have hNJ : N ⊓ J = ⊥ := by
    have hnorm : ∀ k ∈ J, ∀ r ∈ N, k * r * k⁻¹ ∈ N := by
      intro k hk r hr
      exact (Subgroup.mem_normalizer_iff.mp (hJN hk) r).mp hr
    have h := CFSG.RankThree.PartTwo.Sec21.FF79.split_inf_eq_bot (K := J) (R := N)
      hJ hJ_even hN hnorm
    simpa [inf_comm] using h
  have hM_even : Even (Nat.card M) :=
    even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 6) hM6)
  have hNM : N ⊓ M = ⊥ := by
    have hnorm : ∀ k ∈ M, ∀ r ∈ N, k * r * k⁻¹ ∈ N := by
      intro k hk r hr
      exact (Subgroup.mem_normalizer_iff.mp (hM_norm_N hk) r).mp hr
    have h := CFSG.RankThree.PartTwo.Sec21.FF79.split_inf_eq_bot (K := M) (R := N)
      hM hM_even hN hnorm
    simpa [inf_comm] using h
  intro q hqQ
  have hqY : q ∈ Y := hH' (hQH hqQ)
  have hdecomp : ∃ n ∈ N, ∃ α ∈ A, ∃ β ∈ B, ∃ j ∈ J, ∃ τ ∈ Tz,
      q = n * α * β * j * τ := by
    obtain ⟨k, hkK, τ, hτTz, hq_eq⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := K) (K := Tz)
        hTz_normK).mp hqY
    obtain ⟨l, hlL1, j, hjJ, hk_eq⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := L1) (K := J)
        hJ_normL1).mp hkK
    obtain ⟨x, hxL0, β, hβB, hl_eq⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := L0) (K := B)
        hB_normL0).mp hlL1
    obtain ⟨n, hnN, α, hαA, hx_eq⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := N) (K := A)
        hA_normN).mp hxL0
    refine ⟨n, hnN, α, hαA, β, hβB, j, hjJ, τ, hτTz, ?_⟩
    calc q = k * τ := hq_eq
      _ = (l * j) * τ := by rw [hk_eq]
      _ = ((x * β) * j) * τ := by rw [hl_eq]
      _ = (((n * α) * β) * j) * τ := by rw [hx_eq]
  obtain ⟨n, hnN, α, hαA, β, hβB, j, hjJ, τ, hτTz, hq_eq⟩ := hdecomp
  have hQN : Q ⊓ N = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp hQ
    exact (hN.coprime_two_left.pow_left k).of_dvd_left hk
  have hqC_t : q ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.mem_inf.mp (hQH hqQ)).1
  have hq_t_comm : q * t = t * q :=
    Subgroup.mem_centralizer_singleton_iff.mp hqC_t
  have hqt : t * q * t⁻¹ = q := by
    rw [hq_t_comm.symm]
    group
  let Nsub : Subgroup Y := N.subgroupOf Y
  let φ : Y →* Y ⧸ Nsub := QuotientGroup.mk' Nsub
  have hstep : ∀ m ∈ M, j * m * j⁻¹ * m⁻¹ = 1 ∧ q * m * q⁻¹ * m⁻¹ = 1 := by
    intro m hm
    have hmJ : m ∈ J := (Subgroup.mem_inf.mp hm).1
    have hmC_t : m ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hm).2
    have hm_t_comm : m * t = t * m :=
      Subgroup.mem_centralizer_singleton_iff.mp hmC_t
    let w : G := j * m * j⁻¹
    have hwJ : w ∈ J := J.mul_mem (J.mul_mem hjJ hmJ) (J.inv_mem hjJ)
    have hwY : w ∈ Y := hJ_le_Y hwJ
    have hτm : τ * m * τ⁻¹ = m := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτTz
      have hcomm : Commute (t ^ k) m :=
        (show Commute t m from hm_t_comm.symm).zpow_left k
      rw [hcomm.eq]
      group
    have hαw : Commute α w := by
      have haw : Commute a w :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hJa hwJ)).symm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hαA
      exact haw.zpow_left k
    have hβw : Commute β w := by
      have hbw : Commute b w :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hJb hwJ)).symm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβB
      exact hbw.zpow_left k
    have hqmq : q * m * q⁻¹ = n * w * n⁻¹ := by
      rw [hq_eq]
      exact conj_decomp (n := n) (α := α) (β := β) (j := j) (τ := τ) (m := m)
        hτm hαw hβw
    let y : G := w * m⁻¹
    let ν : G := n * (w * n⁻¹ * w⁻¹)
    have hyJ : y ∈ J := J.mul_mem hwJ (J.inv_mem hmJ)
    have hyY : y ∈ Y := hJ_le_Y hyJ
    have hνN : ν ∈ N := by
      have hconj : w * n⁻¹ * w⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hY_normN hwY) n⁻¹).mp (N.inv_mem hnN)
      exact N.mul_mem hnN hconj
    have hcomm_eq : q * m * q⁻¹ * m⁻¹ = ν * y := by
      rw [hqmq]
      dsimp [w, y, ν]
      group
    have hmt : t * m * t⁻¹ = m := by
      rw [hm_t_comm.symm]
      group
    have hfix : t * (q * m * q⁻¹ * m⁻¹) * t⁻¹ = q * m * q⁻¹ * m⁻¹ := by
      calc t * (q * m * q⁻¹ * m⁻¹) * t⁻¹
          = (t * q * t⁻¹) * (t * m * t⁻¹) * (t * q⁻¹ * t⁻¹) * (t * m⁻¹ * t⁻¹) := by
            group
        _ = q * m * q⁻¹ * m⁻¹ := by
          rw [hqt, hmt,
            show t * q⁻¹ * t⁻¹ = (t * q * t⁻¹)⁻¹ by rw [conj_inv],
            show t * m⁻¹ * t⁻¹ = (t * m * t⁻¹)⁻¹ by rw [conj_inv],
            hqt, hmt]
    have hνtN : t * ν * t⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp htN ν).mp hνN
    have hytJ : t * y * t⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp htJ y).mp hyJ
    have hfix' : (t * ν * t⁻¹) * (t * y * t⁻¹) = ν * y := by
      have h := hfix
      rw [hcomm_eq] at h
      calc (t * ν * t⁻¹) * (t * y * t⁻¹) = t * (ν * y) * t⁻¹ := by group
        _ = ν * y := h
    have hEq : ν⁻¹ * (t * ν * t⁻¹) = y * (t * y * t⁻¹)⁻¹ := by
      calc ν⁻¹ * (t * ν * t⁻¹)
          = ν⁻¹ * ((t * ν * t⁻¹) * (t * y * t⁻¹)) * (t * y * t⁻¹)⁻¹ := by
            group
        _ = ν⁻¹ * (ν * y) * (t * y * t⁻¹)⁻¹ := by rw [hfix']
        _ = y * (t * y * t⁻¹)⁻¹ := by group
    have hleftN : ν⁻¹ * (t * ν * t⁻¹) ∈ N :=
      N.mul_mem (N.inv_mem hνN) hνtN
    have hrightJ : y * (t * y * t⁻¹)⁻¹ ∈ J :=
      J.mul_mem hyJ (J.inv_mem hytJ)
    have hleft1 : ν⁻¹ * (t * ν * t⁻¹) = 1 := by
      have hmem : ν⁻¹ * (t * ν * t⁻¹) ∈ N ⊓ J :=
        ⟨hleftN, by rw [hEq]; exact hrightJ⟩
      rw [hNJ] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hright1 : y * (t * y * t⁻¹)⁻¹ = 1 := by
      rw [← hEq, hleft1]
    have hyfix : t * y * t⁻¹ = y := by
      have h3 : (t * y * t⁻¹)⁻¹ = y⁻¹ := by
        calc (t * y * t⁻¹)⁻¹ = y⁻¹ * (y * (t * y * t⁻¹)⁻¹) := by group
          _ = y⁻¹ * 1 := by rw [hright1]
          _ = y⁻¹ := mul_one _
      simpa using congrArg Inv.inv h3
    have hyt : y * t = t * y := by
      calc y * t = (t * y * t⁻¹) * t := by rw [hyfix]
        _ = t * y := by group
    have hyM : y ∈ M :=
      ⟨hyJ, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩
    have hmQnorm : m ∈ Subgroup.normalizer (Q : Set G) := hHQ (hM_le_H hm)
    have hmqQ : m * q⁻¹ * m⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hmQnorm q⁻¹).mp (Q.inv_mem hqQ)
    have hcommQ : q * m * q⁻¹ * m⁻¹ ∈ Q := by
      have h := Q.mul_mem hqQ hmqQ
      simpa [mul_assoc] using h
    have hcommNM : q * m * q⁻¹ * m⁻¹ ∈ N ⊔ M := by
      rw [hcomm_eq]
      exact (N ⊔ M).mul_mem (Subgroup.mem_sup_left hνN) (Subgroup.mem_sup_right hyM)
    let P : Subgroup G := Q ⊓ (N ⊔ M)
    have hcommP : q * m * q⁻¹ * m⁻¹ ∈ P := ⟨hcommQ, hcommNM⟩
    have hM_norm_NM : M ≤ Subgroup.normalizer ((N ⊔ M : Subgroup G) : Set G) :=
      (le_sup_right : M ≤ N ⊔ M).trans Subgroup.le_normalizer
    have hM_normP : M ≤ Subgroup.normalizer (P : Set G) := by
      have h := (le_inf hM_norm_Q hM_norm_NM).trans
        (Subgroup.inf_normalizer_le_normalizer_inf)
      simpa [P] using h
    let NP : Subgroup G := N ⊔ P
    have hM_normNP : M ≤ Subgroup.normalizer (NP : Set G) := by
      have h := (le_inf hM_norm_N hM_normP).trans
        (Subgroup.inf_normalizer_le_normalizer_sup N P)
      simpa [NP] using h
    have hM_le_norm_MinfNP : M ≤ Subgroup.normalizer ((M ⊓ NP : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer hM_normNP).trans
        (Subgroup.inf_normalizer_le_normalizer_inf)
    have hMinfNP : ((M ⊓ NP).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := M ⊓ NP) (K := M)
        inf_le_left).mpr hM_le_norm_MinfNP
    have hMNP_bot : M ⊓ NP = ⊥ := by
      have hMsimp : IsSimpleGroup ↥M := hM
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ NP).subgroupOf M) with
        hbot | htop
      · have hEq2 : (M ⊓ NP).subgroupOf M = (⊥ : Subgroup G).subgroupOf M := by
          rw [hbot, Subgroup.bot_subgroupOf]
        rw [Subgroup.subgroupOf_inj] at hEq2
        simpa using hEq2
      · exfalso
        have hMleMinfNP : M ≤ M ⊓ NP := Subgroup.subgroupOf_eq_top.mp htop
        have hMleNP : M ≤ NP := hMleMinfNP.trans (inf_le_right : M ⊓ NP ≤ NP)
        have hP_le_Y : P ≤ Y := by
          have h := (inf_le_left : P ≤ Q).trans (hQH.trans hH')
          simpa [P] using h
        have hP_normN : P ≤ Subgroup.normalizer (N : Set G) := by
          have h := (inf_le_left : P ≤ Q).trans (hQH.trans (hH'.trans hY_normN))
          simpa [P] using h
        have hP2 : IsPGroup 2 P := IsPGroup.to_le hQ (inf_le_left : P ≤ Q)
        have hPsub2 : IsPGroup 2 (P.subgroupOf Y) :=
          IsPGroup.of_equiv hP2 (Subgroup.subgroupOfEquivOfLe hP_le_Y).symm
        have hPsub_map2 : IsPGroup 2 ((P.subgroupOf Y).map φ) :=
          IsPGroup.map hPsub2 φ
        have hM2 : IsPGroup 2 M := by
          intro x
          obtain ⟨n0, hn0N, p0, hp0P, hx_eq⟩ :=
            (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := N) (K := P)
              hP_normN).mp (hMleNP x.2)
          have hn01 : φ ⟨n0, hN_le_Y hn0N⟩ = 1 :=
            (QuotientGroup.eq_one_iff (N := N.subgroupOf Y) ⟨n0, hN_le_Y hn0N⟩).mpr
              (Subgroup.mem_subgroupOf.mpr hn0N)
          have hφx : φ ⟨(x : G), hM_le_Y x.2⟩ = φ ⟨p0, hP_le_Y hp0P⟩ := by
            have hxYeq : (⟨(x : G), hM_le_Y x.2⟩ : Y) =
                ⟨n0, hN_le_Y hn0N⟩ * ⟨p0, hP_le_Y hp0P⟩ := Subtype.ext hx_eq
            rw [hxYeq, map_mul, hn01, one_mul]
          have hx_mem : φ ⟨(x : G), hM_le_Y x.2⟩ ∈ (P.subgroupOf Y).map φ := by
            rw [hφx]
            exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hp0P)
          obtain ⟨k, hk⟩ := hPsub_map2 ⟨_, hx_mem⟩
          have hk' : (φ ⟨(x : G), hM_le_Y x.2⟩) ^ 2 ^ k = 1 := by
            simpa using congrArg Subtype.val hk
          refine ⟨k, Subtype.ext ?_⟩
          have hker : (⟨(x : G), hM_le_Y x.2⟩ : Y) ^ 2 ^ k ∈ N.subgroupOf Y := by
            refine (QuotientGroup.eq_one_iff (N := N.subgroupOf Y) _).mp ?_
            change φ ((⟨(x : G), hM_le_Y x.2⟩ : Y) ^ 2 ^ k) = 1
            rw [map_pow]
            exact hk'
          have hmemN : (x : G) ^ 2 ^ k ∈ N := by
            have h := Subgroup.mem_subgroupOf.mp hker
            simpa using h
          have hmemM : (x : G) ^ 2 ^ k ∈ M := M.pow_mem x.2 (2 ^ k)
          have hmemBot : (x : G) ^ 2 ^ k ∈ M ⊓ N := ⟨hmemM, hmemN⟩
          rw [inf_comm, hNM] at hmemBot
          exact Subgroup.mem_bot.mp hmemBot
        obtain ⟨k, hcard⟩ := IsPGroup.exists_card_eq hM2
        have h3dvd : 3 ∣ Nat.card M := dvd_trans (by norm_num : 3 ∣ 6) hM6
        rw [hcard] at h3dvd
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)
    have hyNP : y ∈ NP := by
      have hy_eq : y = ν⁻¹ * (q * m * q⁻¹ * m⁻¹) := by
        rw [hcomm_eq]
        group
      rw [hy_eq]
      exact NP.mul_mem (Subgroup.mem_sup_left (N.inv_mem hνN))
        (Subgroup.mem_sup_right hcommP)
    have hy1 : y = 1 := by
      have hmem : y ∈ M ⊓ NP := ⟨hyM, hyNP⟩
      rw [hMNP_bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hcomm_eq1 : q * m * q⁻¹ * m⁻¹ = ν := by
      rw [hcomm_eq, hy1, mul_one]
    have hcomm1 : q * m * q⁻¹ * m⁻¹ = 1 := by
      have hmem : q * m * q⁻¹ * m⁻¹ ∈ Q ⊓ N :=
        ⟨hcommQ, by rw [hcomm_eq1]; exact hνN⟩
      rw [hQN] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact ⟨hy1, hcomm1⟩
  have hjC : j ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hy1 : j * m * j⁻¹ * m⁻¹ = 1 := (hstep m hm).1
    have h : j * m = m * j := by
      calc j * m = (j * m * j⁻¹ * m⁻¹) * (m * j) := by group
        _ = 1 * (m * j) := by rw [hy1]
        _ = m * j := one_mul _
    exact h.symm
  have hj1 : j = 1 := by
    have hmem : j ∈ J ⊓ Subgroup.centralizer ((M : Subgroup G) : Set G) := ⟨hjJ, hjC⟩
    rw [hJM] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hq_eq2 : q = n * α * β * τ := by
    rw [hq_eq, hj1, mul_one]
  have hαinv : t * α * t⁻¹ = α⁻¹ :=
    CFSG.GroupTheory.inverted_zpowers_of_inv (x := t) (y := a) hta α hαA
  have hβfix : t * β * t⁻¹ = β := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβB
    rw [← conj_zpow, htb']
  have hτfix : t * τ * t⁻¹ = τ := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτTz
    rw [← conj_zpow, show t * t * t⁻¹ = t from by group]
  have hexp : t * q * t⁻¹ = (t * n * t⁻¹) * α⁻¹ * β * τ := by
    rw [hq_eq2]
    calc t * (n * α * β * τ) * t⁻¹
        = (t * n * t⁻¹) * (t * α * t⁻¹) * (t * β * t⁻¹) * (t * τ * t⁻¹) := by
          group
      _ = (t * n * t⁻¹) * α⁻¹ * β * τ := by rw [hαinv, hβfix, hτfix]
  have hEq5 : (t * n * t⁻¹) * α⁻¹ * β * τ = n * α * β * τ := by
    rw [← hexp, hqt, hq_eq2]
  have hEq6 : (t * n * t⁻¹) * α⁻¹ = n * α := by
    have h := hEq5
    rw [show (t * n * t⁻¹) * α⁻¹ * β * τ = ((t * n * t⁻¹) * α⁻¹) * (β * τ) by
          group,
        show n * α * β * τ = (n * α) * (β * τ) by group] at h
    exact mul_right_cancel h
  have hα2N : α ^ 2 ∈ N := by
    have h' : n⁻¹ * (t * n * t⁻¹) = α ^ 2 := by
      calc n⁻¹ * (t * n * t⁻¹)
          = (n⁻¹ * ((t * n * t⁻¹) * α⁻¹)) * α := by group
        _ = (n⁻¹ * (n * α)) * α := by rw [hEq6]
        _ = α ^ 2 := by rw [pow_two]; group
    rw [← h']
    exact N.mul_mem (N.inv_mem hnN) ((Subgroup.mem_normalizer_iff.mp htN n).mp hnN)
  have hα3 : α ^ 3 = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp
      ((orderOf_dvd_of_mem_zpowers hαA).trans (orderOf_dvd_of_pow_eq_one ha))
  have hαN : α ∈ N := by
    have hα4 : α ^ 4 = α := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hα3, one_mul, pow_one]
    have hαeq : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, hα4]
    have h := N.pow_mem hα2N 2
    rwa [hαeq] at h
  let n' : G := n * α
  have hn'N : n' ∈ N := N.mul_mem hnN hαN
  have hq_eq3 : q = n' * β * τ := by
    rw [hq_eq2]
  obtain ⟨s, hs⟩ := isPGroup_iff_orderOf_dvd_pow.mp hQ ⟨q, hqQ⟩
  have hq2 : ∃ s, orderOf q ∣ 2 ^ s := by
    refine ⟨s, ?_⟩
    simpa using hs
  have hβ3 : β ^ 3 = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp
      ((orderOf_dvd_of_mem_zpowers hβB).trans (orderOf_dvd_of_pow_eq_one hb))
  have hτ2 : τ ^ 2 = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp
      ((orderOf_dvd_of_mem_zpowers hτTz).trans (orderOf_dvd_of_pow_eq_one ht))
  have hβτ : β * τ = τ * β := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτTz
    exact ((show Commute b t from htb.symm).zpow_zpow i k).eq
  have hβN : β ∈ N :=
    mem_normal_of_mul_mem_normal_of_two_pow hN_le_Y hY_normN hn'N hqY
      (hB_le_Y hβB) (hTz_le_Y hτTz) hq_eq3 hβ3 hτ2 hβτ hq2
  have hqτ_eq : q * τ⁻¹ = n' * β := by
    rw [hq_eq3]
    group
  have hn'βN : n' * β ∈ N := N.mul_mem hn'N hβN
  have hqτ2 : ∃ k, orderOf (q * τ⁻¹) ∣ 2 ^ k := by
    obtain ⟨s, hs⟩ := hq2
    have hτ_comm : Commute τ q := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτTz
      exact (show Commute t q from hq_t_comm.symm).zpow_left k
    have hqτ_comm : Commute q τ := hτ_comm.symm
    have hqpow : q ^ 2 ^ (s + 1) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp
        (hs.trans (pow_dvd_pow 2 (Nat.le_succ s)))
    have hτpow : τ ^ 2 ^ (s + 1) = 1 := by
      rw [show 2 ^ (s + 1) = 2 * 2 ^ s by rw [pow_succ]; ring,
        pow_mul, hτ2, one_pow]
    have hτinvpow : (τ⁻¹) ^ 2 ^ (s + 1) = 1 := by
      rw [inv_pow, hτpow, inv_one]
    have hprod : (q * τ⁻¹) ^ 2 ^ (s + 1) = 1 := by
      rw [hqτ_comm.inv_right.mul_pow, hqpow, hτinvpow, one_mul]
    exact ⟨s + 1, orderOf_dvd_of_pow_eq_one hprod⟩
  obtain ⟨k, hk⟩ := hqτ2
  have hn'β_order2 : orderOf (n' * β) ∣ 2 ^ k := by
    rw [← hqτ_eq]
    exact hk
  have hn'β_order : orderOf (n' * β) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((hN.coprime_two_left).pow_left k)
      hn'β_order2 (Subgroup.orderOf_dvd_natCard N hn'βN)
  have hn'β : n' * β = 1 := orderOf_eq_one_iff.mp hn'β_order
  have hqτ1 : q * τ⁻¹ = 1 := by
    rw [hqτ_eq, hn'β]
  have hq_final : q = τ := by
    calc q = (q * τ⁻¹) * τ := by group
      _ = 1 * τ := by rw [hqτ1]
      _ = τ := one_mul τ
  rw [hq_final]
  exact hτTz


end CFSG.StandardType.FrameRoute.FS81

end

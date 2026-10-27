module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma14Key
public import CFSG.RankThree.GF2n.Parrott.A1ModelNoZ4Q8

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P S K : Subgroup G} (hS : IsSylowOf p S K)
    (hPK : P ≤ K) (hP : IsPGroup p P) : Nat.card P ≤ Nat.card S := by
  have hPsub : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hPQ⟩ := hPsub.exists_le_sylow
  have h1 : Nat.card P = Nat.card (P.subgroupOf K) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv).symm
  rw [h1, hS.card_eq, ← Sylow.card_eq_multiplicity Q]
  exact Subgroup.card_le_of_le hPQ

theorem CJ_conj_eq_of_mem_normalizer {g σ : G} (hg : g ∈ H z)
    (hn : g ∈ Subgroup.normalizer (CJ z σ : Set G)) : CJ z (g * σ * g⁻¹) = CJ z σ := by
  ext a
  have key : a ∈ CJ z (g * σ * g⁻¹) ↔ g⁻¹ * a * g ∈ CJ z σ := by
    rw [mem_CJ, mem_CJ, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc g⁻¹ * a * g * σ = g⁻¹ * (a * (g * σ * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * σ * g⁻¹) * a) * g := by rw [h1]
          _ = σ * (g⁻¹ * a * g) := by group
      · have := conj_mem_J ((H z).inv_mem hg) h2
        simpa using this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc a * (g * σ * g⁻¹) = g * ((g⁻¹ * a * g) * σ) * g⁻¹ := by group
          _ = g * (σ * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
          _ = g * σ * g⁻¹ * a := by group
      · have := conj_mem_J hg h2
        have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
        rwa [e] at this
  rw [key, Subgroup.mem_normalizer_iff.mp hn (g⁻¹ * a * g)]
  have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
  rw [e]

section Core

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

theorem card_le_of_le_centralizer_ut
    (hA1 : Tim79a.ParrottHypA1 z) {S : Subgroup G} (hSH : S ≤ H z) {x : G} (hxH : x ∈ H z)
    (hxq : qHP D ⟨x, hxH⟩ =
      (⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup))
    (hSx : S ≤ Subgroup.centralizer ({x} : Set G)) (hS2 : IsPGroup 2 S) :
    Nat.card S ≤ 2 ^ 14 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥S →* ↥QP45.originalSubgroup := (qHP D).comp (Subgroup.inclusion hSH)
  have hker : Nat.card φ.ker ≤ 2 ^ 9 := by
    have hle : φ.ker.map S.subtype ≤ J z := by
      rintro _ ⟨y, hy, rfl⟩
      have hk : Subgroup.inclusion hSH y ∈ (qHP D).ker := hy
      rw [ker_qHP] at hk
      exact Subgroup.mem_subgroupOf.mp hk
    have h := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective S.subtype_injective, hA1.card_J] at h
  have hle : φ.range ≤ Subgroup.centralizer
      ({(⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup)} :
        Set ↥QP45.originalSubgroup) := by
    intro g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxq]
    have hyx : Subgroup.inclusion hSH y * ⟨x, hxH⟩ = ⟨x, hxH⟩ * Subgroup.inclusion hSH y :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hSx y.2))
    have h := congrArg (qHP D) hyx
    rw [map_mul, map_mul] at h
    exact h
  have hdvd : Nat.card φ.range ∣ 96 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [qp45_card_centralizer_ut] at h
  have hp : IsPGroup 2 φ.range := hS2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hn5 : n ≤ 5 := by
    by_contra hcon
    have h64 : (64 : ℕ) ∣ 96 := by
      have h64n : (64 : ℕ) ∣ 2 ^ n := by
        rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
        exact Nat.pow_dvd_pow 2 (by omega)
      exact h64n.trans (by rw [← hn]; exact hdvd)
    omega
  have hrange : Nat.card φ.range ≤ 2 ^ 5 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) hn5
  have h := Subgroup.card_ker_mul_card_range φ
  calc Nat.card S = Nat.card φ.ker * Nat.card φ.range := h.symm
    _ ≤ 2 ^ 9 * 2 ^ 5 := Nat.mul_le_mul hker hrange
    _ = 2 ^ 14 := by norm_num

include D in
theorem exists_two_subgroup_H (hA1 : Tim79a.ParrottHypA1 z) :
    ∃ T : Subgroup G, T ≤ H z ∧ IsPGroup 2 T ∧ Nat.card T = 2 ^ 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ct := Subgroup.centralizer ({(⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup)} :
    Set ↥QP45.originalSubgroup) with hCt
  have hCt576 : Nat.card Ct = 576 := qp45_card_centralizer_t
  obtain ⟨St⟩ := (inferInstance : Nonempty (Sylow 2 ↥Ct))
  set SP : Subgroup ↥QP45.originalSubgroup := (St : Subgroup ↥Ct).map Ct.subtype with hSP
  have hSP64 : Nat.card SP = 2 ^ 6 := by
    rw [hSP, Subgroup.card_map_of_injective Ct.subtype_injective, Sylow.card_eq_multiplicity,
      hCt576]
    have h : (576 : ℕ) = 2 ^ 6 * 9 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9)]
  set TH : Subgroup ↥(H z) := SP.comap (qHP D) with hTH
  let f : ↥TH →* ↥QP45.originalSubgroup := (qHP D).comp TH.subtype
  have hker : f.ker.map TH.subtype = (qHP D).ker := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      change qHP D x ∈ SP
      rw [hx]
      exact SP.one_mem
  have hkercard : Nat.card f.ker = 2 ^ 9 := by
    rw [← Subgroup.card_map_of_injective TH.subtype_injective, hker, ker_qHP,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe J_le_H).toEquiv, hA1.card_J]
  have hrange : f.range = SP := by
    ext s
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hs
      obtain ⟨h, rfl⟩ := qHP_surjective D s
      exact ⟨⟨h, hs⟩, rfl⟩
  have hTHcard : Nat.card TH = 2 ^ 15 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hkercard, hrange, hSP64] at h
    rw [← h]
    norm_num
  refine ⟨TH.map (H z).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 15)
      (by rw [Subgroup.card_map_of_injective (H z).subtype_injective, hTHcard])
  · rw [Subgroup.card_map_of_injective (H z).subtype_injective, hTHcard]

theorem lemma14_core
    (hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G))
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    (hJ0 : H z ≤ Subgroup.normalizer (CJ z ((s1HP D : ↥(H z)) : G) : Set G))
    (hus1 : ((uHP D : ↥(H z)) : G) * ((s1HP D : ↥(H z)) : G) * ((uHP D : ↥(H z)) : G)⁻¹ =
      ((s2HP D : ↥(H z)) : G)) :
    ∀ x : G, (∃ j ∈ J z, x = ((uHP D * tHP D : ↥(H z)) : G) * j) → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s1 : G := ((s1HP D : ↥(H z)) : G) with hs1
  set s2 : G := ((s2HP D : ↥(H z)) : G) with hs2
  obtain ⟨u₁, t₁, c₁, hc₁H, hu₁H, ht₁H, hu₁J, ht₁J, hc₁R, hus1', hus2', hts1, hts2, huC, htC,
    hc₁C, ht2, hu₁2, hut, hc₁2, hc₁Rn, hfreec⟩ := exists_c1 D hy hJ0 hus1
  have hRJ : hy.R ≤ J z := hy.R_le_J
  have hc₁J : (u₁ * t₁)⁻¹ * c₁ ∈ J z := hRJ hc₁R
  set ut : G := ((uHP D * tHP D : ↥(H z)) : G) with hut'
  have hutH : ut ∈ H z := (uHP D * tHP D).2
  have hc₁ut : ut⁻¹ * c₁ ∈ J z := by
    have e : ut⁻¹ * c₁ = ((tHP D : ↥(H z)) : G)⁻¹ * ((((uHP D : ↥(H z)) : G))⁻¹ * u₁) *
        ((tHP D : ↥(H z)) : G) * (((tHP D : ↥(H z)) : G)⁻¹ * t₁) * ((u₁ * t₁)⁻¹ * c₁) := by
      rw [hut']
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    have h1 : ((tHP D : ↥(H z)) : G)⁻¹ * ((((uHP D : ↥(H z)) : G))⁻¹ * u₁) *
        ((tHP D : ↥(H z)) : G) ∈ J z := by
      have := conj_mem_J ((H z).inv_mem (tHP D).2) hu₁J
      simpa using this
    exact (J z).mul_mem ((J z).mul_mem h1 ht₁J) hc₁J
  intro x hx hx2 g hg
  obtain ⟨j, hj, hxj⟩ := hx
  have hxc₁ : ∃ j' ∈ J z, x = c₁ * j' := by
    refine ⟨c₁⁻¹ * ut * j, (J z).mul_mem ?_ hj, by rw [hxj]; group⟩
    have e : c₁⁻¹ * ut = (ut⁻¹ * c₁)⁻¹ := by group
    rw [e]
    exact (J z).inv_mem hc₁ut
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h
  obtain ⟨h, hhR, e, he, hhx⟩ := hy.exists_conj_mem_of_free hc₁H hc₁C hc₁Rn hc₁2 hfreec hxc₁ hxx
  set x' := c₁ * e with hx'
  have heJ : e ∈ J z := (CJ_le_J _) he
  have hhJ : h ∈ J z := hRJ hhR
  have hx'H : x' ∈ H z := (H z).mul_mem hc₁H (J_le_H heJ)
  have hts := Hyp.commute_s_of_t1 hts1 hts2
  have hus : u₁ * (s1 * s2⁻¹) * u₁⁻¹ = (s1 * s2⁻¹)⁻¹ := by
    have hc : s2 * s1⁻¹ = (s1 * s2⁻¹)⁻¹ := by group
    calc u₁ * (s1 * s2⁻¹) * u₁⁻¹ = (u₁ * s1 * u₁⁻¹) * (u₁ * s2 * u₁⁻¹)⁻¹ := by group
      _ = (s1 * s2⁻¹)⁻¹ := by rw [hus1', hus2', hc]
  have hbu := betaHP_conj_mem D hu₁H ht₁H hu₁J ht₁J
  have hFt := hy.card_fixIn_t1_sq_le D rfl ht₁H ht₁J hts1 htC
  obtain ⟨r, hrR, hr2, hc₁r⟩ := hy.exists_key ht₁H hu₁H hc₁H (betaHP D).2 hts hus htC huC
    (hy.zpowers_le_J ht2) hu₁2 hut hc₁J hc₁2 hc₁Rn hbu hFt hfreec
  obtain ⟨K, hKJ, hKx, eK, heKz⟩ := hy.exists_z4q8 hc₁H hc₁C hrR hr2 hc₁r he
  set m := h * g with hm
  have hmz : m * z * m⁻¹ = x' := by
    rw [← hhx, ← hg, hm]
    group
  have hxq : qHP D ⟨x', hx'H⟩ =
      (⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup) := by
    have hJ' : ut⁻¹ * x' ∈ J z := by
      rw [hx']
      have e2 : ut⁻¹ * (c₁ * e) = (ut⁻¹ * c₁) * e := by group
      rw [e2]
      exact (J z).mul_mem hc₁ut heJ
    rw [qHP_eq_of_inv_mul_mem_J D (x := uHP D * tHP D) (y := ⟨x', hx'H⟩) hJ', map_mul, qHP_uHP,
      qHP_tHP]
  have hK16 : Nat.card K = 16 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hK2 : IsPGroup 2 K := IsPGroup.of_card (n := 4) (by rw [hK16]; norm_num)
  set M := H z ⊓ Subgroup.centralizer ({x'} : Set G) with hM
  have hKM : K ≤ M := fun k hk => ⟨J_le_H (hKJ hk), hKx hk⟩
  obtain ⟨Q, hKQ⟩ := (hK2.comap_subtype : IsPGroup 2 (K.subgroupOf M)).exists_le_sylow
  set X : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hX
  have hXsyl : IsSylowOf 2 X M := ⟨Q, rfl⟩
  have hKX : K ≤ X := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKM]
    exact Subgroup.map_mono hKQ
  have hXH : X ≤ H z := hXsyl.le.trans inf_le_left
  have hXx : X ≤ Subgroup.centralizer ({x'} : Set G) := hXsyl.le.trans inf_le_right
  have hXcard : Nat.card X ≤ 2 ^ 14 :=
    card_le_of_le_centralizer_ut D hy.hA1 hXH hx'H hxq hXx hXsyl.isPGroup
  obtain ⟨T, hTH, hT2, hTcard⟩ := exists_two_subgroup_H D hy.hA1
  set Tm := T.map (MulAut.conj m).toMonoidHom with hTm
  have hTmx : Tm ≤ Subgroup.centralizer ({x'} : Set G) := by
    rintro _ ⟨y, hyT, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyz : y * z = z * y := commute_z_of_mem_H (hTH hyT)
    change m * y * m⁻¹ * x' = x' * (m * y * m⁻¹)
    rw [← hmz]
    calc m * y * m⁻¹ * (m * z * m⁻¹) = m * (y * z) * m⁻¹ := by group
      _ = m * (z * y) * m⁻¹ := by rw [hyz]
      _ = m * z * m⁻¹ * (m * y * m⁻¹) := by group
  have hTmcard : Nat.card Tm = 2 ^ 15 := by
    rw [hTm, Subgroup.card_map_of_injective (MulAut.conj m).injective, hTcard]
  have hTm2 : IsPGroup 2 Tm := IsPGroup.of_card (n := 15) hTmcard
  have hnotsyl : ¬ IsSylowOf 2 X (Subgroup.centralizer ({x'} : Set G)) := by
    intro hsyl
    have := card_le_of_isSylowOf hsyl hTmx hTm2
    rw [hTmcard] at this
    omega
  have hNle : ¬ (Subgroup.normalizer (X : Set G) ⊓ Subgroup.centralizer ({x'} : Set G) ≤ H z) :=
    fun hle => hnotsyl (isSylowOf_of_normalizer_inf_le hXsyl hle)
  obtain ⟨y, ⟨hyN, hyx⟩, hyH'⟩ := Set.not_subset.mp hNle
  have hyH : y ∉ H z := hyH'
  have hyzJ : y * z * y⁻¹ ∉ J z := by
    intro hJy
    by_cases hyz : y * z * y⁻¹ = z
    · apply hyH
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      calc y * z = (y * z * y⁻¹) * y := by group
        _ = z * y := by rw [hyz]
    · have hord : orderOf (y * z * y⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy.orderOf_z]
      exact hJ _ hJy hord hyz y rfl
  set Ky := K.map (MulAut.conj y).toMonoidHom with hKy
  have hKyX : Ky ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hyN k).mp (hKX hk)
  have hKyH : Ky ≤ H z := hKyX.trans hXH
  have hKyx : Ky ≤ Subgroup.centralizer ({x'} : Set G) := hKyX.trans hXx
  have hKyJ : ∀ k ∈ Ky, k ∈ J z → k = 1 := by
    rintro _ ⟨κ, hκ, rfl⟩ hkJ
    by_contra hk1
    have hκ1 : (⟨κ, hκ⟩ : ↥K) ≠ 1 := by
      intro h1
      apply hk1
      have : κ = 1 := congrArg Subtype.val h1
      simp [this]
    have hm1 : eK ⟨κ, hκ⟩ ≠ 1 := fun h1 => hκ1 (eK.injective (by rw [h1, map_one]))
    have hzK : ((eK.symm ⟨2, 0, 0⟩ : ↥K) : G) = z := heKz
    apply hyzJ
    rcases pauli_cases_of_ne_one _ hm1 with h | h | ⟨m', h⟩
    · have hκz : κ = z := by
        have := congrArg (fun w => ((eK.symm w : ↥K) : G)) h
        simpa [hzK] using this
      change y * κ * y⁻¹ ∈ J z at hkJ
      rwa [hκz] at hkJ
    · have hκz : κ * κ = z := by
        have := congrArg (fun w => ((eK.symm w : ↥K) : G)) h
        simpa [hzK] using this
      change y * κ * y⁻¹ ∈ J z at hkJ
      have h2 := (J z).mul_mem hkJ hkJ
      have e2 : y * κ * y⁻¹ * (y * κ * y⁻¹) = y * (κ * κ) * y⁻¹ := by group
      rwa [e2, hκz] at h2
    · set κ' : G := ((eK.symm m' : ↥K) : G) with hκ'
      have hκ'K : κ' ∈ K := (eK.symm m').2
      have hκz : κ * κ' * κ⁻¹ * κ'⁻¹ = z := by
        have := congrArg (fun w => ((eK.symm w : ↥K) : G)) h
        simpa [hzK, hκ'] using this
      change y * κ * y⁻¹ ∈ J z at hkJ
      have hκ'H : y * κ' * y⁻¹ ∈ H z := hKyH ⟨κ', hκ'K, rfl⟩
      have h1 : (y * κ' * y⁻¹) * (y * κ * y⁻¹)⁻¹ * (y * κ' * y⁻¹)⁻¹ ∈ J z :=
        conj_mem_J hκ'H ((J z).inv_mem hkJ)
      have h2 := (J z).mul_mem hkJ h1
      have e2 : y * κ * y⁻¹ * ((y * κ' * y⁻¹) * (y * κ * y⁻¹)⁻¹ * (y * κ' * y⁻¹)⁻¹) =
          y * (κ * κ' * κ⁻¹ * κ'⁻¹) * y⁻¹ := by group
      rwa [e2, hκz] at h2
  let ψ : ↥Ky →* ↥QP45.originalSubgroup := (qHP D).comp (Subgroup.inclusion hKyH)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkJ : (k : G) ∈ J z := mem_J_of_qHP_eq_one D (x := Subgroup.inclusion hKyH k) hk
    exact Subtype.ext (hKyJ k k.2 hkJ)
  have hψle : ψ.range ≤ Subgroup.centralizer
      ({(⟨u, u_mem_Q⟩ : ↥QP45.originalSubgroup) * (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup)} :
        Set ↥QP45.originalSubgroup) := by
    intro w hw
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff, ← hxq]
    have hkx : Subgroup.inclusion hKyH k * ⟨x', hx'H⟩ = ⟨x', hx'H⟩ * Subgroup.inclusion hKyH k :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKyx k.2))
    have h1 := congrArg (qHP D) hkx
    rw [map_mul, map_mul] at h1
    exact h1
  have hiso : ↥ψ.range ≃* CFSG.Quasithin.Z4StarQ8Model :=
    ((MonoidHom.ofInjective hψinj).symm.trans ((MulAut.conj y).subgroupMap K).symm).trans eK
  exact qp45_no_z4q8_le_centralizer_ut ψ.range hψle ⟨hiso⟩

end Core

end CFSG.RankThree.GF2n.Parrott.A1Section2Local

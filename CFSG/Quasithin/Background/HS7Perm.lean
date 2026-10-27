module

public import CFSG.Quasithin.Background.HSL3NPrime

public section

namespace CFSG.Quasithin

namespace H

namespace S7

open CFSG.Open Equiv
open scoped Pointwise

theorem card_sylow_two_eq {G : Type*} [Group G] [Finite G] {U L : Subgroup G}
    (hU : IsSylowIn 2 U L) {k m : ℕ} (hm : Odd m) (hL : Nat.card L = 2 ^ k * m) :
    Nat.card U = 2 ^ k := by
  obtain ⟨j, hj⟩ := hU.isPGroup.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card (H := U) (K := L)
  rw [inf_eq_left.2 hU.le, hj, hL] at h1
  have hr : Odd (U.relIndex L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hU.not_dvd_relIndex)
  have hjk : 2 ^ j ∣ 2 ^ k := by
    have h2 : 2 ^ j ∣ 2 ^ k * m := ⟨U.relIndex L, by rw [← h1, mul_comm]⟩
    exact (Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right h2
  have hkj : 2 ^ k ∣ 2 ^ j := by
    have h2 : 2 ^ k ∣ 2 ^ j * U.relIndex L := ⟨m, by rw [mul_comm (2 ^ j), h1]⟩
    exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hr)).dvd_of_dvd_mul_right h2
  rw [hj, Nat.dvd_antisymm hjk hkj]

section Seven

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_support_le (hα : Fintype.card α = 7) (σ : Perm α) : σ.support.card ≤ 7 :=
  hα ▸ Finset.card_le_univ _

theorem orderOf_dvd_420 (hα : Fintype.card α = 7) (σ : Perm α) : orderOf σ ∣ 420 := by
  rw [← Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun n hn => ?_
  have h1 := (Perm.le_card_support_of_mem_cycleType hn).trans (card_support_le hα σ)
  have h2 := Perm.two_le_of_mem_cycleType hn
  have key : ∀ m : ℕ, 2 ≤ m → m ≤ 7 → m ∣ 420 := by decide
  exact key n h2 h1

theorem cycleType_of_orderOf_prime (hα : Fintype.card α = 7) {σ : Perm α} {p : ℕ}
    (hp : p.Prime) (h4 : 4 ≤ p) (hσ : orderOf σ = p) : σ.cycleType = {p} := by
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (by rw [hσ]; exact hp)
  rw [hσ] at hn
  have hsum := Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have h1 : (n + 1) * p ≤ 7 := hsum ▸ card_support_le hα σ
  have hn0 : n = 0 := by nlinarith
  rw [hn, hn0]
  rfl

theorem card_centralizer_of_cycleType (hα : Fintype.card α = 7) {σ : Perm α} {p : ℕ}
    (h : σ.cycleType = {p}) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm α))) = (7 - p).factorial * p := by
  rw [Perm.nat_card_centralizer, h, hα]
  simp

theorem not_commute_three_five (hα : Fintype.card α = 7) {y z : Perm α} (hy : orderOf y = 3)
    (hz : orderOf z = 5) (hyz : y * z = z * y) : False := by
  have hmem : y ∈ Subgroup.centralizer ({z} : Set (Perm α)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyz
  have h1 := Subgroup.orderOf_dvd_natCard _ hmem
  rw [card_centralizer_of_cycleType hα
    (cycleType_of_orderOf_prime hα (by norm_num) (by norm_num) hz), hy] at h1
  norm_num at h1

theorem zpowers_eq_centralizer (hα : Fintype.card α = 7) {g : Perm α} (h7 : orderOf g = 7) :
    Subgroup.zpowers g = Subgroup.centralizer ({g} : Set (Perm α)) := by
  have hle : Subgroup.zpowers g ≤ Subgroup.centralizer ({g} : Set (Perm α)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_centralizer_of_cycleType hα
    (cycleType_of_orderOf_prime hα (by norm_num) (by norm_num) h7), Nat.card_zpowers, h7]
  norm_num

theorem eq_zpowers_of_seven (hα : Fintype.card α = 7) {B : Subgroup (Perm α)}
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) {g : Perm α} (hg : g ∈ B) (h7 : orderOf g = 7) :
    B = Subgroup.zpowers g := by
  have hle : B ≤ Subgroup.centralizer ({g} : Set (Perm α)) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hBab b hb g hg)
  rw [← zpowers_eq_centralizer hα h7] at hle
  exact le_antisymm hle ((Subgroup.zpowers_le).mpr hg)

theorem exists_pow_apply_eq (hα : Fintype.card α = 7) {g : Perm α} (h7 : orderOf g = 7)
    (x y : α) : ∃ i : ℕ, (g ^ i) x = y := by
  have hct := cycleType_of_orderOf_prime hα (by norm_num) (by norm_num) h7
  have hcyc : g.IsCycle := Perm.card_cycleType_eq_one.mp (by rw [hct]; rfl)
  have hsupp : g.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Perm.sum_cycleType, hct, hα]
    rfl
  have hx : g x ≠ x := Perm.mem_support.mp (hsupp ▸ Finset.mem_univ x)
  have hy : g y ≠ y := Perm.mem_support.mp (hsupp ▸ Finset.mem_univ y)
  exact hcyc.exists_pow_eq hx hy

theorem card_normalizer_le (hα : Fintype.card α = 7) {g : Perm α} (h7 : orderOf g = 7) :
    Nat.card (Subgroup.normalizer ((Subgroup.zpowers g : Subgroup (Perm α)) : Set (Perm α))) ≤
      42 := by
  set P := Subgroup.zpowers g with hP
  set N := Subgroup.normalizer (P : Set (Perm α)) with hN
  set φ := P.normalizerMonoidHom with hφ
  have hcard : Nat.card N = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  have hker : Nat.card φ.ker ≤ 7 := by
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    have h1 : Nat.card ((Subgroup.centralizer (P : Set (Perm α))).subgroupOf N) =
        Nat.card (Subgroup.centralizer (P : Set (Perm α))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv
    have h2 : Subgroup.centralizer (P : Set (Perm α)) ≤
        Subgroup.centralizer ({g} : Set (Perm α)) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers g))
    have h3 := Subgroup.card_le_of_le h2
    rw [card_centralizer_of_cycleType hα
      (cycleType_of_orderOf_prime hα (by norm_num) (by norm_num) h7)] at h3
    norm_num at h3
    exact le_trans (le_of_eq h1) h3
  have hrange : Nat.card φ.range ≤ 6 := by
    have h1 : Nat.card φ.range ≤ Nat.card (MulAut ↥P) := Subgroup.card_le_card_group _
    have h2 : Nat.card (MulAut ↥P) = 6 := by
      rw [IsCyclic.card_mulAut, hP, Nat.card_zpowers, h7, Nat.totient_prime (by norm_num)]
    omega
  rw [hcard]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 7 * 6 := Nat.mul_le_mul hker hrange
    _ = 42 := by norm_num

theorem false_of_card_56 (hα : Fintype.card α = 7) {K : Subgroup (Perm α)}
    (hK : Nat.card K = 56) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g', hg'⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 7 (by rw [hK]; norm_num)
  have hg7 : orderOf (g' : Perm α) = 7 := by rw [Subgroup.orderOf_coe, hg']
  have hPc : Nat.card (Subgroup.zpowers g') = 7 := by rw [Nat.card_zpowers, hg']
  have hPp : IsPGroup 7 (Subgroup.zpowers g') :=
    IsPGroup.of_card (n := 1) (by rw [hPc, pow_one])
  have hPidx : (Subgroup.zpowers g').index = 8 := by
    have := (Subgroup.zpowers g').card_mul_index
    rw [hPc, hK] at this
    omega
  let Q : Sylow 7 ↥K := hPp.toSylow (by rw [hPidx]; norm_num)
  have hQ : (Q : Subgroup ↥K) = Subgroup.zpowers g' := rfl
  have hn := card_sylow_modEq_one 7 ↥K
  have hd := Q.card_dvd_index
  rw [hQ, hPidx] at hd
  have key : ∀ m : ℕ, m ≤ 8 → m ∣ 8 → m ≡ 1 [MOD 7] → m = 1 ∨ m = 8 := by decide
  rcases key _ (Nat.le_of_dvd (by norm_num) hd) hd hn with h1 | h8
  ·
    have : Subsingleton (Sylow 7 ↥K) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hnorm : (Subgroup.zpowers g').Normal := Q.normal_of_subsingleton
    have hKN : K ≤ Subgroup.normalizer
        ((Subgroup.zpowers (g' : Perm α) : Subgroup (Perm α)) : Set (Perm α)) := by
      have hmap : (Subgroup.zpowers g').map K.subtype = Subgroup.zpowers (g' : Perm α) :=
        MonoidHom.map_zpowers K.subtype g'
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← hmap] at hx ⊢
        obtain ⟨x', hx', rfl⟩ := hx
        exact ⟨⟨k, hk⟩ * x' * ⟨k, hk⟩⁻¹, hnorm.conj_mem x' hx' ⟨k, hk⟩, rfl⟩
      · intro hx
        rw [← hmap] at hx ⊢
        obtain ⟨x', hx', hxe⟩ := hx
        refine ⟨⟨k, hk⟩⁻¹ * x' * ⟨k, hk⟩, ?_, ?_⟩
        · have := hnorm.conj_mem x' hx' ⟨k, hk⟩⁻¹
          simpa using this
        · have hxe' : (x' : Perm α) = k * x * k⁻¹ := hxe
          change k⁻¹ * (x' : Perm α) * k = x
          rw [hxe']
          group
    have h1 := Subgroup.card_le_of_le hKN
    have h2 := card_normalizer_le hα hg7
    omega
  ·
    have hNidx : (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K)).index = 8 :=
      Q.card_eq_index_normalizer.symm.trans h8
    have hNcard : Nat.card (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K)) = 7 := by
      have := (Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K)).card_mul_index
      rw [hNidx, hK] at this
      omega
    have hNQ : Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K) = Q :=
      (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [hNcard, hQ, hPc])).symm
    have hNC : Subgroup.normalizer ((Q : Subgroup ↥K) : Set ↥K) ≤
        Subgroup.centralizer ((Q : Subgroup ↥K) : Set ↥K) := by
      rw [hNQ]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hQ] at hx hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← zpow_add, add_comm]
    have hcomp := MonoidHom.ker_transferSylow_isComplement' Q hNC
    set E := (MonoidHom.transferSylow Q hNC).ker with hE
    have hEc : Nat.card E = 8 := by
      have := hcomp.card_mul_card
      rw [hQ, hPc, hK] at this
      omega
    have hEn : E.Normal := MonoidHom.normal_ker _
    set E' := E.map K.subtype with hE'
    have hE'c : Nat.card E' = 8 := by
      rw [hE', Subgroup.card_map_of_injective K.subtype_injective, hEc]
    have hE'p : IsPGroup 2 E' := IsPGroup.of_card (n := 3) (by rw [hE'c]; norm_num)
    have hfix := hE'p.card_modEq_card_fixedPoints α
    rw [Nat.card_eq_fintype_card, hα] at hfix
    have hne : Nat.card (MulAction.fixedPoints E' α) ≠ 0 := by
      intro h0
      rw [h0] at hfix
      exact absurd hfix (by decide)
    obtain ⟨⟨a, ha⟩⟩ := (Nat.card_ne_zero.mp hne).1
    have hall : ∀ e ∈ E', e = 1 := by
      intro e he
      obtain ⟨e₀, he₀, rfl⟩ := he
      ext y
      obtain ⟨i, rfl⟩ := exists_pow_apply_eq hα hg7 a y
      have hc : (g' ^ i)⁻¹ * e₀ * g' ^ i ∈ E := by
        have := hEn.conj_mem e₀ he₀ (g' ^ i)⁻¹
        simpa using this
      have hcm : (((g' ^ i)⁻¹ * e₀ * g' ^ i : ↥K) : Perm α) ∈ E' := ⟨_, hc, rfl⟩
      have h1 := ha ⟨_, hcm⟩
      change ((((g' ^ i)⁻¹ * e₀ * g' ^ i : ↥K) : Perm α)) a = a at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Perm.coe_mul,
        Function.comp_apply] at h1
      change (K.subtype e₀) (((g' : Perm α) ^ i) a) = (1 : Perm α) (((g' : Perm α) ^ i) a)
      rw [Perm.one_apply]
      have h2 := congrArg ((g' : Perm α) ^ i) h1
      simpa using h2
    have hbot : E' = ⊥ := (Subgroup.eq_bot_iff_forall E').mpr hall
    rw [hbot, Subgroup.card_bot] at hE'c
    norm_num at hE'c

theorem nPrime_le_two (hα : Fintype.card α = 7) : E3.nPrime (⊤ : Subgroup (Perm α)) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two ⊤).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two _).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  rintro c ⟨Y, B, S, hYB, -, hY, hYc, hBab, hBodd, hS, hBS⟩
  by_contra hc
  push Not at hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Y)
  have hgo : orderOf (g : Perm α) = 2 ^ c - 1 := by rw [Subgroup.orderOf_coe, hg, hYc]
  have hgB : (g : Perm α) ∈ B := hYB g.2
  have hodd : Odd (orderOf (g : Perm α)) :=
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hgB)
  have h105 : 2 ^ c - 1 ∣ 105 := by
    rw [← hgo]
    have hcop : Nat.Coprime (orderOf (g : Perm α)) 4 :=
      (Nat.coprime_two_right.mpr hodd).pow_right 2
    have h420 : orderOf (g : Perm α) ∣ 4 * 105 := orderOf_dvd_420 hα _
    exact hcop.dvd_of_dvd_mul_left h420
  have hc6 : c ≤ 6 := by
    by_contra h7
    push Not at h7
    have h1 : 2 ^ 7 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) h7
    have h2 := Nat.le_of_dvd (by norm_num) h105
    omega
  interval_cases c
  ·
    have hg7 : orderOf (g : Perm α) = 7 := by rw [hgo]; norm_num
    have hB := eq_zpowers_of_seven hα hBab hgB hg7
    have hBc : Nat.card B = 7 := by rw [hB, Nat.card_zpowers, hg7]
    have hcard : Nat.card (⊤ : Subgroup (Perm α)) = 2 ^ 4 * 315 := by
      rw [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, hα]
      rfl
    have hSc := card_sylow_two_eq hS (by decide) hcard
    have hcop : Nat.Coprime (Nat.card B) (Nat.card S) := by rw [hBc, hSc]; norm_num
    have hKc : Nat.card ↥(B ⊔ S) = 112 := by
      rw [SL3One.card_sup_of_permute hBS (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot,
        hBc, hSc]
      norm_num
    set K₀ := (alternatingGroup α) ⊓ (B ⊔ S) with hK₀
    have hrel := Subgroup.relIndex_mul_card (H := alternatingGroup α) (K := B ⊔ S)
    rw [hKc, ← hK₀] at hrel
    have hrel2 : (alternatingGroup α).relIndex (B ⊔ S) ∣ 2 := by
      have := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup α) (B ⊔ S)
      have hnt : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hα]; norm_num)
      rwa [alternatingGroup.index_eq_two] at this
    have hA : Nat.card (alternatingGroup α) = 2520 := by
      have hnt : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hα]; norm_num)
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hα]
      rfl
    have hK₀A : Nat.card K₀ ∣ 2520 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
    have hK₀c : Nat.card K₀ = 56 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hrel2 with h | h
      · rw [h, one_mul] at hrel
        rw [hrel] at hK₀A
        norm_num at hK₀A
      · rw [h] at hrel
        omega
    exact false_of_card_56 hα hK₀c
  ·
    have hg15 : orderOf (g : Perm α) = 15 := by rw [hgo]; norm_num
    refine not_commute_three_five hα (y := (g : Perm α) ^ 5) (z := (g : Perm α) ^ 3) ?_ ?_ ?_
    · rw [orderOf_pow' _ (by norm_num), hg15]
      norm_num
    · rw [orderOf_pow' _ (by norm_num), hg15]
      norm_num
    · rw [← pow_add, ← pow_add, add_comm]
  · norm_num at h105
  · norm_num at h105

end Seven

section Lower

noncomputable abbrev hsum : Perm (Fin 4) × Perm (Fin 3) →* Perm (Fin 4 ⊕ Fin 3) :=
  Perm.sumCongrHom (Fin 4) (Fin 3)

theorem two_le_nPrime : 2 ≤ E3.nPrime (⊤ : Subgroup (Perm (Fin 4 ⊕ Fin 3))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := hsum.range with hH
  set B₀ := (⊥ : Subgroup (Perm (Fin 4))).prod (alternatingGroup (Fin 3)) with hB₀
  set B := B₀.map hsum with hB
  have hinj : Function.Injective hsum := Perm.sumCongrHom_injective
  have hBH : B ≤ H := Subgroup.map_le_range _ _
  have hHc : Nat.card H = 2 ^ 4 * 9 := by
    rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_perm,
      Nat.card_perm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
      Fintype.card_fin]
    rfl
  have hBc : Nat.card B = 3 := by
    rw [hB, Subgroup.card_map_of_injective hinj, hB₀,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hBn : ∀ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ B := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, hq, rfl⟩
    refine ⟨p * q * p⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hq' : q.1 = 1 ∧ q.2 ∈ alternatingGroup (Fin 3) := ⟨Subgroup.mem_bot.mp hq.1, hq.2⟩
    refine ⟨Subgroup.mem_bot.mpr ?_, ?_⟩
    · change p.1 * q.1 * p.1⁻¹ = 1
      rw [hq'.1, mul_one, mul_inv_cancel]
    · change p.2 * q.2 * p.2⁻¹ ∈ alternatingGroup (Fin 3)
      exact (alternatingGroup.normal (α := Fin 3)).conj_mem _ hq'.2 p.2
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  set S := (S₀ : Subgroup ↥H).map H.subtype with hS
  have hSH : S ≤ H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS₀ : IsSylowIn 2 S H := by
    refine ⟨hSH, ?_, ?_⟩
    · exact IsPGroup.map S₀.isPGroup' H.subtype
    · have : S.subgroupOf H = S₀ := by
        rw [hS]
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective (S₀ : Subgroup ↥H)
      rw [Subgroup.relIndex, this]
      exact S₀.not_dvd_index
  have hSc : Nat.card S = 2 ^ 4 := card_sylow_two_eq hS₀ (by decide) hHc
  have hSsyl : IsSylowIn 2 S ⊤ := by
    refine ⟨le_top, IsPGroup.of_card hSc, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := ⊤)
    rw [inf_top_eq, hSc, Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    norm_num [Nat.factorial] at h1
    rw [Subgroup.relIndex_top_right]
    omega
  have hBS : (B : Set (Perm (Fin 4 ⊕ Fin 3))) * (S : Set (Perm (Fin 4 ⊕ Fin 3))) =
      (S : Set (Perm (Fin 4 ⊕ Fin 3))) * (B : Set (Perm (Fin 4 ⊕ Fin 3))) := by
    ext x
    constructor
    · rintro ⟨b, hb, s, hs, rfl⟩
      refine ⟨s, hs, s⁻¹ * b * s, ?_, by group⟩
      have := hBn s⁻¹ (H.inv_mem (hSH hs)) b hb
      simpa using this
    · rintro ⟨s, hs, b, hb, rfl⟩
      exact ⟨s * b * s⁻¹, hBn s (hSH hs) b hb, s, hs, by group⟩
  have hBcyc : IsCyclic ↥B := isCyclic_of_prime_card hBc
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hg⟩ := hBcyc.exists_generator
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have e := congrArg Subtype.val (show g ^ i * g ^ j = g ^ j * g ^ i by
      rw [← zpow_add, ← zpow_add, add_comm])
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hi, hj] at e
    exact e
  exact E3.le_nPrime (Y := B) (B := B) (S := S) le_rfl le_top hBcyc (by rw [hBc]; norm_num)
    hBab (by rw [hBc]; decide) hSsyl hBS

theorem nPrime_eq_two : E3.nPrime (⊤ : Subgroup (Perm (Fin 4 ⊕ Fin 3))) = 2 :=
  le_antisymm (nPrime_le_two (by simp)) two_le_nPrime

end Lower

end S7

end H

end CFSG.Quasithin

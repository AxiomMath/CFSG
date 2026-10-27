module

public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian
public import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
import CFSG.RankThree.GF2n.Parrott.LocalData
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43

private def b0P : Equiv.Perm (Fin 45) := beta1 * beta

private def g0P : Equiv.Perm (Fin 45) := u * sigma2 * sigma2 * beta1 * beta * sigma1 * alpha1

private theorem b0_conj_u : b0P * u * b0P⁻¹ = t := by decide +kernel

private theorem b0_conj_a12 : b0P * (alpha1 * alpha2) * b0P⁻¹ = alpha1 * alpha2 * t := by
  decide +kernel

private theorem b0_conj_b12 :
    b0P * (beta1 * beta2) * b0P⁻¹ = alpha1 * alpha2 * (beta1 * beta2) * t := by decide +kernel

private theorem b0_conj_t : b0P * t * b0P⁻¹ = u * (beta1 * beta2) * t := by decide +kernel

private theorem b0_pow_five : b0P ^ 5 = 1 := by decide +kernel

private theorem b0_ne_one : b0P ≠ 1 := by decide +kernel

private theorem g0_conj_b0 : g0P * b0P * g0P⁻¹ = b0P ^ 3 := by decide +kernel

private theorem g0_conj_t_not_commute : g0P * t * g0P⁻¹ * u ≠ u * (g0P * t * g0P⁻¹) := by
  decide +kernel

private theorem card_modEq_one_of_fixedPointFree {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B X : Subgroup G} (hB : IsPGroup p B)
    (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hfix : ∀ x ∈ X, (∀ b ∈ B, b * x * b⁻¹ = x) → x = 1) : Nat.card X ≡ 1 [MOD p] := by
  let _ : MulAction ↥B ↥X :=
    { smul := fun b x => ⟨(b : G) * x * (b : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hBX b.2) x).mp x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥B) : G) * x * ((1 : ↥B) : G)⁻¹ = x
        simp)
      mul_smul := fun b c x => Subtype.ext (by
        show ((b * c : ↥B) : G) * x * ((b * c : ↥B) : G)⁻¹ =
          (b : G) * ((c : G) * x * (c : G)⁻¹) * (b : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hfp : MulAction.fixedPoints ↥B ↥X = {1} := by
    ext x
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply Subtype.ext
      exact hfix _ x.2 fun b hb => congrArg Subtype.val (hx ⟨b, hb⟩)
    · rintro rfl b
      apply Subtype.ext
      show (b : G) * ((1 : ↥X) : G) * (b : G)⁻¹ = ((1 : ↥X) : G)
      simp
  have h := hB.card_modEq_card_fixedPoints ↥X
  have h1 : Nat.card ↑(({1} : Set ↥X)) = 1 := by simp
  rwa [hfp, h1] at h

private theorem mem_normalizer_inf_centralizer {G : Type*} [Group G] {X : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (X : Set G)) :
    b ∈ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
  have key : ∀ {b : G}, b ∈ Subgroup.normalizer (X : Set G) →
      ∀ z ∈ X ⊓ Subgroup.centralizer (X : Set G),
        b * z * b⁻¹ ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
    intro b hb z hz
    obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hb z).mp hzX, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    intro y hy
    have hy' : b⁻¹ * y * b ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) y).mp hy
      simpa using this
    have h1 := hzC _ hy'
    calc y * (b * z * b⁻¹) = b * ((b⁻¹ * y * b) * z) * b⁻¹ := by group
      _ = b * (z * (b⁻¹ * y * b)) * b⁻¹ := by rw [h1]
      _ = b * z * b⁻¹ * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key hb z, fun hz => ?_⟩
  have h := key (inv_mem hb) _ hz
  convert h using 1
  group

private theorem eq_sixteen_of_dvd_of_modEq {n : ℕ} (hdvd : n ∣ 64) (hmod : n ≡ 1 [MOD 5])
    (h1 : n ≠ 1) : n = 16 := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show n ∣ 2 ^ 6 by simpa using hdvd)
  interval_cases i <;> simp_all [Nat.ModEq]

section Model


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "Pp" => QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a1A" => (⟨alpha1, alpha1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b1A" => (⟨beta1, beta1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)

private theorem b0P_mem_Q : b0P ∈ QP45.originalSubgroup := by
  unfold b0P
  exact mul_mem beta1_mem_Q beta_mem_Q

private theorem g0P_mem_Q : g0P ∈ QP45.originalSubgroup := by
  unfold g0P
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem u_mem_Q sigma2_mem_Q) sigma2_mem_Q)
    beta1_mem_Q) beta_mem_Q) sigma1_mem_Q) alpha1_mem_Q

set_option quotPrecheck false in
local notation "b0A" => (⟨b0P, QP45_le_QA45 b0P_mem_Q⟩ : A45)
set_option quotPrecheck false in
local notation "g0A" => (⟨g0P, QP45_le_QA45 g0P_mem_Q⟩ : A45)

private theorem b0A_pow_five : b0A ^ 5 = 1 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact b0_pow_five)

private theorem b0A_ne_one : b0A ≠ 1 := fun h => b0_ne_one (by
  have h' := congrArg Subtype.val h
  rwa [Subgroup.coe_mk, Subgroup.coe_one] at h')

private theorem b0A_conj_u : b0A * uA * b0A⁻¹ = tA := Subtype.ext b0_conj_u

private theorem b0A_conj_a12 : b0A * (a1A * a2A) * b0A⁻¹ = a1A * a2A * tA :=
  Subtype.ext b0_conj_a12

private theorem b0A_conj_b12 : b0A * (b1A * b2A) * b0A⁻¹ = a1A * a2A * (b1A * b2A) * tA :=
  Subtype.ext b0_conj_b12

private theorem b0A_conj_t : b0A * tA * b0A⁻¹ = uA * (b1A * b2A) * tA := Subtype.ext b0_conj_t

private theorem g0A_conj_b0A : g0A * b0A * g0A⁻¹ = b0A ^ 3 := Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact g0_conj_b0)

private theorem g0A_conj_t_not_commute : g0A * tA * g0A⁻¹ * uA ≠ uA * (g0A * tA * g0A⁻¹) :=
  fun h => g0_conj_t_not_commute (by
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    exact h')

theorem qp45_card_ne_320 (K : Subgroup ↥QA45.originalSubgroup)
    (hK : K ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) : Nat.card K ≠ 320 := by
  intro hK320
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hPn : (Pp).Normal := Subgroup.normal_of_index_eq_two index_QP45
  have huP : uA ∈ Pp := Subgroup.mem_subgroupOf.mpr u_mem_Q
  have hvP : vA ∉ Pp := by
    rw [Subgroup.mem_subgroupOf]
    exact v_not_mem_Q
  have huvP : uA * vA ∉ Pp := fun h =>
    hvP (((Subgroup.mul_mem_iff_of_index_two index_QP45).mp h).mp huP)
  have hcop : ∀ x : A45, orderOf x ∣ 5 → orderOf x ∣ 64 → x = 1 := by
    intro x h5x h64x
    have hg := Nat.dvd_gcd h5x h64x
    have h1 : Nat.gcd 5 64 = 1 := by norm_num
    rw [h1] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  have hfive : ∀ B : Subgroup A45, B ≤ Pp → Nat.card B = 5 →
      Nat.card ↥(Subgroup.normalizer (B : Set A45) ⊓ Pp) = 20 ∧
        ∀ x ∈ Pp, (∀ b ∈ B, b * x * b⁻¹ = x) → x ∈ B := by
    intro B hBP hB
    obtain ⟨hN40, -, w, hw2, hwc, hCeq⟩ := qa45_sylowFive B hB
    have hwP : w ∉ Pp := by
      intro hw
      obtain ⟨c, hc⟩ := isConj_iff.mp hwc
      apply huvP
      rw [← hc]
      exact hPn.conj_mem w hw c
    have hwC : w ∈ Subgroup.centralizer (B : Set A45) := by
      rw [hCeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    refine ⟨?_, ?_⟩
    ·
      have hwN : w ∈ Subgroup.normalizer (B : Set A45) :=
        Subgroup.centralizer_le_normalizer _ hwC
      set N := Subgroup.normalizer (B : Set A45) with hN_def
      have hidx : ((N ⊓ Pp).subgroupOf N).index = 2 := by
        refine Subgroup.index_eq_two_iff.mpr ⟨⟨w, hwN⟩, fun b => ?_⟩
        rw [xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
          Subgroup.mem_inf]
        have hbN : (b : A45) ∈ N := b.2
        have hbw : ((b * ⟨w, hwN⟩ : ↥N) : A45) ∈ N := (b * ⟨w, hwN⟩).2
        have hiff := (Subgroup.mul_mem_iff_of_index_two index_QP45 (a := (b : A45)) (b := w))
        constructor
        · rintro ⟨-, h⟩ ⟨-, hb⟩
          exact hwP ((hiff.mp h).mp hb)
        · intro h
          refine ⟨hbw, hiff.mpr ⟨fun hb => absurd ⟨hbN, hb⟩ h, fun hw => absurd hw hwP⟩⟩
      have h := Subgroup.card_mul_index ((N ⊓ Pp).subgroupOf N)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hidx, hN40] at h
      omega
    · intro x hxP hxc
      have hxC : x ∈ Subgroup.centralizer (B : Set A45) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        calc b * x = b * x * b⁻¹ * b := by group
          _ = x * b := by rw [hxc b hb]
      have hcomm : ∀ a ∈ B, ∀ y ∈ Subgroup.zpowers w, Commute a y := by
        intro a ha y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hwC a ha) k
      rw [hCeq, CFSG.mem_sup_of_commute hcomm] at hxC
      obtain ⟨b, hb, y, hy, rfl⟩ := hxC
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : w ^ k = w ^ (k % 2) := by
        rw [← zpow_mod_orderOf w k, hw2]
        norm_num
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [hk, h, zpow_zero, mul_one]
        exact hb
      · exfalso
        rw [hk, h, zpow_one] at hxP
        apply hwP
        have := mul_mem (inv_mem (hBP hb)) hxP
        simpa using this
  obtain ⟨T, hT64⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K) 2 (n := 6)
    (by rw [hK320]; norm_num)
  have hTidx : T.index = 5 := by
    have h := Subgroup.card_mul_index T
    rw [hT64, hK320] at h
    omega
  set N₀ := T.normalCore with hN₀_def
  have hN₀idx : N₀.index ∣ 40 := by
    have h1 : N₀.index ∣ 120 := by
      have h := Subgroup.index_normalCore_dvd_factorial_index T
      rwa [hTidx, show Nat.factorial 5 = 120 by decide] at h
    have h2 : N₀.index ∣ 320 := hK320 ▸ Subgroup.index_dvd_card N₀
    have h3 := Nat.dvd_gcd h1 h2
    rwa [show Nat.gcd 120 320 = 40 by norm_num] at h3
  have hN₀8 : 8 ≤ Nat.card N₀ := by
    have h := Subgroup.card_mul_index N₀
    rw [hK320] at h
    have hle : N₀.index ≤ 40 := Nat.le_of_dvd (by norm_num) hN₀idx
    by_contra hlt
    push Not at hlt
    have : Nat.card N₀ * N₀.index ≤ 7 * 40 := Nat.mul_le_mul (by omega) hle
    omega
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hT64
  have hN₀T : N₀ ≤ T := Subgroup.normalCore_le T
  have hN₀64 : Nat.card N₀ ∣ 64 := by
    have h := Subgroup.card_dvd_of_le hN₀T
    rwa [hT64] at h
  set N₀A := N₀.map K.subtype with hN₀A_def
  have hN₀Acard : Nat.card N₀A = Nat.card N₀ :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hN₀AK : N₀A ≤ K := Subgroup.map_subtype_le N₀
  have hKN : K ≤ Subgroup.normalizer (N₀A : Set A45) := by
    have h := Subgroup.le_normalizer_map (H := N₀) K.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normalCore_normal T),
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hfact5 : (Nat.card ↥K).factorization 5 = 1 := by
    rw [hK320, show (320 : ℕ) = 2 ^ 6 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2 ^ 6),
      Nat.Prime.factorization_self Nat.prime_five]
  obtain ⟨P5⟩ : Nonempty (Sylow 5 ↥K) := inferInstance
  have hP5 : Nat.card (P5 : Subgroup ↥K) = 5 := by
    rw [Sylow.card_eq_multiplicity, hfact5, pow_one]
  set B5A := (P5 : Subgroup ↥K).map K.subtype with hB5A_def
  have hB5A : Nat.card B5A = 5 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hP5]
  have hB5AK : B5A ≤ K := Subgroup.map_subtype_le _
  have hB5AP : B5A ≤ Pp := hB5AK.trans hK
  have hB5A5 : IsPGroup 5 B5A := IsPGroup.of_card (n := 1) (by rw [hB5A, pow_one])
  obtain ⟨hNB20, hCB⟩ := hfive B5A hB5AP hB5A
  have hfixN₀ : ∀ x ∈ N₀A, (∀ b ∈ B5A, b * x * b⁻¹ = x) → x = 1 := by
    intro x hx hxc
    have hxB := hCB x (hK (hN₀AK hx)) hxc
    refine hcop x ?_ ?_
    · have := orderOf_dvd_natCard (⟨x, hxB⟩ : ↥B5A)
      rwa [hB5A, Subgroup.orderOf_mk] at this
    · have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥N₀A)
      rw [Subgroup.orderOf_mk, hN₀Acard] at this
      exact this.trans hN₀64
  have hcong : ∀ X : Subgroup A45, X ≤ N₀A → B5A ≤ Subgroup.normalizer (X : Set A45) →
      Nat.card X ≡ 1 [MOD 5] := fun X hX hBX =>
    card_modEq_one_of_fixedPointFree hB5A5 hBX fun x hx hxc => hfixN₀ x (hX hx) hxc
  have hB5AN : B5A ≤ Subgroup.normalizer (N₀A : Set A45) := hB5AK.trans hKN
  have h16of : ∀ X : Subgroup A45, X ≤ N₀A → B5A ≤ Subgroup.normalizer (X : Set A45) →
      Nat.card X ≠ 1 → Nat.card X = 16 := by
    intro X hX hBX h1
    have hdvd : Nat.card X ∣ 64 := by
      have := Subgroup.card_dvd_of_le hX
      rw [hN₀Acard] at this
      exact this.trans hN₀64
    exact eq_sixteen_of_dvd_of_modEq hdvd (hcong X hX hBX) h1
  have hN₀16 : Nat.card N₀A = 16 := h16of N₀A le_rfl hB5AN (by rw [hN₀Acard]; omega)
  have hN₀A2 : IsPGroup 2 N₀A := IsPGroup.of_card (n := 4) (by rw [hN₀16]; norm_num)
  have hZ : N₀A ⊓ Subgroup.centralizer (N₀A : Set A45) = N₀A := by
    have hZle : N₀A ⊓ Subgroup.centralizer (N₀A : Set A45) ≤ N₀A := inf_le_left
    have hZN : B5A ≤ Subgroup.normalizer
        ((N₀A ⊓ Subgroup.centralizer (N₀A : Set A45) : Subgroup A45) : Set A45) :=
      fun b hb => mem_normalizer_inf_centralizer (hB5AN hb)
    have hZ1 : Nat.card ↥(N₀A ⊓ Subgroup.centralizer (N₀A : Set A45)) ≠ 1 := by
      have : Nontrivial ↥N₀A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hN₀16]; norm_num)
      have hnt := hN₀A2.center_nontrivial
      rw [CFSG.GroupTheory.inf_centralizer_eq_map_center,
        Subgroup.card_map_of_injective N₀A.subtype_injective]
      exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne'
    exact Subgroup.eq_of_le_of_card_ge hZle (by rw [h16of _ hZle hZN hZ1, hN₀16])
  have hcommN₀ : ∀ x ∈ N₀A, ∀ y ∈ N₀A, x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ Subgroup.centralizer (N₀A : Set A45) := (Subgroup.mem_inf.mp (hZ.ge hy)).2
    exact Subgroup.mem_centralizer_iff.mp hy' x hx
  let Ω : Subgroup A45 :=
    { carrier := {x | x ∈ N₀A ∧ x * x = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcommN₀ b hb.1 a ha.1]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hΩle : Ω ≤ N₀A := fun x hx => hx.1
  have hΩN : B5A ≤ Subgroup.normalizer (Ω : Set A45) := by
    have key : ∀ {b : A45}, b ∈ Subgroup.normalizer (N₀A : Set A45) → ∀ x ∈ Ω,
        b * x * b⁻¹ ∈ Ω := by
      intro b hb x hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp hb x).mp hx.1, ?_⟩
      calc b * x * b⁻¹ * (b * x * b⁻¹) = b * (x * x) * b⁻¹ := by group
        _ = 1 := by rw [hx.2]; group
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key (hB5AN hb) x, fun hx => ?_⟩
    have h := key (inv_mem (hB5AN hb)) _ hx
    convert h using 1
    group
  have hΩ1 : Nat.card Ω ≠ 1 := by
    have : Fintype ↥N₀A := Fintype.ofFinite _
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := ↥N₀A) 2
      (by rw [← Nat.card_eq_fintype_card, hN₀16]; norm_num)
    intro h1
    have hyΩ : (y : A45) ∈ Ω := ⟨y.2, by
      rw [← pow_two, ← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]⟩
    have hbot : Ω = ⊥ := Subgroup.eq_bot_of_card_eq Ω h1
    rw [hbot, Subgroup.mem_bot] at hyΩ
    have : y = 1 := Subtype.ext hyΩ
    rw [this, orderOf_one] at hy
    norm_num at hy
  have hΩeq : Ω = N₀A :=
    Subgroup.eq_of_le_of_card_ge hΩle (by rw [h16of Ω hΩle hΩN hΩ1, hN₀16])
  have hEA : CFSG.Open.IsElemAbelian 2 N₀A := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hcommN₀ a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
    have hx' : x ∈ Ω := hΩeq.ge hx
    rw [pow_two]
    exact hx'.2
  have hNPK : Subgroup.normalizer (B5A : Set A45) ⊓ Pp ≤ K := by
    have hmod := card_sylow_modEq_one 5 ↥K
    have hidx5 : (P5 : Subgroup ↥K).index = 64 := by
      have h := Subgroup.card_mul_index (P5 : Subgroup ↥K)
      rw [hP5, hK320] at h
      omega
    have hdvd := Sylow.card_dvd_index P5
    rw [hidx5] at hdvd
    have hn : Nat.card (Sylow 5 ↥K) = (Subgroup.normalizer ((P5 : Subgroup ↥K) : Set ↥K)).index :=
      Sylow.card_eq_index_normalizer P5
    have hmapN : (Subgroup.normalizer ((P5 : Subgroup ↥K) : Set ↥K)).map K.subtype ≤
        Subgroup.normalizer (B5A : Set A45) ⊓ Pp :=
      le_inf (Subgroup.le_normalizer_map K.subtype)
        ((Subgroup.map_subtype_le _).trans hK)
    have hn1 : Nat.card (Sylow 5 ↥K) ≠ 1 := by
      intro h1
      rw [h1] at hn
      have htop := Subgroup.index_eq_one.mp hn.symm
      rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmapN
      have := Subgroup.card_le_of_le hmapN
      rw [hNB20, hK320] at this
      norm_num at this
    have h16 : Nat.card (Sylow 5 ↥K) = 16 := eq_sixteen_of_dvd_of_modEq hdvd hmod hn1
    have hcardN : Nat.card ↥((Subgroup.normalizer ((P5 : Subgroup ↥K) : Set ↥K)).map
        K.subtype) = 20 := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      have h := Subgroup.card_mul_index (Subgroup.normalizer ((P5 : Subgroup ↥K) : Set ↥K))
      rw [← hn, h16, hK320] at h
      omega
    have heq := Subgroup.eq_of_le_of_card_ge hmapN (by rw [hNB20, hcardN])
    rw [← heq]
    exact Subgroup.map_subtype_le _
  obtain ⟨g, hg⟩ := qa45_elemAbelian_sixteen.2 N₀A hEA hN₀16 (hN₀AK.trans hK)
  set B' := B5A.map (MulAut.conj g).toMonoidHom with hB'_def
  have hB'5 : Nat.card B' = 5 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB5A]
  have hB'P : B' ≤ Pp := by
    rintro _ ⟨b, hb, rfl⟩
    exact hPn.conj_mem b (hB5AP hb) g
  have hNB' : ∀ x ∈ Subgroup.normalizer (B' : Set A45), x ∈ Pp →
      x ∈ Subgroup.normalizer (sQA45 : Set A45) := by
    intro x hxN hxP
    rw [hB'_def, ← Subgroup.map_equiv_normalizer_eq] at hxN
    obtain ⟨y, hyN, rfl⟩ := hxN
    have hyP : y ∈ Pp := by
      have h1 := hPn.conj_mem _ hxP g⁻¹
      have e : g⁻¹ * ((MulAut.conj g).toMonoidHom y) * g⁻¹⁻¹ = y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [e] at h1
    have hyK := hNPK ⟨hyN, hyP⟩
    rw [← hg, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨y, hKN hyK, rfl⟩
  have hB'N : B' ≤ Subgroup.normalizer (sQA45 : Set A45) := fun b hb =>
    hNB' b (Subgroup.le_normalizer hb) (hB'P hb)
  have hb0ord : orderOf b0A = 5 := orderOf_eq_prime b0A_pow_five b0A_ne_one
  have hgenS : ∀ x ∈ ({uA, a1A * a2A, b1A * b2A, tA} : Set A45), x ∈ sQA45 := fun x hx =>
    Subgroup.subset_closure hx
  have hb0N : b0A ∈ Subgroup.normalizer (sQA45 : Set A45) := by
    show b0A ∈ Subgroup.normalizer ((Subgroup.closure {uA, a1A * a2A, b1A * b2A, tA} :
      Subgroup A45) : Set A45)
    refine CFSG.GroupTheory.mem_normalizer_closure fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [b0A_conj_u]
      exact hgenS _ (by simp)
    · rw [b0A_conj_a12]
      exact mul_mem (hgenS _ (by simp)) (hgenS _ (by simp))
    · rw [b0A_conj_b12]
      exact mul_mem (mul_mem (hgenS _ (by simp)) (hgenS _ (by simp))) (hgenS _ (by simp))
    · rw [b0A_conj_t]
      exact mul_mem (mul_mem (hgenS _ (by simp)) (hgenS _ (by simp))) (hgenS _ (by simp))
  set B₀ := Subgroup.zpowers b0A with hB₀_def
  have hB₀5 : Nat.card B₀ = 5 := by rw [Nat.card_zpowers, hb0ord]
  have hB₀N : B₀ ≤ Subgroup.normalizer (sQA45 : Set A45) := Subgroup.zpowers_le.mpr hb0N
  set NS := Subgroup.normalizer (sQA45 : Set A45) with hNS_def
  have hNS : Nat.card NS = 1920 := card_normalizer_sQA45
  have hsub5 : ∀ {C : Subgroup A45}, C ≤ NS → Nat.card C = 5 →
      IsPGroup 5 ↥(C.subgroupOf NS) ∧ ¬ 5 ∣ (C.subgroupOf NS).index := by
    intro C hC hC5
    have hcard : Nat.card ↥(C.subgroupOf NS) = 5 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv, hC5]
    refine ⟨IsPGroup.of_card (n := 1) (by rw [hcard, pow_one]), ?_⟩
    have h := Subgroup.card_mul_index (C.subgroupOf NS)
    rw [hcard, hNS] at h
    omega
  obtain ⟨h, hh⟩ := CFSG.GroupTheory.exists_conj_of_isPGroup 5 (G := ↥NS)
    (B := B'.subgroupOf NS) (B₀ := B₀.subgroupOf NS) (hsub5 hB'N hB'5).1 (hsub5 hB₀N hB₀5).1
    (hsub5 hB'N hB'5).2 (hsub5 hB₀N hB₀5).2
  have hB'map : B₀.map (MulAut.conj (h : A45)).toMonoidHom = B' := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hbN : b ∈ NS := hB₀N hb
      have hmem : (MulAut.conj h).toMonoidHom (⟨b, hbN⟩ : ↥NS) ∈ B'.subgroupOf NS := by
        rw [← hh]
        exact ⟨⟨b, hbN⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      have := Subgroup.mem_subgroupOf.mp hmem
      simpa using this
    · intro hy
      have hyN : y ∈ NS := hB'N hy
      have hmem : (⟨y, hyN⟩ : ↥NS) ∈ B'.subgroupOf NS := Subgroup.mem_subgroupOf.mpr hy
      rw [← hh] at hmem
      obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp hmem
      refine ⟨b, Subgroup.mem_subgroupOf.mp hb, ?_⟩
      have := congrArg Subtype.val hbe
      simpa using this
  have hg0P : g0A ∈ Pp := by
    rw [Subgroup.mem_subgroupOf]
    exact g0P_mem_Q
  have hg0N : g0A ∈ Subgroup.normalizer (B₀ : Set A45) := by
    rw [hB₀_def, CFSG.GroupTheory.mem_normalizer_zpowers_iff, g0A_conj_b0A]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3
  have hg0S : g0A ∈ NS := by
    have hx : (MulAut.conj (h : A45)).toMonoidHom g0A ∈ Subgroup.normalizer (B' : Set A45) := by
      rw [← hB'map, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨g0A, hg0N, rfl⟩
    have hxP : (MulAut.conj (h : A45)).toMonoidHom g0A ∈ Pp := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hPn.conj_mem g0A hg0P h
    have hxS := hNB' _ hx hxP
    have hhN : (h : A45) ∈ NS := h.2
    have h1 := mul_mem (mul_mem (inv_mem hhN) hxS) hhN
    have e : (h : A45)⁻¹ * ((MulAut.conj (h : A45)).toMonoidHom g0A) * (h : A45) = g0A := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [e] at h1
  have htS : tA ∈ sQA45 := hgenS _ (by simp)
  have huS : uA ∈ sQA45 := hgenS _ (by simp)
  have hc := (Subgroup.mem_normalizer_iff.mp hg0S tA).mp htS
  have hcomm := isElemAbelian_sQA45.1.is_comm.comm (⟨_, hc⟩ : ↥sQA45) ⟨uA, huS⟩
  have hcomm' := congrArg Subtype.val hcomm
  simp only [Subgroup.coe_mul] at hcomm'
  exact g0A_conj_t_not_commute hcomm'

end Model

end CFSG.RankThree.GF2n.Parrott

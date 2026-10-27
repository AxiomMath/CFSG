module

public import CFSG.Quasithin.Recognition.RuTypeJ36e

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin

theorem inv_of_fixedPointFree {G : Type*} [Group G] {P : Subgroup G} [Finite P] {i : G}
    (hi2 : i * i = 1) (hiP : ∀ x ∈ P, i * x * i⁻¹ ∈ P)
    (hfix : ∀ x ∈ P, i * x = x * i → x = 1) : ∀ x ∈ P, i * x * i⁻¹ = x⁻¹ := by
  have hii : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  let f : P → P := fun x => ⟨(x : G)⁻¹ * (i * x * i⁻¹), mul_mem (inv_mem x.2) (hiP x x.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h : (x : G)⁻¹ * (i * x * i⁻¹) = (y : G)⁻¹ * (i * y * i⁻¹) := congrArg Subtype.val hxy
    have hc : i * ((y : G) * (x : G)⁻¹) = ((y : G) * (x : G)⁻¹) * i := by
      have e : i * ((y : G) * (x : G)⁻¹) * i⁻¹ = (y : G) * (x : G)⁻¹ := by
        calc i * ((y : G) * (x : G)⁻¹) * i⁻¹ = (y : G) * ((y : G)⁻¹ * (i * y * i⁻¹)) *
              ((x : G)⁻¹ * (i * x * i⁻¹))⁻¹ * (x : G)⁻¹ := by group
          _ = (y : G) * (x : G)⁻¹ := by rw [h]; group
      calc i * ((y : G) * (x : G)⁻¹) = i * ((y : G) * (x : G)⁻¹) * i⁻¹ * i := by group
        _ = ((y : G) * (x : G)⁻¹) * i := by rw [e]
    have h1 := hfix _ (mul_mem y.2 (inv_mem x.2)) hc
    exact Subtype.ext (by
      calc (x : G) = ((y : G) * (x : G)⁻¹)⁻¹ * y := by group
        _ = y := by rw [h1, inv_one, one_mul])
  have hs := Finite.injective_iff_surjective.mp hf
  intro y hy
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  have hx' : (x : G)⁻¹ * (i * x * i⁻¹) = y := congrArg Subtype.val hx
  rw [← hx']
  calc i * ((x : G)⁻¹ * (i * x * i⁻¹)) * i⁻¹ = (i * x * i⁻¹)⁻¹ * ((i * i) * x * (i⁻¹ * i⁻¹)) := by
        group
    _ = ((x : G)⁻¹ * (i * x * i⁻¹))⁻¹ := by
        rw [hi2, show i⁻¹ * i⁻¹ = (i * i)⁻¹ by group, hi2]
        group

theorem comm_of_fixedPointFree {G : Type*} [Group G] {P : Subgroup G} [Finite P] {i : G}
    (hi2 : i * i = 1) (hiP : ∀ x ∈ P, i * x * i⁻¹ ∈ P)
    (hfix : ∀ x ∈ P, i * x = x * i → x = 1) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro x hx y hy
  have h := inv_of_fixedPointFree hi2 hiP hfix
  have hxy := h (x * y) (mul_mem hx hy)
  have e : i * (x * y) * i⁻¹ = (i * x * i⁻¹) * (i * y * i⁻¹) := by group
  rw [e, h x hx, h y hy] at hxy
  have h2 : (x⁻¹ * y⁻¹)⁻¹ = x * y := by rw [hxy, inv_inv]
  rw [← h2]
  group

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G) [Finite G]

theorem card_centralizer_of_isConj {i : G} (hi : IsConj M.z i) :
    Nat.card (Subgroup.centralizer ({i} : Set G)) = Nat.card (ruH M.T) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hi
  rw [← M.centralizer_z_eq_H, ← hc]
  have e : Subgroup.centralizer ({c * M.z * c⁻¹} : Set G) =
      (Subgroup.centralizer ({M.z} : Set G)).map (MulAut.conj c).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    simp only [MulAut.conj_symm_apply]
    constructor
    · intro h
      calc c⁻¹ * x * c * M.z = c⁻¹ * (x * (c * M.z * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * M.z * c⁻¹) * x) * c := by rw [h]
        _ = M.z * (c⁻¹ * x * c) := by group
    · intro h
      calc x * (c * M.z * c⁻¹) = c * (c⁻¹ * x * c * M.z) * c⁻¹ := by group
        _ = c * (M.z * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
        _ = c * M.z * c⁻¹ * x := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem card_le_five_of_isPGroup {i : G} (hi : IsConj M.z i) {X : Subgroup G}
    (hX : X ≤ Subgroup.centralizer ({i} : Set G)) (h5 : IsPGroup 5 X) : Nat.card X ≤ 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := h5.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hX
  rw [M.card_centralizer_of_isConj hi, M.toRuData.card_H, hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra h
    have h25 : 5 ^ 2 ∣ 2 ^ 11 * 120 :=
      (pow_dvd_pow 5 (by omega : 2 ≤ k)).trans hdvd
    norm_num at h25
  rw [hk]
  calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 5 := by norm_num

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem mem_P5_of_pow_five {x : G} (hx : x ∈ G5 b)
    (hx5 : x ^ 5 = 1) : x ∈ P5 b := by
  obtain ⟨p, hp, t, ht, rfl⟩ := G5_eq_mul hbH hb5 hx
  have key : ∀ n : ℕ, ∃ p' ∈ P5 b, (p * t) ^ n = p' * t ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨p', hp', e⟩ := ih
      refine ⟨p' * (t ^ n * p * (t ^ n)⁻¹), mul_mem hp' (conj_mem_P5
        (pow_mem (M.T5_le_G5 ht) n) hp), ?_⟩
      rw [pow_succ, e]
      group
  obtain ⟨p', hp', e⟩ := key 5
  rw [hx5] at e
  have ht5 : t ^ 5 ∈ P5 b := by
    have : t ^ 5 = p'⁻¹ := by
      calc t ^ 5 = p'⁻¹ * (p' * t ^ 5) := by group
        _ = p'⁻¹ := by rw [← e, mul_one]
    rw [this]
    exact inv_mem hp'
  have h1 : t ^ 5 = 1 := eq_one_of_P5_T5 hbH hb5 ht5 (pow_mem ht 5)
  have h2 : t ^ 8 = 1 := by
    have := Subgroup.orderOf_dvd_natCard _ ht
    rw [card_T5 hbH hb5] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have h3 : t = 1 := by
    have := (pow_gcd_eq_one (a := t)).mpr ⟨h1, h2⟩
    rwa [show Nat.gcd 5 8 = 1 by norm_num, pow_one] at this
  rw [h3, mul_one]
  exact hp

theorem comm_mem_zpowers_P5
    {x y : G} (hx : x ∈ P5 b) (hy : y ∈ P5 b) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers b := by
  have h := comm_V5 hbH hb5 ((⟨x, hx⟩ : P5 b) : V5 b) ((⟨y, hy⟩ : P5 b) : V5 b)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h
  have h' : (x * y)⁻¹ * (y * x) ∈ Subgroup.zpowers b := h
  have e2 : x * y * x⁻¹ * y⁻¹ = (x * y) * ((x * y)⁻¹ * (y * x))⁻¹ * (x * y)⁻¹ := by group
  rw [e2]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (inv_mem h')
  rw [← hk]
  have hc := comm_zpowers_P5 (mul_mem hx hy) k
  rw [hc, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers b k

theorem card_P5_inf_centralizer
    {i : G} (hiz : IsConj M.z i) (hi2 : i * i = 1) (hib : i * b * i⁻¹ = b⁻¹) :
    Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP := card_P5_eq_125 hbH hb5
  have hdvd : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) ∣ 5 ^ 3 := by
    have := Subgroup.card_dvd_of_le
      (inf_le_left : P5 b ⊓ Subgroup.centralizer ({i} : Set G) ≤ P5 b)
    rwa [hP, show (125 : ℕ) = 5 ^ 3 by norm_num] at this
  obtain ⟨m, hm3, hm⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
  have hle : Nat.card (P5 b ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) ≤ 5 :=
    M.card_le_five_of_isPGroup hiz inf_le_right (IsPGroup.of_card hm)
  set C := P5 b ⊓ Subgroup.centralizer ({i} : Set G)
  have hne : Nat.card C ≠ 1 := by
    intro h1
    apply not_comm_P5 hbH hb5
    refine comm_of_fixedPointFree hi2 (fun x hx => conj_mem_P5_of_inv hib hx) fun x hx hxi => ?_
    have hxC : x ∈ C := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxi.symm⟩
    have := (Subgroup.card_eq_one.mp h1)
    rw [this] at hxC
    exact hxC
  rw [hm] at hle hne ⊢
  interval_cases m
  · exact absurd (pow_zero 5) hne
  · rfl
  · norm_num at hle
  · norm_num at hle

end Five

end RuDataM

end CFSG.Quasithin.RuType

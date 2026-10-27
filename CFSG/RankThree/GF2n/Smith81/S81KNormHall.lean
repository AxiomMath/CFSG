module

public import CFSG.GroupTheory.SolvableHallNodes
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coprime.Lemmas

public section

open scoped Pointwise

namespace CFSG.RankThree.GF2n.Smith81.D6Normalizer

theorem eq_one_of_isPGroup_two_of_odd {G : Type*} [Group G] {U : Subgroup G} (hU : IsPGroup 2 U)
    {x : G} (hx : x ∈ U) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
  have h1 : x ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hi0 : i = 0 := by
    by_contra hne
    have : Even (orderOf x) := by
      rw [hi]
      exact (Nat.even_pow.2 ⟨even_two, hne⟩)
    exact (Nat.not_even_iff_odd.2 hodd) this
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact hi

theorem odd_card_of_odd_orderOf {G : Type*} [Group G] [Finite G]
    (h : ∀ x : G, Odd (orderOf x)) : Odd (Nat.card G) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card G := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

theorem exists_mul_normalizes {G : Type*} [Group G] [Finite G] {U H B : Subgroup G}
    (hU : IsPGroup 2 U) (hH : ∀ h ∈ H, Odd (orderOf h))
    (hUB : U ≤ B) (hHB : H ≤ B) (hUn : ∀ b ∈ B, ∀ x ∈ U, b * x * b⁻¹ ∈ U)
    (hB : ∀ g ∈ B, ∃ x ∈ U, ∃ h ∈ H, g = x * h)
    (T : G) (hT : ∀ b ∈ B, T * b * T⁻¹ ∈ B) :
    ∃ n ∈ U, ∀ h ∈ H, n * T * h * (n * T)⁻¹ ∈ H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H' : Subgroup G := H.map (MulAut.conj T).toMonoidHom with hH'
  have hH'B : H' ≤ B := by
    rintro _ ⟨h, hh, rfl⟩
    exact hT h (hHB hh)
  have hH'odd : ∀ h ∈ H', Odd (orderOf h) := by
    rintro _ ⟨h, hh, rfl⟩
    have : orderOf ((MulAut.conj T).toMonoidHom h) = orderOf h :=
      orderOf_injective _ (MulAut.conj T).injective h
    rw [this]
    exact hH h hh
  let N : Subgroup B := U.subgroupOf B
  let H₁ : Subgroup B := H.subgroupOf B
  let K₁ : Subgroup B := H'.subgroupOf B
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hUn g g.2 n hn
    simpa using this⟩
  have hNp : IsPGroup 2 N := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUB).symm
  have hNs : Group.IsSolvable N := by
    haveI : Group.IsNilpotent N := IsPGroup.isNilpotent hNp
    infer_instance
  have hdisj : ∀ X : Subgroup G, (∀ x ∈ X, Odd (orderOf x)) → N ⊓ X.subgroupOf B = ⊥ := by
    intro X hX
    rw [eq_bot_iff]
    rintro n ⟨hn1, hn2⟩
    have hn1' : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn1
    have hn2' : (n : G) ∈ X := Subgroup.mem_subgroupOf.1 hn2
    have := eq_one_of_isPGroup_two_of_odd hU hn1' (hX _ hn2')
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hNH' : N ⊓ H₁ = ⊥ := hdisj H hH
  have hNK' : N ⊓ K₁ = ⊥ := hdisj H' hH'odd
  have hNH : (N : Set B) * (H₁ : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨x, hx, h, hh, hgxh⟩ := hB g g.2
    exact Set.mem_mul.2 ⟨⟨x, hUB hx⟩, Subgroup.mem_subgroupOf.2 hx, ⟨h, hHB hh⟩,
      Subgroup.mem_subgroupOf.2 hh, Subtype.ext hgxh.symm⟩
  have hcompH : Subgroup.IsComplement' N H₁ :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hNH') hNH
  have hcardH : Nat.card N * Nat.card H₁ = Nat.card B := hcompH.card_mul_card
  have hcardK : Nat.card K₁ = Nat.card H₁ := by
    have e1 : Nat.card K₁ = Nat.card H' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'B).toEquiv
    have e2 : Nat.card H₁ = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv
    have e3 : Nat.card H' = Nat.card H := Subgroup.card_map_of_injective (MulAut.conj T).injective
    omega
  have hcompK : Subgroup.IsComplement' N K₁ :=
    Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hcardK, hcardH])
      (disjoint_iff.2 hNK')
  have hNK : (N : Set B) * (K₁ : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := hcompK.2 g
    exact Set.mem_mul.2 ⟨a, a.2, b, b.2, hab⟩
  have hindex : N.index = Nat.card H₁ := by
    have h1 := Subgroup.card_mul_index N
    have hN0 : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hN0 (h1.trans hcardH.symm)
  have hH1odd : Odd (Nat.card H₁) := by
    refine odd_card_of_odd_orderOf fun x => ?_
    have h1 : orderOf (x : B) = orderOf x := Subgroup.orderOf_coe x
    have h2 : orderOf ((x : B) : G) = orderOf (x : B) := Subgroup.orderOf_coe (x : B)
    rw [← h1, ← h2]
    exact hH _ (Subgroup.mem_subgroupOf.1 x.2)
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hNp
    rw [ha, hindex]
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hH1odd)
  obtain ⟨n, hn, hK⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N hNs hcop
    hNH hNK hNH' hNK'
  refine ⟨(n : G), Subgroup.mem_subgroupOf.1 hn, fun h hh => ?_⟩
  have hmem : (⟨T * h * T⁻¹, hT h (hHB hh)⟩ : B) ∈ K₁ :=
    Subgroup.mem_subgroupOf.2 ⟨h, hh, by simp [MulAut.conj_apply]⟩
  rw [hK] at hmem
  obtain ⟨h', hh', hconj⟩ := Subgroup.mem_map.1 hmem
  have h3 := congrArg Subtype.val hconj
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h3
  have hh'H : (h' : G) ∈ H := Subgroup.mem_subgroupOf.1 hh'
  have e : (n : G) * T * h * ((n : G) * T)⁻¹ = h' := by
    have : (n : G) * T * h * ((n : G) * T)⁻¹ = (n : G) * (T * h * T⁻¹) * (n : G)⁻¹ := by group
    rw [this, ← h3]
    group
  rw [e]
  exact hh'H

theorem conj_inv_mem_of_finite {G : Type*} [Group G] [Finite G] {H : Subgroup G} {T : G}
    (hT : ∀ h ∈ H, T * h * T⁻¹ ∈ H) : ∀ h ∈ H, T⁻¹ * h * T ∈ H := by
  have hle : H.map (MulAut.conj T).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact hT h hh
  have heq : H.map (MulAut.conj T).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj T).injective])
  intro h hh
  rw [← heq] at hh
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  simpa [MulAut.conj_apply, mul_assoc] using hh₀

theorem pow_mul_pow_inv_mem {G : Type*} [Group G] {Γ : Subgroup G} {T D c : G} (hc : c ∈ Γ)
    (hTD : T = c⁻¹ * D) (hD : D ∈ Subgroup.normalizer (Γ : Set G)) (n : ℕ) :
    T ^ n * (D ^ n)⁻¹ ∈ Γ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hDn : D ^ n ∈ Subgroup.normalizer (Γ : Set G) := pow_mem hD n
    have hconj : D ^ n * c⁻¹ * (D ^ n)⁻¹ ∈ Γ :=
      (Subgroup.mem_normalizer_iff.1 hDn _).1 (inv_mem hc)
    have e : T ^ (n + 1) * (D ^ (n + 1))⁻¹ =
        (T ^ n * (D ^ n)⁻¹) * (D ^ n * c⁻¹ * (D ^ n)⁻¹) := by
      rw [pow_succ T n, pow_succ D n, hTD]
      group
    rw [e]
    exact mul_mem ih hconj

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {Γ : Subgroup G} {T D c : G}
    (hc : c ∈ Γ) (hTD : T = c⁻¹ * D) (hD : D ∈ Subgroup.normalizer (Γ : Set G)) {m k : ℕ}
    (hm : Odd m) (hDm : D ^ m = 1) (hT : T ^ (2 ^ k) = 1) : T ∈ Γ := by
  have h1 : T ^ m ∈ Γ := by
    have := pow_mul_pow_inv_mem hc hTD hD m
    rwa [hDm, inv_one, mul_one] at this
  have hcop : IsCoprime (m : ℤ) ((2 ^ k : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hm)
  obtain ⟨a, b, hab⟩ := hcop
  have e : T = (T ^ m) ^ a * (T ^ (2 ^ k)) ^ b := by
    have h2 : (T ^ m) ^ a * (T ^ (2 ^ k)) ^ b = T ^ (a * (m : ℤ) + b * ((2 ^ k : ℕ) : ℤ)) := by
      rw [← zpow_natCast T m, ← zpow_natCast T (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add]
      congr 1
      ring
    rw [h2, hab, zpow_one]
  rw [e, hT, one_zpow, mul_one]
  exact zpow_mem h1 a

end CFSG.RankThree.GF2n.Smith81.D6Normalizer

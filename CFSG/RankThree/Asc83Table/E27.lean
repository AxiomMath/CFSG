module

public import CFSG.RankThree.Asc83Table.GL33
public import CFSG.RankThree.Asc83Table.Reduction
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup

@[expose] def IsE9Z8 (A : Type*) [Group A] : Prop :=
  Nat.card A = 72 ∧ ∃ (E : Subgroup A) (_ : E.Normal), IsElementaryAbelian 3 E ∧
    Nat.card E = 9 ∧ IsCyclic (A ⧸ E) ∧ Nat.card (A ⧸ E) = 8

theorem comap_equiv_eq_map_symm'' {A A' : Type*} [Group A] [Group A'] (f : A ≃* A')
    (E : Subgroup A') : E.comap f.toMonoidHom = E.map f.symm.toMonoidHom := by
  ext a
  constructor
  · intro ha
    exact ⟨f a, ha, f.symm_apply_apply a⟩
  · rintro ⟨b, hb, rfl⟩
    change f (f.symm b) ∈ E
    rwa [f.apply_symm_apply]

theorem IsE9Z8.of_mulEquiv {A A' : Type*} [Group A] [Group A'] (f : A ≃* A') (h : IsE9Z8 A') :
    IsE9Z8 A := by
  obtain ⟨hcard, E, hE, hEa, hE9, hcyc, hq⟩ := h
  have hmap : (E.comap f.toMonoidHom).map f.toMonoidHom = E :=
    map_comap_eq_self_of_surjective f.surjective E
  let q : A ⧸ E.comap f.toMonoidHom ≃* A' ⧸ E := QuotientGroup.congr _ _ f hmap
  refine ⟨by rw [Nat.card_congr f.toEquiv, hcard], E.comap f.toMonoidHom, hE.comap _, ?_, ?_,
    isCyclic_of_surjective q.symm.toMonoidHom q.symm.surjective, ?_⟩
  · have := IsElementaryAbelian.map_hom f.symm.toMonoidHom hEa
    rwa [← comap_equiv_eq_map_symm''] at this
  · rw [comap_equiv_eq_map_symm'', card_map_of_injective f.symm.injective, hE9]
  · rw [Nat.card_congr q.toEquiv, hq]

section Basis

variable {G : Type*} [Group G] {x : Fin 3 → G} (hx : ∀ i, x i ^ 3 = 1)
  (hc : ∀ i j, Commute (x i) (x j))
include hx hc

theorem basisProd_mem (a : Fin 3 → ZMod 3) : basisProd x a ∈ closure (Set.range x) := by
  have := coe_basisHom hx hc (Multiplicative.ofAdd a)
  rw [toAdd_ofAdd] at this
  rw [← this]
  exact Subtype.mem _

theorem exists_basisProd {g : G} (hg : g ∈ closure (Set.range x)) : ∃ a, g = basisProd x a := by
  obtain ⟨a, ha⟩ := basisHom_surjective hx hc ⟨g, hg⟩
  exact ⟨Multiplicative.toAdd a, by rw [← coe_basisHom hx hc, ha]⟩

theorem isElementaryAbelian_closure : IsElementaryAbelian 3 (closure (Set.range x)) := by
  have hcomm : IsMulCommutative (closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  have hab : ∀ a ∈ closure (Set.range x), ∀ b ∈ closure (Set.range x), a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : closure (Set.range x)) ⟨b, hb⟩)
  rw [isElementaryAbelian_iff]
  refine ⟨hab, fun a ha => ?_⟩
  induction ha using closure_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    exact hx i
  | one => exact one_pow 3
  | mul a b ha hb h₁ h₂ => rw [(show Commute a b from hab a ha b hb).mul_pow, h₁, h₂, one_mul]
  | inv a _ h => rw [inv_pow, h, inv_one]

theorem mem_normalizer_of_basis [Finite G] {g : G} {M : GL33}
    (hM : ∀ j, g * x j * g⁻¹ = basisProd x fun i => (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j) :
    g ∈ normalizer (closure (Set.range x) : Set G) :=
  mem_normalizer_closure_of_conj_mem (by rintro _ ⟨j, rfl⟩; rw [hM j]; exact basisProd_mem hx hc _)

end Basis

@[expose] def t33 : Fin 3 → GL33 := ![t33A, t33B, t33C]

section Automizer

variable {G : Type*} [Group G] [Finite G] {x : Fin 3 → G} (hx : ∀ i, x i ^ 3 = 1)
  (hc : ∀ i j, Commute (x i) (x j)) (hinj : Function.Injective (basisProd x)) {h : Fin 3 → G}
  (hh : ∀ k j, h k * x j * (h k)⁻¹ =
    basisProd x fun i => (t33 k : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j)
  (hN : Nat.card (normalizer (closure (Set.range x) : Set G)) ≤ 1944)

local notation "B" => closure (Set.range x)

local notation "ρ" => rho (basisEquiv hx hc hinj)

include hx hc hinj

omit [Finite G] in
theorem card_basis : Nat.card B = 27 := by
  rw [card_closure_basis hx hc hinj]; norm_num

theorem card_ker_ge : 27 ≤ Nat.card (MonoidHom.ker ρ) := by
  rw [ker_rho]
  have hcomm : IsMulCommutative B :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  have hle : Subgroup.subgroupOf B (normalizer (B : Set G)) ≤
      (centralizer (B : Set G)).subgroupOf (normalizer (B : Set G)) :=
    fun g hg => by
      rw [mem_subgroupOf] at hg ⊢
      exact le_centralizer (closure (Set.range x)) hg
  have hcard : Nat.card (Subgroup.subgroupOf B (normalizer (B : Set G))) = 27 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, card_basis hx hc hinj]
  rw [← hcard]
  exact card_le_of_le hle

omit [Finite G] in
theorem card_normalizer_eq : Nat.card (normalizer (B : Set G)) =
    Nat.card (MonoidHom.ker ρ) * Nat.card (MonoidHom.range ρ) := by
  rw [card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker ρ),
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm]

include hh

omit hinj in
theorem mem_normalizer_h (k : Fin 3) : h k ∈ normalizer (B : Set G) :=
  mem_normalizer_of_basis hx hc (hh k)

theorem rho_h (k : Fin 3) : ρ ⟨h k, mem_normalizer_h hx hc hh k⟩ = t33 k :=
  Units.ext (rho_basis_eq hx hc hinj _ _ (hh k))

theorem t33_mem_range (k : Fin 3) : t33 k ∈ (MonoidHom.range ρ) := ⟨_, rho_h hx hc hinj hh k⟩

theorem seventy_two_le_range : 72 ≤ Nat.card (MonoidHom.range ρ) := by
  have hdvd := seventy_two_dvd (t33_mem_range hx hc hinj hh 0) (t33_mem_range hx hc hinj hh 1)
    (t33_mem_range hx hc hinj hh 2)
  exact Nat.le_of_dvd Nat.card_pos hdvd

include hN

theorem card_range : Nat.card (MonoidHom.range ρ) = 72 := by
  have h1 := card_normalizer_eq hx hc hinj
  have h2 := card_ker_ge hx hc hinj
  have h3 := seventy_two_le_range hx hc hinj hh
  have h4 : 27 * Nat.card (MonoidHom.range ρ) ≤ 27 * 72 := by
    calc 27 * Nat.card (MonoidHom.range ρ)
        ≤ Nat.card (MonoidHom.ker ρ) * Nat.card (MonoidHom.range ρ) := Nat.mul_le_mul_right _ h2
      _ = Nat.card (normalizer (B : Set G)) := h1.symm
      _ ≤ 27 * 72 := by norm_num; exact hN
  exact le_antisymm (Nat.le_of_mul_le_mul_left h4 (by norm_num)) h3

theorem card_ker : Nat.card (MonoidHom.ker ρ) = 27 := by
  have h1 := card_normalizer_eq hx hc hinj
  have h2 := card_ker_ge hx hc hinj
  rw [card_range hx hc hinj hh hN] at h1
  have : Nat.card (MonoidHom.ker ρ) * 72 ≤ 27 * 72 := by rw [← h1]; norm_num; exact hN
  exact le_antisymm (Nat.le_of_mul_le_mul_right this (by norm_num)) h2

theorem range_eq : (MonoidHom.range ρ) = Subgroup.closure {t33A, t33B, t33C} := by
  have hle : Subgroup.closure ({t33A, t33B, t33C} : Set GL33) ≤ (MonoidHom.range ρ) := by
    rw [closure_le]
    rintro s (rfl | rfl | rfl)
    · exact t33_mem_range hx hc hinj hh 0
    · exact t33_mem_range hx hc hinj hh 1
    · exact t33_mem_range hx hc hinj hh 2
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_range hx hc hinj hh hN]
  exact Nat.le_of_dvd Nat.card_pos (seventy_two_dvd (subset_closure (by simp))
    (subset_closure (by simp)) (subset_closure (by simp)))

theorem e9t_le_range : e9t.sub ≤ (MonoidHom.range ρ) := by
  rw [range_eq hx hc hinj hh hN, e9t_sub]
  refine Subgroup.closure_mono fun s hs => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
  tauto

theorem isE9Z8_range : IsE9Z8 (MonoidHom.range ρ) := by
  set R := (MonoidHom.range ρ)
  have hR : R = Subgroup.closure {t33A, t33B, t33C} := range_eq hx hc hinj hh hN
  have hle : e9t.sub ≤ R := e9t_le_range hx hc hinj hh hN
  set E := e9t.sub.subgroupOf R
  have hnorm : E.Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hle, hR]
    exact closure_le_normalizer
  have hE9 : Nat.card E = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact e9t.card
  have hR72 : Nat.card R = 72 := card_range hx hc hinj hh hN
  have hq8 : Nat.card (R ⧸ E) = 8 := by
    have h := card_eq_card_quotient_mul_card_subgroup E
    rw [hR72, hE9] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 9) (h.symm.trans (by norm_num))
  have hEa : IsElementaryAbelian 3 E := by
    have h := e9t.isElementaryAbelian
    rw [isElementaryAbelian_iff] at h ⊢
    refine ⟨fun a ha b hb => Subtype.ext (h.1 a ha b hb), fun a ha => Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.2 a ha
  have hC : t33C ∈ R := by rw [hR]; exact subset_closure (by simp)
  refine ⟨hR72, E, hnorm, hEa, hE9, ?_, hq8⟩
  set c : R ⧸ E := QuotientGroup.mk ⟨t33C, hC⟩
  have hc8 : c ^ 2 ^ (2 + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, show (2 : ℕ) ^ (2 + 1) = 8 by norm_num]
    rw [show (⟨t33C, hC⟩ : R) ^ 8 = 1 from Subtype.ext t33C_pow_eight, QuotientGroup.mk_one]
  have hc4 : ¬ c ^ 2 ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, QuotientGroup.eq_one_iff,
      mem_subgroupOf, Subgroup.coe_pow]
    intro hmem
    have h3 : (t33C ^ 4) ^ 3 = 1 := (isElementaryAbelian_iff.1 e9t.isElementaryAbelian).2 _ hmem
    have h2 : (t33C ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact t33C_pow_eight
    apply t33C_pow_four
    calc t33C ^ 4 = (t33C ^ 4) ^ 3 * ((t33C ^ 4) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have hord : orderOf c = 8 := orderOf_eq_prime_pow hc4 hc8
  exact isCyclic_of_orderOf_eq_card c (by rw [hord, hq8])

theorem isE9Z8_automizer : IsE9Z8 (Automizer B) :=
  IsE9Z8.of_mulEquiv (automizerEquivRange (basisEquiv hx hc hinj)) (isE9Z8_range hx hc hinj hh hN)

theorem ker_eq : (MonoidHom.ker ρ) = Subgroup.subgroupOf B (normalizer (B : Set G)) := by
  have hle : Subgroup.subgroupOf B (normalizer (B : Set G)) ≤ (MonoidHom.ker ρ) := by
    rw [ker_rho]
    intro g hg
    rw [mem_subgroupOf] at hg ⊢
    have hcomm : IsMulCommutative B :=
      isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
    exact le_centralizer (closure (Set.range x)) hg
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_ker hx hc hinj hh hN, Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv,
    card_basis hx hc hinj]

theorem card_sylow_basis :
    Nat.card ((e9t.sub.comap ρ).map (normalizer (B : Set G)).subtype) = 243 := by
  rw [card_map_of_injective Subtype.val_injective]
  set K := e9t.sub.comap ρ
  have hker : (MonoidHom.ker ρ) ≤ K := fun g hg => by
    rw [mem_comap, (MonoidHom.mem_ker).1 hg]; exact one_mem _
  have hrange : (MonoidHom.domRestrict ρ K).range = e9t.sub := by
    rw [MonoidHom.domRestrict_range, map_comap_eq, inf_eq_right.2 (e9t_le_range hx hc hinj hh hN)]
  have hkerK : (MonoidHom.domRestrict ρ K).ker = (MonoidHom.ker ρ).subgroupOf K :=
    MonoidHom.ker_domRestrict K ρ
  have h1 := card_eq_card_quotient_mul_card_subgroup (MonoidHom.domRestrict ρ K).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (MonoidHom.domRestrict ρ K)).toEquiv,
    hrange,
    hkerK, Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv, card_ker hx hc hinj hh hN] at h1
  rw [h1, show Nat.card e9t.sub = 9 from e9t.card]

variable (hΩ : ∀ a : Fin 3 → ZMod 3, ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) →
  (basisProd x a * h 0 ^ i * h 1 ^ j) ^ 3 ≠ 1)
include hΩ

theorem mem_of_pow_three {g : G} (hg : g ∈ (e9t.sub.comap ρ).map (normalizer (B : Set G)).subtype)
    (h3 : g ^ 3 = 1) : g ∈ B := by
  obtain ⟨n, hn, rfl⟩ := hg
  rw [SetLike.mem_coe, mem_comap] at hn
  obtain ⟨i, j, hi, hj, hij⟩ := e9t.exists_pow_mul_pow hn
  set h₀ : normalizer (B : Set G) := ⟨h 0, mem_normalizer_h hx hc hh 0⟩
  set h₁ : normalizer (B : Set G) := ⟨h 1, mem_normalizer_h hx hc hh 1⟩
  have hρ : ρ (n * (h₀ ^ i * h₁ ^ j)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, rho_h hx hc hinj hh 0,
      rho_h hx hc hinj hh 1, hij, e9t_a, e9t_b]
    exact mul_inv_cancel _
  rw [← MonoidHom.mem_ker, ker_eq hx hc hinj hh hN, mem_subgroupOf] at hρ
  obtain ⟨a, ha⟩ := exists_basisProd hx hc hρ
  have hg : (n : G) = basisProd x a * h 0 ^ i * h 1 ^ j := by
    rw [mul_assoc, ← ha]
    simp only [h₀, h₁, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    group
  change (n : G) ^ 3 = 1 at h3
  change (n : G) ∈ B
  by_cases h0 : i = 0 ∧ j = 0
  · rw [h0.1, h0.2] at hg
    simp only [pow_zero, mul_one] at hg
    rw [hg]
    exact basisProd_mem hx hc a
  · exact absurd (hg ▸ h3) (hΩ a i j hi hj (by tauto))

variable (hG : (Nat.card G).factorization 3 = 5)
include hG

theorem exists_conj_le_basis {A : Subgroup G} (hA : IsElementaryAbelian 3 A) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ B := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_map_conj_le (p := 3)
    (by rw [card_sylow_basis hx hc hinj hh hN, hG]; norm_num) (isPGroup_of_isElementaryAbelian hA)
  refine ⟨g, fun y hy => mem_of_pow_three hx hc hinj hh hN hΩ (hg hy) ?_⟩
  exact (isElementaryAbelian_iff.1 (IsElementaryAbelian.map_hom (MulAut.conj g).toMonoidHom hA)).2
    y hy

theorem e27_pRank : CFSG.pRank 3 G = 3 := by
  refine pRank_eq (by norm_num) (isElementaryAbelian_closure hx hc)
    (by rw [card_basis hx hc hinj]; norm_num) fun A hA => ?_
  obtain ⟨g, hg⟩ := exists_conj_le_basis hx hc hinj hh hN hΩ hG hA
  have := card_le_of_le hg
  rw [card_map_conj, card_basis hx hc hinj] at this
  exact this

theorem e27_automizer {A : Subgroup G} (hA : IsElementaryAbelian 3 A) (h27 : Nat.card A = 27) :
    IsE9Z8 (Automizer A) := by
  obtain ⟨g, hg⟩ := exists_conj_le_basis hx hc hinj hh hN hΩ hG hA
  have heq : A.map (MulAut.conj g).toMonoidHom = B :=
    eq_of_le_of_card_ge hg (by rw [card_map_conj, h27, card_basis hx hc hinj])
  exact IsE9Z8.of_mulEquiv ((automizerCongr (MulAut.conj g) A).trans (automizerOfEq heq))
    (isE9Z8_automizer hx hc hinj hh hN)

end Automizer

section Transport

variable {G : Type*} [Group G] {L : Type*} [Group L]

theorem pRank_congr {p : ℕ} (e : L ≃* G) : CFSG.pRank p L = CFSG.pRank p G := by
  unfold CFSG.pRank
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, hcard⟩
    exact ⟨A.map e.toMonoidHom, IsElementaryAbelian.map_hom _ hA,
      by rw [card_map_of_injective e.injective, hcard]⟩
  · rintro ⟨A, hA, hcard⟩
    exact ⟨A.map e.symm.toMonoidHom, IsElementaryAbelian.map_hom _ hA,
      by rw [card_map_of_injective e.symm.injective, hcard]⟩

theorem e27_transport (e : L ≃* G) (hp : CFSG.pRank 3 G = 3)
    (ha : ∀ A : Subgroup G, IsElementaryAbelian 3 A → Nat.card A = 27 → IsE9Z8 (Automizer A)) :
    CFSG.pRank 3 L = 3 ∧
      ∀ A : Subgroup L, IsElementaryAbelian 3 A → Nat.card A = 27 → IsE9Z8 (Automizer A) :=
  ⟨(pRank_congr e).trans hp, fun A hA h27 => IsE9Z8.of_mulEquiv (automizerCongr e A)
    (ha _ (IsElementaryAbelian.map_hom e.toMonoidHom hA)
      (by rw [card_map_of_injective e.injective, h27]))⟩

end Transport

end CFSG.RankThree.Asc83Table

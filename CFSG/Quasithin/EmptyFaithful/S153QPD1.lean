module

public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.QP

open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G] [Finite G]

theorem eq_top_of_sup_isPGroup_of_isPerfect [Group.IsPerfect G] {X U : Subgroup G}
    (hU : IsPGroup 2 U) (hN : U ≤ Subgroup.normalizer (X : Set G)) (hsup : X ⊔ U = ⊤) : X = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN : X.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le (Subgroup.le_normalizer) hN
  let f : U →* G ⧸ X := (QuotientGroup.mk' X).comp U.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : g ∈ X ⊔ U := by rw [hsup]; trivial
    have h2 : g ∈ ((X ⊔ U : Subgroup G) : Set G) := hg
    rw [Subgroup.normal_mul X U] at h2
    obtain ⟨x, hx, u, hu, rfl⟩ := h2
    refine ⟨⟨u, hu⟩, ?_⟩
    show (QuotientGroup.mk u : G ⧸ X) = QuotientGroup.mk (x * u)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).2 hx, one_mul]
  have hp : IsPGroup 2 (G ⧸ X) := IsPGroup.of_surjective hU f hf
  have hnil := hp.isNilpotent
  have hsolv : Group.IsSolvable (G ⧸ X) := inferInstance
  have hperf : Group.IsPerfect (G ⧸ X) := by
    rw [Group.isPerfect_def, commutator_def]
    have := Group.isPerfect_def.1 (inferInstance : Group.IsPerfect G)
    rw [commutator_def] at this
    have h3 := Subgroup.map_commutator (⊤ : Subgroup G) ⊤ (QuotientGroup.mk' X)
    rw [this, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective X)] at h3
    exact h3.symm
  have htop : ∀ n, derivedSeries (G ⧸ X) n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def]; exact Group.isPerfect_def.1 hperf
  obtain ⟨n, hn⟩ := hsolv.solvable
  rw [htop] at hn
  rw [eq_top_iff]
  intro g _
  have h1 : (QuotientGroup.mk g : G ⧸ X) ∈ (⊥ : Subgroup (G ⧸ X)) := by rw [← hn]; trivial
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
  exact h1

end Perfect

section Cover

theorem not_isPGroup_two_of_card_sixty {N : Type*} [Group N] (hN : Nat.card N = 60) :
    ¬ IsPGroup 2 N := by
  intro h
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hN] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem card_dvd_two_pow_mul_of_surjective {X H N : Type*} [Group X] [Finite X] [Group H] [Group N]
    [Finite N] (φ : X →* H) (hφ : Function.Surjective φ) (θ : X →* N) (hθ : Function.Surjective θ)
    (hk : IsPGroup 2 θ.ker) (hN : Nat.card N = 60) : ∃ b : ℕ, Nat.card H ∣ 2 ^ b * 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card H ∣ Nat.card X := Subgroup.card_dvd_of_surjective hφ
  have h2 : Nat.card X = Nat.card (X ⧸ θ.ker) * Nat.card θ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have h3 : Nat.card (X ⧸ θ.ker) = Nat.card N :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv
  obtain ⟨b, hb⟩ := hk.exists_card_eq
  refine ⟨b, ?_⟩
  rw [h2, h3, hN, hb, mul_comm] at h1
  exact h1

theorem exists_orderOf_five {X N : Type*} [Group X] [Finite X] [Group N] [Finite N]
    (hN : Nat.card N = 60) (θ : X →* N) (hθ : Function.Surjective θ) : ∃ a : X, orderOf a = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 (by rw [hN]; norm_num)
  obtain ⟨x, rfl⟩ := hθ y
  have hdvd : 5 ∣ orderOf x := hy ▸ orderOf_map_dvd θ x
  exact ⟨x ^ (orderOf x / 5), orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd⟩

theorem isPerfect_of_simple_card_sixty {N : Type*} [Group N] [IsSimpleGroup N] [Finite N]
    (hN : Nat.card N = 60) : Group.IsPerfect N := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator N) with h | h
  · exfalso
    have hcomm : ∀ a b : N, a * b = b * a := by
      intro a b
      have : ⁅a, b⁆ ∈ commutator N := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 (by rw [hN]; norm_num)
    have hnorm : (Subgroup.zpowers a).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [show g * n * g⁻¹ = n by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]]
      exact hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers a) with h1 | h1
    · have : orderOf a = 1 := by
        rw [← Nat.card_zpowers, h1, Subgroup.card_bot]
      omega
    · have : orderOf a = 60 := by
        rw [← Nat.card_zpowers, h1, Subgroup.card_top, hN]
      omega
  · exact h

theorem not_isSolvable_of_simple_card_sixty {N : Type*} [Group N] [IsSimpleGroup N] [Finite N]
    (hN : Nat.card N = 60) : ¬ Group.IsSolvable N := by
  intro hs
  have hperf := isPerfect_of_simple_card_sixty (N := N) hN
  have htop : ∀ n, derivedSeries N n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def]; exact Group.isPerfect_def.1 hperf
  obtain ⟨n, hn⟩ := hs.solvable
  rw [htop] at hn
  have hsub : Subsingleton N := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Subgroup N) := by rw [← hn]; trivial
    have hb : b ∈ (⊥ : Subgroup N) := by rw [← hn]; trivial
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have : Nat.card N = 1 := Nat.card_unique
  omega

end Cover

end CFSG.Quasithin.QP

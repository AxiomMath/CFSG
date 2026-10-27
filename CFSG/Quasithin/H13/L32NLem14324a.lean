module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.H13.L14324

open scoped Pointwise
open CFSG.Quasithin

theorem false_of_orderOf_four {Γ : Type*} [Group Γ] [Finite Γ] {X : Subgroup Γ}
    (hsq : ∀ x ∈ X, x * x = 1) {g : Γ} (hg : orderOf g = 4) {n m : ℕ}
    (hX : Nat.card X = 2 ^ n) (hΓ : Nat.card Γ = 2 ^ n * m) (hm : ¬ 2 ∣ m) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  have hfac : (Nat.card Γ).factorization 2 = n := by
    rw [hΓ, Nat.factorization_mul (pow_ne_zero n two_ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  let P : Sylow 2 Γ := Sylow.ofCard X (by rw [hX, hfac])
  have hg2 : IsPGroup 2 (Subgroup.zpowers g) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_zpowers, hg]
    norm_num
  obtain ⟨Q, hQ⟩ := hg2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Γ Q P
  have hgQ : g ∈ (Q : Subgroup Γ) := hQ (Subgroup.mem_zpowers g)
  have hmem : MulAut.conj c • g ∈ MulAut.conj c • (Q : Subgroup Γ) :=
    Subgroup.smul_mem_pointwise_smul g _ _ hgQ
  rw [← Sylow.coe_subgroup_smul, hc] at hmem
  have hcg : c * g * c⁻¹ ∈ X := hmem
  have h1 := hsq _ hcg
  have h2 : g * g = 1 := by
    have : c * (g * g) * c⁻¹ = 1 := by
      calc c * (g * g) * c⁻¹ = c * g * c⁻¹ * (c * g * c⁻¹) := by group
        _ = 1 := h1
    have := congrArg (fun y => c⁻¹ * y * c) this
    simpa [mul_assoc] using this
  have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rw [hg] at h3
  norm_num at h3

theorem le_of_two_pow_dvd {n m k : ℕ} (hm : ¬ 2 ∣ m) (h : 2 ^ k ∣ 2 ^ n * m) : k ≤ n := by
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm)
  have h2 : 2 ^ k ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2

theorem false_of_two_pow_le {Γ : Type*} [Group Γ] [Finite Γ] {X : Subgroup Γ}
    (hsq : ∀ x ∈ X, x * x = 1) {g : Γ} (hg : orderOf g = 4) {n m k : ℕ}
    (hk : Nat.card X = 2 ^ k) (hle : 2 ^ n ≤ Nat.card X) (hΓ : Nat.card Γ = 2 ^ n * m)
    (hm : ¬ 2 ∣ m) : False := by
  have hdvd : 2 ^ k ∣ 2 ^ n * m := hk ▸ hΓ ▸ Subgroup.card_subgroup_dvd_card X
  have hkn := le_of_two_pow_dvd hm hdvd
  have hnk : n ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp (hk ▸ hle)
  exact false_of_orderOf_four hsq hg (n := n) (m := m) (by rw [hk, le_antisymm hkn hnk]) hΓ hm

theorem false_of_two_pow_lt {Γ : Type*} [Group Γ] [Finite Γ] {X : Subgroup Γ} {n m k : ℕ}
    (hk : Nat.card X = 2 ^ k) (hlt : 2 ^ n < Nat.card X) (hΓ : Nat.card Γ = 2 ^ n * m)
    (hm : ¬ 2 ∣ m) : False := by
  have hdvd : 2 ^ k ∣ 2 ^ n * m := hk ▸ hΓ ▸ Subgroup.card_subgroup_dvd_card X
  have hkn := le_of_two_pow_dvd hm hdvd
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hkn
  omega

variable {G : Type*} [Group G]

theorem card_subgroupOf_of_le {X Γ : Subgroup G} (h : X ≤ Γ) :
    Nat.card (X.subgroupOf Γ) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem sq_subgroupOf {X Γ : Subgroup G} (hsq : ∀ x ∈ X, x * x = 1) :
    ∀ x ∈ X.subgroupOf Γ, x * x = 1 := fun _ hx =>
  Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.mp hx))

theorem orderOf_c7 : orderOf (Equiv.swap (0 : Fin 7) 3 * Equiv.swap 0 2 * Equiv.swap 0 1) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem orderOf_c5 : orderOf (Equiv.swap (0 : Fin 5) 3 * Equiv.swap 0 2 * Equiv.swap 0 1) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

@[expose] def a6Four : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap (0 : Fin 6) 3 * Equiv.swap 0 2 * Equiv.swap 0 1 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem orderOf_a6Four : orderOf a6Four = 4 := by
  rw [← orderOf_injective (alternatingGroup (Fin 6)).subtype Subtype.val_injective,
    orderOf_eq_iff (by norm_num)]
  decide

section Concl

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem finite_gl : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

theorem false_of_concl8 (hXΓ : X ≤ Γ) (hsq : ∀ x ∈ X, x * x = 1) {k : ℕ}
    (hk : Nat.card X = 2 ^ k) (h16 : 16 ≤ Nat.card X) (h8 : G112Concl8 B Γ X) : False := by
  have := finite_gl (V := V)
  obtain ⟨-, ⟨e⟩, -⟩ := h8
  have hΓ : Nat.card Γ = 2 ^ 4 * 315 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine false_of_two_pow_le (X := X.subgroupOf Γ) (sq_subgroupOf hsq)
    (g := e.symm (Equiv.swap (0 : Fin 7) 3 * Equiv.swap 0 2 * Equiv.swap 0 1)) ?_ (k := k)
    (by rw [card_subgroupOf_of_le hXΓ, hk]) (by rw [card_subgroupOf_of_le hXΓ]; omega) hΓ
    (by decide)
  rw [MulEquiv.orderOf_eq, orderOf_c7]

theorem false_of_concl9 (hXΓ : X ≤ Γ) (hsq : ∀ x ∈ X, x * x = 1) {k : ℕ}
    (hk : Nat.card X = 2 ^ k) (h16 : 16 ≤ Nat.card X) (h9 : G112Concl9 Γ) : False := by
  have := finite_gl (V := V)
  obtain ⟨-, h9⟩ := h9
  rcases h9 with h9 | h9
  · obtain ⟨e⟩ := h9
    have hΓ : Nat.card Γ = 2 ^ 4 * 45 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    refine false_of_two_pow_le (X := X.subgroupOf Γ) (sq_subgroupOf hsq)
      (g := e.symm (1, Equiv.swap (0 : Fin 5) 3 * Equiv.swap 0 2 * Equiv.swap 0 1)) ?_ (k := k)
      (by rw [card_subgroupOf_of_le hXΓ, hk]) (by rw [card_subgroupOf_of_le hXΓ]; omega) hΓ
      (by decide)
    rw [MulEquiv.orderOf_eq, Prod.orderOf, orderOf_one, orderOf_c5]
    rfl
  · obtain ⟨e⟩ := h9
    have hΓ : Nat.card Γ = 2 ^ 3 * 45 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact false_of_two_pow_lt (X := X.subgroupOf Γ) (k := k)
      (by rw [card_subgroupOf_of_le hXΓ, hk]) (by rw [card_subgroupOf_of_le hXΓ]; omega) hΓ
      (by decide)

theorem false_of_concl10 (hXΓ : X ≤ Γ) (hsq : ∀ x ∈ X, x * x = 1) {k : ℕ}
    (hk : Nat.card X = 2 ^ k) (h16 : 16 ≤ Nat.card X) (h10 : G112Concl10 Γ X) : False := by
  have := finite_gl (V := V)
  obtain ⟨-, hΓ, ⟨e⟩, -⟩ := h10
  refine false_of_two_pow_le (X := X.subgroupOf Γ) (sq_subgroupOf hsq)
    (g := ((e.symm a6Four : ↥(CFSG.Open.genFittingLayer ↥Γ)) : ↥Γ)) ?_ (k := k)
    (by rw [card_subgroupOf_of_le hXΓ, hk]) (by rw [card_subgroupOf_of_le hXΓ]; omega)
    (n := 4) (m := 135) (by rw [hΓ]; norm_num) (by decide)
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a6Four]

omit [Finite V] in
theorem card_X_of_concl12 (h12 : G112Concl12 Γ X) : Nat.card X = 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h8, -⟩ := h12
  exact h8

end Concl

end CFSG.Quasithin.H13.L14324

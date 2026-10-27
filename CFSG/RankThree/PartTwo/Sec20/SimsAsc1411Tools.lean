module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

section Words

variable {G : Type*} [Group G]

@[expose] def word1411 (α : MulAut G) (x₁ x₂ x₃ : G) : G :=
  α x₁ * x₁⁻¹ * (x₂ * α (x₂⁻¹ * x₃) * x₃⁻¹)

theorem word1411_conj (β α : MulAut G) (x₁ x₂ x₃ : G) :
    word1411 (β * α * β⁻¹) (β x₁) (β x₂) (β x₃) = β (word1411 α x₁ x₂ x₃) := by
  simp [word1411, MulAut.mul_apply, map_mul, map_inv]

theorem word1411_congr {H : Type*} [Group H] (e : G ≃* H) (α : MulAut G) (x₁ x₂ x₃ : G) :
    word1411 (MulAut.congr e α) (e x₁) (e x₂) (e x₃) = e (word1411 α x₁ x₂ x₃) := by
  simp [word1411, MulAut.congr_apply, map_mul, map_inv]

theorem word1411_conj_eq {s : G} (hs : s * s = 1) (x₁ x₂ x₃ : G) :
    word1411 (MulAut.conj s) x₁ x₂ x₃ =
      s * (x₁ * s * x₁⁻¹) * (x₂ * s * x₂⁻¹) * (x₃ * s * x₃⁻¹) := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  simp only [word1411, MulAut.conj_apply, hinv]
  group

end Words

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem relIndex_centralizer_conj_tools {I : Subgroup X} (hI : I.Normal) (g x : X) :
    (centralizer ({g * x * g⁻¹} : Set X)).relIndex I =
      (centralizer ({x} : Set X)).relIndex I := by
  have hcomap : (centralizer ({g * x * g⁻¹} : Set X)).comap
      (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    ext y
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := hy.symm
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · intro hy
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hy]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [← hcomap, Subgroup.relIndex_comap]
  congr 1
  exact (Subgroup.normal_iff_map_conj_eq.mp hI g).symm

theorem not_sq_dvd_card_mulAut_of_two_group {U : Type*} [Group U] [Finite U] {k : ℕ}
    (hU : Nat.card U = 2 ^ k) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : ∀ e, 1 ≤ e → e ≤ k → ¬ p ^ 2 ∣ 2 ^ e - 1)
    (h2 : ∀ e₁ e₂, 1 ≤ e₁ → e₁ ≤ k → 1 ≤ e₂ → e₂ ≤ k → p ∣ 2 ^ e₁ - 1 → p ∣ 2 ^ e₂ - 1 →
      e₁ = e₂) :
    ¬ p ^ 2 ∣ Nat.card (MulAut U) := by
  classical
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut U) := Finite.of_injective (fun σ : MulAut U => (σ : U → U))
    fun a b hab => MulEquiv.ext (congrFun hab)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  by_cases hcyc : ∃ σ ∈ Q, p ^ 2 ∣ orderOf σ
  · obtain ⟨σ, -, hσ⟩ := hcyc
    obtain ⟨e, he1, hek, he⟩ :=
      prime_pow_dvd_two_pow_sub_one_of_dvd_orderOf hU σ hp hp2 (by norm_num) hσ
    exact h1 e he1 hek he
  push Not at hcyc
  have hordp : ∀ σ ∈ Q, σ ≠ 1 → orderOf σ = p := by
    intro σ hσQ hσ1
    have hd : orderOf σ ∣ p ^ 2 := hQ ▸ Subgroup.orderOf_dvd_natCard Q hσQ
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hd
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hj'
      exact absurd hj' hσ1
    · rwa [pow_one] at hj'
    · exact absurd (dvd_of_eq hj'.symm) (hcyc σ hσQ)
  have hQ1 : ∃ σ ∈ Q, σ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall Q).mpr hcon, Subgroup.card_bot] at hQ
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨σ₀, hσ₀Q, hσ₀1⟩ := hQ1
  obtain ⟨c₀, hc₀k, -, hc₀dvd⟩ :=
    exists_card_fixed_of_orderOf_eq_prime hU σ₀ hp hp2 (hordp σ₀ hσ₀Q hσ₀1)
  have hfix : ∀ σ ∈ Q, σ ≠ 1 → Nat.card {u : U // σ u = u} = 2 ^ c₀ := by
    intro σ hσQ hσ1
    obtain ⟨c, hck, hccard, hcdvd⟩ :=
      exists_card_fixed_of_orderOf_eq_prime hU σ hp hp2 (hordp σ hσQ hσ1)
    have he := h2 (k - c) (k - c₀) (by omega) (by omega) (by omega) (by omega) hcdvd hc₀dvd
    rw [hccard, show c = c₀ by omega]
  have : Fintype U := Fintype.ofFinite U
  have : Fintype Q := Fintype.ofFinite Q
  have : Fintype (Quotient (MulAction.orbitRel Q U)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Q U
  have hcardQ : Fintype.card Q = p ^ 2 := by rw [Fintype.card_eq_nat_card, hQ]
  have hfix1 : Fintype.card (MulAction.fixedBy U (1 : Q)) = 2 ^ k := by
    rw [Fintype.card_eq_nat_card, ← hU]
    exact Nat.card_congr ((Equiv.subtypeEquivRight fun u => by
      simp [MulAction.mem_fixedBy]).trans (Equiv.Set.univ U))
  have hfixσ : ∀ σ : Q, σ ≠ 1 → Fintype.card (MulAction.fixedBy U σ) = 2 ^ c₀ := by
    intro σ hσ
    rw [Fintype.card_eq_nat_card, ← hfix σ σ.2 fun h1 => hσ (Subtype.ext h1)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [MulAction.mem_fixedBy, Subgroup.smul_def, MulAut.smul_def])
  rw [Fintype.sum_eq_add_sum_compl (1 : Q), hfix1,
    Finset.sum_congr rfl fun σ hσ => hfixσ σ (by simpa using hσ), Finset.sum_const,
    Finset.card_compl, Finset.card_singleton, smul_eq_mul, hcardQ] at hB
  obtain ⟨A', hA'⟩ : ∃ A', 2 ^ (k - c₀) = A' + 1 := ⟨2 ^ (k - c₀) - 1, by
    have := Nat.one_le_two_pow (n := k - c₀)
    omega⟩
  obtain ⟨P', hP'⟩ : ∃ P', p ^ 2 = P' + 1 := ⟨p ^ 2 - 1, by
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega⟩
  have hk : 2 ^ k = 2 ^ c₀ * 2 ^ (k - c₀) := by
    rw [← pow_add, Nat.add_sub_cancel' hc₀k.le]
  rw [hk, hA', hP', Nat.add_sub_cancel] at hB
  have hsum : 2 ^ c₀ * A' + 2 ^ c₀ * (P' + 1) =
      Fintype.card (Quotient (MulAction.orbitRel Q U)) * (P' + 1) := by
    rw [← hB]
    ring
  have hdvdA : P' + 1 ∣ 2 ^ c₀ * A' :=
    (Nat.dvd_add_left (dvd_mul_left _ _)).mp (hsum ▸ dvd_mul_left _ _)
  have hcop : Nat.Coprime (P' + 1) (2 ^ c₀) := by
    rw [← hP']
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdvdA' : p ^ 2 ∣ 2 ^ (k - c₀) - 1 := by
    rw [hP', hA', Nat.add_sub_cancel]
    exact hcop.dvd_of_dvd_mul_left hdvdA
  exact h1 (k - c₀) (by omega) (by omega) hdvdA'

theorem pow_four_eq_one_of_pow_eight_eq_one {U : Type*} [Group U] [Finite U]
    (hcomm : ∀ a b : U, a * b = b * a) (h2 : ∀ u : U, u * u = 1) (hcard : Nat.card U ≤ 16)
    {τ : MulAut U} (hτ : τ ^ 8 = 1) : τ ^ 4 = 1 := by
  classical
  have hinv : ∀ u : U, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (h2 u)
  let ε : U →* U :=
    { toFun := fun u => τ u * u⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        calc τ a * τ b * (b⁻¹ * a⁻¹) = τ a * ((τ b * b⁻¹) * a⁻¹) := by simp only [mul_assoc]
          _ = τ a * (a⁻¹ * (τ b * b⁻¹)) := by rw [hcomm (τ b * b⁻¹) a⁻¹]
          _ = τ a * a⁻¹ * (τ b * b⁻¹) := by simp only [mul_assoc] }
  have hε : ∀ u, ε u = τ u * u⁻¹ := fun u => rfl
  have hpow : ∀ j : ℕ, ∀ u : U, ε^[2 ^ j] u = (τ ^ 2 ^ j) u * u⁻¹ := by
    intro j
    induction j with
    | zero => intro u; simp [hε]
    | succ j ih =>
      intro u
      have e1 : ε^[2 ^ (j + 1)] u = ε^[2 ^ j] (ε^[2 ^ j] u) := by
        rw [pow_succ, mul_two, Function.iterate_add_apply]
      have e2 : (τ ^ 2 ^ (j + 1)) u = (τ ^ 2 ^ j) ((τ ^ 2 ^ j) u) := by
        rw [pow_succ, mul_two, pow_add, MulAut.mul_apply]
      rw [e1, e2, ih, ih, map_mul, map_inv, mul_inv_rev, inv_inv, hinv ((τ ^ 2 ^ j) u)]
      set A := (τ ^ 2 ^ j) ((τ ^ 2 ^ j) u)
      set B := (τ ^ 2 ^ j) u
      calc A * B * (u * B) = A * (B * u * B) := by simp only [mul_assoc]
        _ = A * (u * B * B) := by rw [hcomm B u]
        _ = A * u⁻¹ := by rw [mul_assoc u, h2 B, mul_one, hinv u]
  have h8 : ∀ u : U, ε^[8] u = 1 := fun u => by
    have := hpow 3 u
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, hτ, MulAut.one_apply, mul_inv_cancel] at this
    exact this
  by_contra hne
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, ε^[4] u₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    ext u
    have := hpow 2 u
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hall u] at this
    exact mul_inv_eq_one.mp this.symm
  have hmul : ∀ n (x y : U), ε^[n] (x * y) = ε^[n] x * ε^[n] y := fun n => by
    induction n with
    | zero => intro x y; rfl
    | succ n ih => intro x y; rw [Function.iterate_succ_apply, map_mul, ih,
        ← Function.iterate_succ_apply ε, ← Function.iterate_succ_apply ε]
  have hone : ∀ n, ε^[n] (1 : U) = 1 := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply, map_one, ih]
  let K : ℕ → Subgroup U := fun i =>
    { carrier := {u | ε^[i] u = 1}
      mul_mem' := fun {a b} (ha : ε^[i] a = 1) (hb : ε^[i] b = 1) => by
        change ε^[i] (a * b) = 1
        rw [hmul, ha, hb, mul_one]
      one_mem' := hone i
      inv_mem' := fun {a} (ha : ε^[i] a = 1) => by
        change ε^[i] a⁻¹ = 1
        rw [hinv]
        exact ha }
  have hmemK : ∀ i u, u ∈ K i ↔ ε^[i] u = 1 := fun _ _ => Iff.rfl
  have hmono : ∀ i, K i ≤ K (i + 1) := fun i u hu => by
    rw [hmemK] at hu ⊢
    rw [Function.iterate_succ_apply', hu, map_one]
  have hstab : ∀ i, K i = K (i + 1) → ∀ j, K (i + j) = K i := by
    intro i hi j
    induction j with
    | zero => rfl
    | succ j ih =>
      apply le_antisymm _ (ih ▸ hmono (i + j))
      intro u hu
      rw [hmemK, ← add_assoc, Function.iterate_succ_apply] at hu
      have h1 : ε u ∈ K (i + j) := hu
      rw [ih] at h1
      have h3 : u ∈ K (i + 1) := by
        rw [hmemK, Function.iterate_succ_apply]
        exact h1
      rw [← hi] at h3
      exact h3
  have hstrict : ∀ i, i ≤ 4 → K i < K (i + 1) := by
    intro i hi
    refine lt_of_le_of_ne (hmono i) fun heq => hu₀ ?_
    have h4 := hstab i heq (4 - i)
    have h8' := hstab i heq (8 - i)
    rw [Nat.add_sub_cancel' hi] at h4
    rw [Nat.add_sub_cancel' (by omega)] at h8'
    have : u₀ ∈ K 8 := (hmemK 8 u₀).mpr (h8 u₀)
    rw [h8', ← h4] at this
    exact this
  have hdouble : ∀ i, i ≤ 4 → 2 * Nat.card (K i) ≤ Nat.card (K (i + 1)) := by
    intro i hi
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (hmono i)
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact Nat.card_pos.ne' hm
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      exact (hstrict i hi).ne (Subgroup.eq_of_le_of_card_ge (hmono i) hm.le)
    rw [hm]
    have : 2 ≤ m := by omega
    nlinarith [Nat.card_pos (α := K i)]
  have hK0 : 1 ≤ Nat.card (K 0) := Nat.card_pos
  have d0 : 2 * Nat.card (K 0) ≤ Nat.card (K 1) := hdouble 0 (by norm_num)
  have d1 : 2 * Nat.card (K 1) ≤ Nat.card (K 2) := hdouble 1 (by norm_num)
  have d2 : 2 * Nat.card (K 2) ≤ Nat.card (K 3) := hdouble 2 (by norm_num)
  have d3 : 2 * Nat.card (K 3) ≤ Nat.card (K 4) := hdouble 3 (by norm_num)
  have d4 : 2 * Nat.card (K 4) ≤ Nat.card (K 5) := hdouble 4 (by norm_num)
  have := Subgroup.card_le_card_group (K 5)
  omega

section Criteria

variable {G : Type*} [Group G]

@[expose] def Excl1411 (α : MulAut G) : Prop :=
  (∃ (x : G) (q k : ℕ), q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧ (∀ e : ℕ, 1 ≤ e → e ≤ 4 → ¬ q ^ k ∣ 2 ^ e - 1) ∧
    q ^ k ∣ orderOf (α x * x⁻¹)) ∨
  (∃ (x₁ x₂ x₃ : G) (q k : ℕ), q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧
    (∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1) ∧ q ^ k ∣ orderOf (word1411 α x₁ x₂ x₃)) ∨
  (∃ (x₁ x₂ : G) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ (∀ e : ℕ, 1 ≤ e → e ≤ 6 → ¬ p ^ 2 ∣ 2 ^ e - 1) ∧
    (∀ e₁ e₂ : ℕ, 1 ≤ e₁ → e₁ ≤ 6 → 1 ≤ e₂ → e₂ ≤ 6 → p ∣ 2 ^ e₁ - 1 → p ∣ 2 ^ e₂ - 1 →
      e₁ = e₂) ∧
    p ^ 2 ∣ Nat.card (Subgroup.closure ({α x₁ * x₁⁻¹, α x₂ * x₂⁻¹} : Set G))) ∨
  (∃ x : G, 16 ∣ orderOf (α x * x⁻¹))

theorem Excl1411.of_congr {H : Type*} [Group H] (e : G ≃* H) {α : MulAut G}
    (hα : Excl1411 (MulAut.congr e α)) : Excl1411 α := by
  have he : ∀ y : H, MulAut.congr e α y * y⁻¹ = e (α (e.symm y) * (e.symm y)⁻¹) := fun y => by
    simp [MulAut.congr_apply]
  rcases hα with ⟨y, q, k, hq, hq2, hk, h4, hy⟩ | ⟨y₁, y₂, y₃, q, k, hq, hq2, hk, h8, hy⟩ |
    ⟨y₁, y₂, p, hp, hp2, h1, h2, hy⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨e.symm y, q, k, hq, hq2, hk, h4, ?_⟩
    rwa [he, MulEquiv.orderOf_eq] at hy
  · refine Or.inr (Or.inl ⟨e.symm y₁, e.symm y₂, e.symm y₃, q, k, hq, hq2, hk, h8, ?_⟩)
    have e1 := word1411_congr e α (e.symm y₁) (e.symm y₂) (e.symm y₃)
    simp only [MulEquiv.apply_symm_apply] at e1
    rwa [e1, MulEquiv.orderOf_eq] at hy
  · refine Or.inr (Or.inr (Or.inl ⟨e.symm y₁, e.symm y₂, p, hp, hp2, h1, h2, ?_⟩))
    have hmap : (Subgroup.closure ({α (e.symm y₁) * (e.symm y₁)⁻¹,
        α (e.symm y₂) * (e.symm y₂)⁻¹} : Set G)).map e.toMonoidHom =
        Subgroup.closure ({MulAut.congr e α y₁ * y₁⁻¹, MulAut.congr e α y₂ * y₂⁻¹} : Set H) := by
      rw [MonoidHom.map_closure, Set.image_pair, he, he]
      rfl
    rwa [← hmap, Subgroup.card_map_of_injective e.injective] at hy
  · refine Or.inr (Or.inr (Or.inr ⟨e.symm y, ?_⟩))
    rwa [he, MulEquiv.orderOf_eq] at hy

theorem excl1411_of_odd_not_dvd_105 {α : MulAut G} {x : G} {n : ℕ} (hn : Odd n)
    (hn105 : ¬ n ∣ 105) (hx : n ∣ orderOf (α x * x⁻¹)) : Excl1411 α := by
  obtain ⟨q, k, hq, hqn, hq105⟩ : ∃ q k : ℕ, q.Prime ∧ q ^ k ∣ n ∧ ¬ q ^ k ∣ 105 := by
    by_contra hall
    push Not at hall
    exact hn105 ((Nat.dvd_iff_prime_pow_dvd_dvd 105 n).mpr fun q k hq hqk => hall q k hq hqk)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hk : k ≠ 0 := by
      rintro rfl
      exact hq105 (by norm_num)
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr
      ((dvd_pow_self 2 hk).trans hqn))
  have hk : 1 ≤ k := by
    by_contra h0
    rw [show k = 0 by omega, pow_zero] at hq105
    exact hq105 (one_dvd _)
  refine Or.inl ⟨x, q, k, hq, hq2, hk, fun e he1 he4 hd => hq105 ?_, hqn.trans hx⟩
  interval_cases e
  · exact hd.trans (by norm_num)
  · exact hd.trans (by norm_num)
  · exact hd.trans (by norm_num)
  · exact hd.trans (by norm_num)

theorem Excl1411.conj (β : MulAut G) {α : MulAut G} (hα : Excl1411 α) :
    Excl1411 (β * α * β⁻¹) := by
  refine Excl1411.of_congr (β⁻¹ : MulAut G) ?_
  have e : MulAut.congr (β⁻¹ : MulAut G) (β * α * β⁻¹) = α := by
    ext x
    simp [MulAut.congr_apply, MulAut.mul_apply]
  rw [e]
  exact hα

theorem Excl1411.of_conj (β : MulAut G) {α : MulAut G} (hα : Excl1411 (β * α * β⁻¹)) :
    Excl1411 α := by
  have h := hα.conj β⁻¹
  rwa [show β⁻¹ * (β * α * β⁻¹) * β⁻¹⁻¹ = α by group] at h

end Criteria

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem false_of_excl_two (h : Hyp1411 X L S) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 4)
    [(L.map π).Normal]
    {x : ↥(L.map π)} {q k : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hk : 1 ≤ k) (h4 : ∀ e : ℕ, 1 ≤ e → e ≤ 4 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hx : q ^ k ∣ orderOf (MulAut.conjNormal (π t) x *
      x⁻¹)) : False := by
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ, -, hℓ⟩ := x.2
  set u : Fin 2 → X := ![t, ℓ * t⁻¹ * ℓ⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hu4 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 4 := by
    intro i
    fin_cases i
    · exact hle
    · change (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4
      rw [htinv, relIndex_centralizer_conj_tools hIn]
      exact hle
  set y : X := t * (ℓ * t⁻¹ * ℓ⁻¹) with hy
  have hymem : y ∈ closure (Set.range u) :=
    mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
  obtain ⟨N, -, hpow, hN⟩ := exists_pow_mem_centralizer_closure_le_four hI u hun hu4 hymem
  have himg : π y = ((ψ x * x⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ, hy,
      map_mul, map_inv]
    group
  have h1 : (ψ x * x⁻¹) ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ x * x⁻¹) ^ (2 * N) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : q ^ k ∣ N * 2 := by
    rw [mul_comm]
    exact hx.trans (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (q ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  obtain ⟨e, he1, he4, hediv⟩ := hN q k hq hq2 hk (hcop.dvd_of_dvd_mul_right hdvd)
  exact h4 e he1 he4 hediv

private theorem false_of_excl_four (h : Hyp1411 X L S) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 4)
    [(L.map π).Normal]
    {x₁ x₂ x₃ : ↥(L.map π)} {q k : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hk : 1 ≤ k) (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hx : q ^ k ∣ orderOf (word1411
      (MulAut.conjNormal (π t)) x₁ x₂ x₃)) : False := by
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ₁, -, hℓ₁⟩ := x₁.2
  obtain ⟨ℓ₂, -, hℓ₂⟩ := x₂.2
  obtain ⟨ℓ₃, -, hℓ₃⟩ := x₃.2
  set u : Fin 4 → X := ![t, ℓ₁ * t⁻¹ * ℓ₁⁻¹, ℓ₂ * t * ℓ₂⁻¹, ℓ₃ * t⁻¹ * ℓ₃⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc : ∀ ℓ : X, (centralizer ({ℓ * t * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := fun ℓ => by
    rw [relIndex_centralizer_conj_tools hIn]
    exact hle
  have hc' : ∀ ℓ : X, (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := fun ℓ => by
    rw [htinv]
    exact hc ℓ
  have hu4 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 4 := by
    intro i
    fin_cases i
    · exact hle
    · exact hc' ℓ₁
    · exact hc ℓ₂
    · exact hc' ℓ₃
  set y : X := t * (ℓ₁ * t⁻¹ * ℓ₁⁻¹) * ((ℓ₂ * t * ℓ₂⁻¹) * (ℓ₃ * t⁻¹ * ℓ₃⁻¹)) with hy
  have hymem : y ∈ closure (Set.range u) :=
    mul_mem (mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩))
      (mul_mem (subset_closure ⟨2, rfl⟩) (subset_closure ⟨3, rfl⟩))
  obtain ⟨N, -, hpow, hN⟩ := exists_pow_mem_centralizer_closure_le_four hI u hun hu4 hymem
  have himg : π y = ((word1411 ψ x₁ x₂ x₃ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [word1411, Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ₁,
      ← hℓ₂, ← hℓ₃, hy, map_mul, map_inv]
    group
  have h1 : (word1411 ψ x₁ x₂ x₃) ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : (((word1411 ψ x₁ x₂ x₃) ^ (2 * N) : ↥(L.map π)) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : q ^ k ∣ N * 2 := by
    rw [mul_comm]
    exact hx.trans (orderOf_dvd_of_pow_eq_one h1)
  have hcop : Nat.Coprime (q ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  obtain ⟨e, he1, he8, hediv⟩ := hN q k hq hq2 hk (hcop.dvd_of_dvd_mul_right hdvd)
  exact h8 e he1 he8 hediv

private theorem false_of_excl_sq (h : Hyp1411 X L S) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 4)
    [(L.map π).Normal]
    {x₁ x₂ : ↥(L.map π)} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h1 : ∀ e : ℕ, 1 ≤ e → e ≤ 6 → ¬ p ^ 2 ∣ 2 ^ e - 1)
    (h2 : ∀ e₁ e₂ : ℕ, 1 ≤ e₁ → e₁ ≤ 6 → 1 ≤ e₂ → e₂ ≤ 6 → p ∣ 2 ^ e₁ - 1 → p ∣ 2 ^ e₂ - 1 →
      e₁ = e₂)
    (hx : p ^ 2 ∣ Nat.card (Subgroup.closure
      ({MulAut.conjNormal (π t) x₁ * x₁⁻¹,
        MulAut.conjNormal (π t) x₂ * x₂⁻¹} :
          Set ↥(L.map π)))) : False := by
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ₁, -, hℓ₁⟩ := x₁.2
  obtain ⟨ℓ₂, -, hℓ₂⟩ := x₂.2
  set u : Fin 3 → X := ![t, ℓ₁ * t⁻¹ * ℓ₁⁻¹, ℓ₂ * t⁻¹ * ℓ₂⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hc' : ∀ ℓ : X, (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := fun ℓ => by
    rw [htinv, relIndex_centralizer_conj_tools hIn]
    exact hle
  have hu4 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 4 := by
    intro i
    fin_cases i
    · exact hle
    · exact hc' ℓ₁
    · exact hc' ℓ₂
  obtain ⟨U, hUI, hUcard, hUy⟩ := exists_subgroup_normalized_closure hI u hun (fun _ => 4) hu4
  have hU64 : Nat.card U ≤ 2 ^ 6 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hUcard
    exact hUcard.trans (by norm_num)
  have hU2 : IsPGroup 2 U := fun g =>
    ⟨1, Subtype.ext (by simpa [pow_two] using hI.2 _ (hUI g.2))⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU2
  have hk6 : k ≤ 6 := by
    rw [hk] at hU64
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hU64
  set w₁ : X := t * (ℓ₁ * t⁻¹ * ℓ₁⁻¹) with hw₁
  set w₂ : X := t * (ℓ₂ * t⁻¹ * ℓ₂⁻¹) with hw₂
  set D₀ : Subgroup X := closure ({w₁, w₂} : Set X) with hD₀
  have hD₀u : D₀ ≤ closure (Set.range u) := by
    rw [hD₀, closure_le]
    rintro _ (rfl | rfl)
    · exact mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
    · exact mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨2, rfl⟩)
  have hD₀N : D₀ ≤ normalizer (U : Set X) := fun y hy => (hUy y (hD₀u hy)).2.1
  have himg₁ : π w₁ = ((ψ x₁ * x₁⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ₁, hw₁,
      map_mul, map_inv]
    group
  have himg₂ : π w₂ = ((ψ x₂ * x₂⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ₂, hw₂,
      map_mul, map_inv]
    group
  have hmapD : D₀.map π = (closure ({ψ x₁ * x₁⁻¹, ψ x₂ * x₂⁻¹} : Set ↥(L.map π))).map
      (L.map π).subtype := by
    rw [hD₀, MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair,
      himg₁, himg₂]
    rfl
  have hD₀L : D₀.map π ≤ L.map π := by
    rw [hmapD]
    exact Subgroup.map_subtype_le _
  set π₀ : D₀ →* X ⧸ CFSG.pPrimeCore 3 X := π.comp D₀.subtype with hπ₀
  set ρ₀ : D₀ →* MulAut U := U.normalizerMonoidHom.comp (Subgroup.inclusion hD₀N) with hρ₀
  have hrange : π₀.range = D₀.map π := by
    rw [hπ₀, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card π₀.range =
      Nat.card (closure ({ψ x₁ * x₁⁻¹, ψ x₂ * x₂⁻¹} : Set ↥(L.map π))) := by
    rw [hrange, hmapD, Subgroup.card_map_of_injective (L.map π).subtype_injective]
  have hJ : IsPGroup 2 (ρ₀.ker.map π₀) := by
    rintro ⟨_, y, hy, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    have hyU : ∀ w ∈ U, (y : X) * w * (y : X)⁻¹ = w := by
      intro w hw
      have e := congrArg (fun σ : MulAut U => ((σ ⟨w, hw⟩ : U) : X)) (MonoidHom.mem_ker.mp hy)
      simp only [hρ₀, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at e
      exact e
    obtain ⟨hyI, -, hyC⟩ := hUy y (hD₀u y.2)
    have hsq := sq_mem_centralizer_of_centralizes hI hUI hyI hyC hyU
    have hmem : π₀ y ^ 2 ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hsq, ?_⟩, ?_⟩
      · rw [hπ₀, MonoidHom.coe_comp, Function.comp_apply, map_pow]
        rfl
      · exact pow_mem (hD₀L ⟨y, y.2, rfl⟩) 2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hJ
  have hidx : Nat.card π₀.range ∣ Nat.card (ρ₀.ker.map π₀) * Nat.card ρ₀.range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker, ← relIndex_ker,
      ← Subgroup.inf_relIndex_left, Subgroup.relIndex_mul_index inf_le_left]
    exact Subgroup.index_dvd_of_le inf_le_right
  have hcop : Nat.Coprime (p ^ 2) (2 ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdvdρ : p ^ 2 ∣ Nat.card ρ₀.range := by
    rw [hj] at hidx
    exact hcop.dvd_of_dvd_mul_left ((hcard ▸ hx).trans hidx)
  exact not_sq_dvd_card_mulAut_of_two_group hk hp hp2
    (fun e he1 hek => h1 e he1 (hek.trans hk6))
    (fun e₁ e₂ h₁ h₁' h₂ h₂' => h2 e₁ e₂ h₁ (h₁'.trans hk6) h₂ (h₂'.trans hk6))
    (hdvdρ.trans (Subgroup.card_subgroup_dvd_card _))

private theorem false_of_excl_two_pow (h : Hyp1411 X L S) {π : X →* X ⧸ CFSG.pPrimeCore 3 X}
    (hπ : π = QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) (hsimp : IsSimpleGroup ↥(L.map π))
    {I : Subgroup X} (hIn : I.Normal) (hI : Sec3.IsElemTwo I)
    (hLI : ∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) {t : X} (htt : t * t = 1)
    (hle : (centralizer ({t} : Set X)).relIndex I ≤ 4)
    [(L.map π).Normal] {x : ↥(L.map π)}
    (hx : 16 ∣ orderOf (MulAut.conjNormal (π t) x * x⁻¹)) : False := by
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hbot : (centralizer (I : Set X)).map π ⊓ L.map π = ⊥ := by
    subst hπ
    exact map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ, -, hℓ⟩ := x.2
  set u : Fin 2 → X := ![t, ℓ * t⁻¹ * ℓ⁻¹] with hu
  have hun : ∀ i, u i ∈ normalizer (I : Set X) := fun i => by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hu4 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 4 := by
    intro i
    fin_cases i
    · exact hle
    · change (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4
      rw [htinv, relIndex_centralizer_conj_tools hIn]
      exact hle
  obtain ⟨U, hUI, hUcard, hUy⟩ := exists_subgroup_normalized_closure hI u hun (fun _ => 4) hu4
  have hU16 : Nat.card U ≤ 16 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hUcard
    exact hUcard.trans (by norm_num)
  set y : X := t * (ℓ * t⁻¹ * ℓ⁻¹) with hy
  have hymem : y ∈ closure (Set.range u) :=
    mul_mem (subset_closure ⟨0, rfl⟩) (subset_closure ⟨1, rfl⟩)
  have himg : π y = ((ψ x * x⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ, hy,
      map_mul, map_inv]
    group
  have hyN : y ∈ normalizer (U : Set X) := (hUy y hymem).2.1
  set σ : MulAut U := U.normalizerMonoidHom ⟨y, hyN⟩ with hσ
  have hcU : ∀ a b : U, a * b = b * a := fun a b => Subtype.ext (hI.1 _ (hUI a.2) _ (hUI b.2))
  have h2U : ∀ w : U, w * w = 1 := fun w => Subtype.ext (hI.2 _ (hUI w.2))
  have : Finite (MulAut U) := Finite.of_injective (fun τ : MulAut U => (τ : U → U))
    fun a b hab => MulEquiv.ext (congrFun hab)
  obtain ⟨a, m, hm, hN⟩ : ∃ a m : ℕ, Odd m ∧ orderOf σ = 2 ^ a * m := by
    obtain ⟨a, m, hm2, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos σ).ne' 2
      (by norm_num)
    exact ⟨a, m, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm2), hNm⟩
  have hσm4 : (σ ^ m) ^ 4 = 1 := by
    have hpow : ∀ b : ℕ, (σ ^ m) ^ 2 ^ (b + 2) = 1 → (σ ^ m) ^ 4 = 1 := by
      intro b
      induction b with
      | zero => intro h1; simpa using h1
      | succ b ih =>
        intro h1
        apply ih
        have h8 : ((σ ^ m) ^ 2 ^ b) ^ 8 = 1 := by
          rw [← pow_mul, show 2 ^ b * 8 = 2 ^ (b + 1 + 2) by ring]
          exact h1
        have h4 := pow_four_eq_one_of_pow_eight_eq_one hcU h2U hU16 h8
        rw [← pow_mul, show 2 ^ b * 4 = 2 ^ (b + 2) by ring] at h4
        exact h4
    apply hpow a
    rw [← pow_mul, show m * 2 ^ (a + 2) = 2 ^ a * m * 4 by ring, pow_mul, ← hN,
      pow_orderOf_eq_one, one_pow]
  have hcent : ∀ w ∈ U, y ^ (m * 4) * w * (y ^ (m * 4))⁻¹ = w := by
    intro w hw
    have e := congrArg (fun τ : MulAut U => ((τ ⟨w, hw⟩ : U) : X)) hσm4
    rw [← pow_mul, hσ, ← map_pow] at e
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using e
  obtain ⟨hyI, -, hyC⟩ := hUy (y ^ (m * 4)) (pow_mem hymem _)
  have hsq := sq_mem_centralizer_of_centralizes hI hUI hyI hyC hcent
  have h1 : (ψ x * x⁻¹) ^ (m * 4 * 2) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ x * x⁻¹) ^ (m * 4 * 2) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, by rw [← pow_mul] at hsq; exact hsq, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd := hx.trans (orderOf_dvd_of_pow_eq_one h1)
  obtain ⟨m', rfl⟩ := hm
  omega

theorem noSmall1411_of_forall_excl (h : Hyp1411 X L S)
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    (hE : ∀ α : MulAut ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))), orderOf α = 2 →
      Excl1411 α) :
    NoSmall1411 X L S := by
  intro I hIn hI hLI t htS htQ htt
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hψ2 : ψ * ψ = 1 := by
    rw [hψ, ← map_mul, ← map_mul, htt, map_one, map_one]
  have hψ1 : ψ ≠ 1 := by
    obtain ⟨l, hl, hne⟩ := exists_not_commute_of_hyp1411 h hZ htS htQ
    intro h1
    apply hne
    have e1 := congrArg (fun f : MulAut ↥(L.map π) =>
      ((f ⟨π l, mem_map_of_mem _ hl⟩ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X)) h1
    simp only [hψ, MulAut.conjNormal_apply, MulAut.one_apply] at e1
    calc π t * π l = π t * π l * (π t)⁻¹ * π t := by group
      _ = π l * π t := by rw [e1]
  have hord : orderOf ψ = 2 := orderOf_eq_prime (by rw [sq]; exact hψ2) hψ1
  rcases hE ψ hord with ⟨x, q, k, hq, hq2, hk, h4, hx⟩ |
    ⟨x₁, x₂, x₃, q, k, hq, hq2, hk, h8, hx⟩ | ⟨x₁, x₂, p, hp, hp2, h1, h2, hx⟩ | ⟨x, hx⟩
  · exact false_of_excl_two h hπ hsimp hIn hI hLI htt hle hq hq2 hk h4 hx
  · exact false_of_excl_four h hπ hsimp hIn hI hLI htt hle hq hq2 hk h8 hx
  · exact false_of_excl_sq h hπ hsimp hIn hI hLI htt hle hp hp2 h1 h2 hx
  · exact false_of_excl_two_pow h hπ hsimp hIn hI hLI htt hle hx

theorem noSmall1411_of_forall_word1411 (h : Hyp1411 X L S)
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk : 1 ≤ k)
    (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hW : ∀ α : MulAut ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))), orderOf α = 2 →
      ∃ x₁ x₂ x₃, q ^ k ∣ orderOf (word1411 α x₁ x₂ x₃)) :
    NoSmall1411 X L S :=
  noSmall1411_of_forall_excl h hsimp hZ fun α hα => by
    obtain ⟨x₁, x₂, x₃, hx⟩ := hW α hα
    exact Or.inr (Or.inl ⟨x₁, x₂, x₃, q, k, hq, hq2, hk, h8, hx⟩)

private theorem isElemTwo_map_tools {Y : Type*} [Group Y] (f : X →* Y) {A : Subgroup X}
    (hA : Sec3.IsElemTwo A) : Sec3.IsElemTwo (A.map f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA.2 a ha, map_one]

private theorem relIndex_pCore_dvd_card_map (h : Hyp1411 X L S) {A : Subgroup X} (hAS : A ≤ S) :
    (CFSG.pCore 2 X).relIndex A ∣
      Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
  have hKA : CFSG.pPrimeCore 3 X ⊓ A ≤ CFSG.pCore 2 X := fun x hx =>
    mem_pCore_of_mem_pPrimeCore_of_hyp1411 h (hAS hx.2) hx.1
  rw [← relIndex_ker, QuotientGroup.ker_mk', ← inf_relIndex_right (CFSG.pPrimeCore 3 X) A]
  exact relIndex_dvd_of_le_left A hKA

theorem relIndex_pCore_le_two_of_isCyclic (h : Hyp1411 X L S)
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2 := by
  intro A hAS hA
  set K := CFSG.pPrimeCore 3 X
  have : IsCyclic ↥(A.map (QuotientGroup.mk' K)) := Subgroup.isCyclic_of_le (map_mono hAS)
  have hexp : Monoid.exponent ↥(A.map (QuotientGroup.mk' K)) ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨y, hy⟩ => ?_
    obtain ⟨a, haA, rfl⟩ := hy
    refine Subtype.ext ?_
    change QuotientGroup.mk' K a ^ 2 = 1
    rw [← map_pow, pow_two, hA.2 a haA, map_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd two_pos ((relIndex_pCore_dvd_card_map h hAS).trans hexp)

theorem relIndex_pCore_le_two_of_pRank_le_one (h : Hyp1411 X L S)
    (hS : CFSG.pRank 2 ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 1) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2 := by
  intro A hAS hA
  have hcard : Nat.card (A.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 2 :=
    (Sec3.card_le_two_pow_pRank (map_mono hAS) (isElemTwo_map_tools _ hA)).trans
      ((Nat.pow_le_pow_right two_pos hS).trans_eq (pow_one 2))
  exact (Nat.le_of_dvd Nat.card_pos (relIndex_pCore_dvd_card_map h hAS)).trans hcard

theorem asc82Item1411_of_forall_word1411 (h : Hyp1411 X L S)
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    (hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk : 1 ≤ k)
    (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1)
    (hW : ∀ α : MulAut ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))), orderOf α = 2 →
      ∃ x₁ x₂ x₃, q ^ k ∣ orderOf (word1411 α x₁ x₂ x₃)) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_isCyclic h hS)
    (noSmall1411_of_forall_word1411 h hsimp hZ hq hq2 hk h8 hW)

end CFSG.RankThree.PartTwo.Sec20

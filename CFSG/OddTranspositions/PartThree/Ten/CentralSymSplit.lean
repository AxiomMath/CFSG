module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Permutation.SymmetricCoxeter
public import Mathlib.GroupTheory.Perm.Cycle.Type
import CFSG.CGT.PushingUpLit.BHSSym.Coxeter
import CFSG.GroupTheory.SmallSymmetric
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

namespace CentralSymSplit

open Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym

section Transport

variable {α β : Type*}

theorem orderOf_dvd_of_apply_eq (u : β → α) (hu : Function.Injective u) (ρ : Perm α)
    (φ : Perm β) (h : ∀ i, ρ (u i) = u (φ i)) : orderOf φ ∣ orderOf ρ := by
  have hpow : ∀ (j : ℕ) i, (ρ ^ j) (u i) = u ((φ ^ j) i) := by
    intro j
    induction j with
    | zero => intro i; rfl
    | succ j ih => intro i; rw [pow_succ, Perm.mul_apply, h, ih, pow_succ, Perm.mul_apply]
  refine orderOf_dvd_of_pow_eq_one (Perm.ext fun i => hu ?_)
  rw [← hpow, pow_orderOf_eq_one]
  rfl

theorem exists_isConj_orderOf_dvd {N : ℕ} (σ : Perm α) (u : Fin N → α)
    (hu : Function.Injective u) (ψσ ψg : Perm (Fin N)) (hσu : ∀ i, σ (u i) = u (ψσ i)) :
    ∃ τ : Perm α, IsConj σ τ ∧ orderOf (ψσ * (ψg * ψσ * ψg⁻¹)) ∣ orderOf (σ * τ) := by
  obtain ⟨g, hg⟩ := Perm.exists_extending_pair u (fun i => u (ψg i)) hu (hu.comp ψg.injective)
  have hginv : ∀ i, g⁻¹ (u i) = u (ψg⁻¹ i) := fun i => by
    rw [Perm.inv_eq_iff_eq, hg]
    simp
  refine ⟨g * σ * g⁻¹, isConj_iff.2 ⟨g, rfl⟩, orderOf_dvd_of_apply_eq u hu _ _ fun i => ?_⟩
  simp only [Perm.mul_apply, hginv, hσu, hg]

end Transport

section Standard

def std6 : Perm (Fin 6) := swap 2 3 * swap 4 5

def conj6 : Perm (Fin 6) := swap 0 2 * (swap 1 3 * swap 3 4)

def std7 : Perm (Fin 7) := swap 1 2 * swap 3 4 * swap 5 6

def conj7 : Perm (Fin 7) := swap 0 1 * swap 4 5

def std8 : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

def conj8 : Perm (Fin 8) := swap 1 2 * swap 3 4 * swap 5 6

theorem orderOf_std6 : orderOf (std6 * (conj6 * std6 * conj6⁻¹)) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide +kernel

theorem orderOf_std7 : orderOf (std7 * (conj7 * std7 * conj7⁻¹)) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide +kernel

theorem orderOf_std8 : orderOf (std8 * (conj8 * std8 * conj8⁻¹)) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide +kernel

theorem std6_apply : ∀ i, std6 i = ![0, 1, 3, 2, 5, 4] i := by decide +kernel

theorem std7_apply : ∀ i, std7 i = ![0, 2, 1, 4, 3, 6, 5] i := by decide +kernel

theorem std8_apply : ∀ i, std8 i = ![1, 0, 3, 2, 5, 4, 7, 6] i := by decide +kernel

end Standard

section Pairs

variable {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}

theorem exists_pair_cons (hσ : ∀ x, σ (σ x) = x) {l : List α} (hnd : l.Nodup)
    (hcl : ∀ x ∈ l, σ x ∈ l ∧ σ x ≠ x) (hlt : l.length < σ.support.card) :
    ∃ a, σ a ≠ a ∧ (σ a :: a :: l).Nodup ∧
      ∀ x ∈ σ a :: a :: l, σ x ∈ σ a :: a :: l ∧ σ x ≠ x := by
  obtain ⟨a, ha, hal⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := l.toFinset) (t := σ.support) (lt_of_le_of_lt (List.toFinset_card_le l) hlt)
  rw [List.mem_toFinset] at hal
  have ha' : σ a ≠ a := Perm.mem_support.1 ha
  have hσa : σ a ∉ l := fun h => hal (by simpa [hσ] using (hcl _ h).1)
  refine ⟨a, ha', List.nodup_cons.2 ⟨by simp [ha', hσa], List.nodup_cons.2 ⟨hal, hnd⟩⟩, ?_⟩
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · simp [hσ, ha'.symm]
  · simp [ha']
  · obtain ⟨h1, h2⟩ := hcl x hx
    exact ⟨by simp [h1], h2⟩

theorem exists_conj_four_dvd_of_two_fixed (hσ : ∀ x, σ (σ x) = x) (h4 : 4 ≤ σ.support.card)
    (h2 : 2 ≤ σ.supportᶜ.card) : ∃ τ : Perm α, IsConj σ τ ∧ 4 ∣ orderOf (σ * τ) := by
  obtain ⟨a1, -, n1, c1⟩ := exists_pair_cons hσ (l := []) (by simp) (by simp)
    (by simp only [List.length_nil]; omega)
  obtain ⟨a2, -, n2, c2⟩ := exists_pair_cons hσ n1 c1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 h2
  have hpf : σ p = p := Perm.notMem_support.1 (Finset.mem_compl.1 hp)
  have hqf : σ q = q := Perm.notMem_support.1 (Finset.mem_compl.1 hq)
  have hpl : p ∉ σ a2 :: a2 :: σ a1 :: a1 :: [] := fun h => (c2 p h).2 hpf
  have hql : q ∉ p :: σ a2 :: a2 :: σ a1 :: a1 :: [] := fun h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact hpq rfl
    · exact (c2 q h).2 hqf
  have nd := List.nodup_cons.2 ⟨hql, List.nodup_cons.2 ⟨hpl, n2⟩⟩
  let u : Fin 6 → α := ![q, p, σ a2, a2, σ a1, a1]
  have hu : Function.Injective u := List.nodup_ofFn.1 (by simpa [u, List.ofFn_succ] using nd)
  obtain ⟨τ, hτ, hdvd⟩ := exists_isConj_orderOf_dvd σ u hu std6 conj6 (fun i => by
    fin_cases i <;> simp [u, std6_apply, hσ, hpf, hqf])
  exact ⟨τ, hτ, orderOf_std6 ▸ hdvd⟩

theorem exists_conj_six_dvd_of_one_fixed (hσ : ∀ x, σ (σ x) = x) (h6 : 6 ≤ σ.support.card)
    (h1 : 1 ≤ σ.supportᶜ.card) : ∃ τ : Perm α, IsConj σ τ ∧ 6 ∣ orderOf (σ * τ) := by
  obtain ⟨a1, -, n1, c1⟩ := exists_pair_cons hσ (l := []) (by simp) (by simp)
    (by simp only [List.length_nil]; omega)
  obtain ⟨a2, -, n2, c2⟩ := exists_pair_cons hσ n1 c1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨a3, -, n3, c3⟩ := exists_pair_cons hσ n2 c2
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h1
  have hpf : σ p = p := Perm.notMem_support.1 (Finset.mem_compl.1 hp)
  have hpl : p ∉ σ a3 :: a3 :: σ a2 :: a2 :: σ a1 :: a1 :: [] := fun h => (c3 p h).2 hpf
  have nd := List.nodup_cons.2 ⟨hpl, n3⟩
  let u : Fin 7 → α := ![p, σ a3, a3, σ a2, a2, σ a1, a1]
  have hu : Function.Injective u := List.nodup_ofFn.1 (by simpa [u, List.ofFn_succ] using nd)
  obtain ⟨τ, hτ, hdvd⟩ := exists_isConj_orderOf_dvd σ u hu std7 conj7 (fun i => by
    fin_cases i <;> simp [u, std7_apply, hσ, hpf])
  exact ⟨τ, hτ, orderOf_std7 ▸ hdvd⟩

theorem exists_conj_four_dvd_of_four_pairs (hσ : ∀ x, σ (σ x) = x) (h8 : 8 ≤ σ.support.card) :
    ∃ τ : Perm α, IsConj σ τ ∧ 4 ∣ orderOf (σ * τ) := by
  obtain ⟨a1, -, n1, c1⟩ := exists_pair_cons hσ (l := []) (by simp) (by simp)
    (by simp only [List.length_nil]; omega)
  obtain ⟨a2, -, n2, c2⟩ := exists_pair_cons hσ n1 c1
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨a3, -, n3, c3⟩ := exists_pair_cons hσ n2 c2
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨a4, -, n4, c4⟩ := exists_pair_cons hσ n3 c3
    (by simp only [List.length_cons, List.length_nil]; omega)
  let u : Fin 8 → α := ![σ a4, a4, σ a3, a3, σ a2, a2, σ a1, a1]
  have hu : Function.Injective u := List.nodup_ofFn.1 (by simpa [u, List.ofFn_succ] using n4)
  obtain ⟨τ, hτ, hdvd⟩ := exists_isConj_orderOf_dvd σ u hu std8 conj8 (fun i => by
    fin_cases i <;> simp [u, std8_apply, hσ])
  exact ⟨τ, hτ, orderOf_std8 ▸ hdvd⟩

end Pairs

section Classes

theorem false_of_dvd_orderOf_mul {G : Type*} [Group G] {C : Set G} (hC : IsOddTransp C)
    {σ τ : G} (hσ : σ ∈ C) (hτ : τ ∈ C) {m : ℕ} (hm : m ∣ orderOf (σ * τ)) (h2 : 2 ∣ m)
    (h3 : 2 < m) : False := by
  have h2' : 2 ∣ orderOf (σ * τ) := h2.trans hm
  rcases hC.2 σ hσ τ hτ with h | ⟨j, hj⟩
  · exact absurd (Nat.le_of_dvd two_pos (hm.trans h)) (by omega)
  · omega

theorem exists_cycleType_replicate_two {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : orderOf σ = 2) : ∃ k, σ.cycleType = Multiset.replicate (k + 1) 2 := by
  have := cycleType_prime_order (σ := σ) (by rw [h]; exact Nat.prime_two)
  rwa [h] at this

theorem sign_eq_of_cycleType_replicate {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    {k : ℕ} (h : σ.cycleType = Multiset.replicate k 2) : sign σ = (-1) ^ k := by
  rw [sign_of_cycleType, h, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    pow_add, mul_comm k 2, pow_mul, neg_one_sq, one_pow, one_mul]

theorem odd_of_closure_eq_top {n : ℕ} (hn : 2 ≤ n) {σ₀ : Perm (Fin n)} {k : ℕ}
    (hk : σ₀.cycleType = Multiset.replicate k 2)
    (hgen : Subgroup.closure {g | IsConj σ₀ g} = ⊤) : Odd k := by
  by_contra hodd
  have hs : sign σ₀ = 1 := by
    rw [sign_eq_of_cycleType_replicate hk]
    exact (Nat.not_odd_iff_even.1 hodd).neg_one_pow
  have hle : Subgroup.closure {g | IsConj σ₀ g} ≤ (sign : Perm (Fin n) →* ℤˣ).ker := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hs]
    exact (isConj_iff_eq.1 (MonoidHom.map_isConj sign hg)).symm
  rw [hgen] at hle
  have hmem := hle (Subgroup.mem_top (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))
  rw [MonoidHom.mem_ker, sign_swap (by simp [Fin.ext_iff])] at hmem
  exact absurd hmem (by decide)

end Classes

section Lifting

variable {X Y : Type*} [Group X] [Group Y]

theorem map_ne_one_of_isConj [Nontrivial Y] (π : X →* Y) (hπ : Function.Surjective π) {d₀ : X}
    (hgen : Subgroup.closure {g | IsConj d₀ g} = ⊤) {c : X} (hc : IsConj d₀ c) : π c ≠ 1 := by
  intro h1
  have hd₀ : π d₀ = 1 := by
    have := π.map_isConj hc
    rw [h1] at this
    exact isConj_one_left.1 this
  have hle : Subgroup.closure {g | IsConj d₀ g} ≤ π.ker := by
    rw [Subgroup.closure_le]
    intro g hg
    have := π.map_isConj hg
    rw [hd₀] at this
    exact isConj_one_right.1 this
  rw [hgen] at hle
  obtain ⟨y, hy⟩ := exists_ne (1 : Y)
  obtain ⟨x, rfl⟩ := hπ y
  exact hy (MonoidHom.mem_ker.1 (hle (Subgroup.mem_top x)))

theorem isOddTransp_image (π : X →* Y) {C : Set X} (hC : IsOddTransp C)
    (h1 : ∀ c ∈ C, π c ≠ 1) : IsOddTransp (π '' C) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    have hd : orderOf (π c) ∣ 2 := (orderOf_map_dvd π c).trans (hC.1 c hc).dvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) (h1 c hc)
    · exact h
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
    rw [← map_mul]
    rcases hC.2 c hc d hd with h | h
    · exact Or.inl ((orderOf_map_dvd π _).trans h)
    · exact Or.inr (h.of_dvd_nat (orderOf_map_dvd π _))

theorem image_isConj_class (π : X →* Y) (hπ : Function.Surjective π) (d₀ : X) :
    π '' {g | IsConj d₀ g} = {g | IsConj (π d₀) g} := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact π.map_isConj hc
  · intro h
    obtain ⟨y, hy⟩ := isConj_iff.1 h
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨x * d₀ * x⁻¹, isConj_iff.2 ⟨x, rfl⟩, by rw [← hy]; simp⟩

theorem closure_image_eq_top (π : X →* Y) (hπ : Function.Surjective π) {C : Set X}
    (hgen : Subgroup.closure C = ⊤) : Subgroup.closure (π '' C) = ⊤ := by
  rw [← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective π hπ]

theorem mul_self_eq_one_of_mem {C : Set X} (hC : IsOddTransp C) {c : X} (hc : c ∈ C) :
    c * c = 1 := by
  rw [← sq]
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hC.1 c hc])

theorem commute_of_mul_self_eq_one {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h : a * b * (a * b) = 1) : a * b = b * a := by
  have h' := inv_eq_of_mul_eq_one_right h
  rwa [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb, eq_comm] at h'

theorem orderOf_mul_eq_two {a b : Y} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hne : a ≠ b) : orderOf (a * b) = 2 := by
  refine orderOf_eq_prime (p := 2) ?_ fun h => hne ?_
  · rw [(show Commute a b from hab).mul_pow, sq a, sq b, ha, hb, one_mul]
  · rw [eq_comm, ← inv_eq_of_mul_eq_one_right ha]
    exact eq_inv_of_mul_eq_one_right h

theorem commute_of_map_commute (π : X →* Y) {C : Set X} (hC : IsOddTransp C) {a b : X}
    (ha : a ∈ C) (hb : b ∈ C) (hcomm : π a * π b = π b * π a) (hne : π a ≠ π b) :
    a * b = b * a := by
  have hord2 : orderOf (π (a * b)) = 2 := by
    rw [map_mul]
    refine orderOf_mul_eq_two ?_ ?_ hcomm hne
    · rw [← map_mul, mul_self_eq_one_of_mem hC ha, map_one]
    · rw [← map_mul, mul_self_eq_one_of_mem hC hb, map_one]
  have h2dvd : 2 ∣ orderOf (a * b) := hord2 ▸ orderOf_map_dvd π _
  have hdvd : orderOf (a * b) ∣ 2 := by
    rcases hC.2 a ha b hb with h | ⟨l, hl⟩
    · exact h
    · omega
  exact commute_of_mul_self_eq_one (mul_self_eq_one_of_mem hC ha) (mul_self_eq_one_of_mem hC hb)
    (by rw [← sq]; exact orderOf_dvd_iff_pow_eq_one.1 hdvd)

theorem pow_three_of_map (π : X →* Y) (hker : π.ker ≤ Subgroup.center X) {C : Set X}
    (hC : IsOddTransp C) {a b : X} (ha : a ∈ C) (hb : b ∈ C) (h3 : (π a * π b) ^ 3 = 1)
    (hne : π a ≠ π b) : (a * b) ^ 3 = 1 := by
  have hsa := mul_self_eq_one_of_mem hC ha
  have hsb := mul_self_eq_one_of_mem hC hb
  have hord3 : orderOf (π (a * b)) = 3 := by
    rw [map_mul]
    refine orderOf_eq_prime h3 fun h => hne ?_
    have h' := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right (by rw [← map_mul, hsa, map_one])] at h'
    exact h'.symm
  have h3dvd : 3 ∣ orderOf (a * b) := hord3 ▸ orderOf_map_dvd π _
  have hodd : Odd (orderOf (a * b)) := by
    rcases hC.2 a ha b hb with h | h
    · exact absurd (Nat.le_of_dvd two_pos (h3dvd.trans h)) (by norm_num)
    · exact h
  have hcen : (a * b) ^ 3 ∈ Subgroup.center X :=
    hker (by rw [MonoidHom.mem_ker, map_pow, map_mul, h3])
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hsa, inv_eq_of_mul_eq_one_right hsb,
      ← mul_assoc, hsa, one_mul]
  have hsqa : (a * b) ^ 3 * (a * b) ^ 3 = 1 := by
    have h2 : a * (a * b) ^ 3 * a⁻¹ = (a * b) ^ 3 := by
      rw [Subgroup.mem_center_iff.1 hcen a, mul_assoc, mul_inv_cancel, mul_one]
    rw [← conj_pow, hconj, inv_pow] at h2
    exact mul_eq_one_iff_eq_inv.2 h2.symm
  have hdvd2 : orderOf ((a * b) ^ 3) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsqa)
  have hodd' : Odd (orderOf ((a * b) ^ 3)) := hodd.of_dvd_nat (orderOf_pow_dvd 3)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd hodd' (by rw [h]; decide)

theorem isCoxeterA_lift (π : X →* Y) (hker : π.ker ≤ Subgroup.center X) {C : Set X}
    (hC : IsOddTransp C) {m : ℕ} {s : ℕ → Y} (hs : IsCoxeterA m s)
    (hne : ∀ i < m, ∀ j < m, i ≠ j → s i ≠ s j) {d : ℕ → X} (hdC : ∀ i < m, d i ∈ C)
    (hds : ∀ i < m, π (d i) = s i) : IsCoxeterA m d := by
  refine isCoxeterA_of_pow_three (fun i hi => mul_self_eq_one_of_mem hC (hdC i hi))
    (fun i hi => ?_) fun i j hij hj => ?_
  · have hi' : i < m := by omega
    refine pow_three_of_map π hker hC (hdC i hi') (hdC (i + 1) hi) ?_ ?_
    · rw [hds i hi', hds (i + 1) hi]
      exact IsCoxeterA.pow_three hs hi
    · rw [hds i hi', hds (i + 1) hi]
      exact hne i hi' (i + 1) hi (by omega)
  · have hi : i < m := by omega
    refine commute_of_map_commute π hC (hdC i hi) (hdC j hj) ?_ ?_
    · rw [hds i hi, hds j hj]
      exact hs.comm i j hij hj
    · rw [hds i hi, hds j hj]
      exact hne i hi j hj (by omega)

theorem exists_lifts (π : X →* Y) {C : Set X} {m : ℕ} {s : ℕ → Y}
    (hsC : ∀ i < m, s i ∈ π '' C) : ∃ d : ℕ → X, ∀ i < m, d i ∈ C ∧ π (d i) = s i := by
  have hlift : ∀ i, ∃ c : X, i < m → c ∈ C ∧ π c = s i := fun i => by
    by_cases hi : i < m
    · obtain ⟨c, hc, hcs⟩ := hsC i hi
      exact ⟨c, fun _ => ⟨hc, hcs⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose d hd using hlift
  exact ⟨d, hd⟩

theorem mem_of_isConj_of_ker_le_center (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {S : Subgroup X} (hS : ∀ x : X, ∃ s ∈ S, s⁻¹ * x ∈ π.ker) {d c : X} (hd : d ∈ S)
    (hc : IsConj d c) : c ∈ S := by
  obtain ⟨y, rfl⟩ := isConj_iff.1 hc
  obtain ⟨s, hs, hz⟩ := hS y
  obtain ⟨z, hz', rfl⟩ : ∃ z ∈ Subgroup.center X, y = s * z := ⟨s⁻¹ * y, hker hz, by simp⟩
  have hcomm := Subgroup.mem_center_iff.1 hz' d
  have h : s * z * d * (s * z)⁻¹ = s * d * s⁻¹ := by
    calc s * z * d * (s * z)⁻¹ = s * (z * d * z⁻¹) * s⁻¹ := by group
      _ = s * d * s⁻¹ := by rw [← hcomm]; group
  rw [h]
  exact S.mul_mem (S.mul_mem hs hd) (S.inv_mem hs)

end Lifting

section Core

theorem adjSwap_injOn {m i j : ℕ} (hi : i < m) (hj : j < m) (h : adjSwap m i = adjSwap m j) :
    i = j := by
  rw [adjSwap_of_lt hi, adjSwap_of_lt hj] at h
  rcases swap_eq_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact congrArg Fin.val h1
  · have h1' := congrArg Fin.val h1
    have h2' := congrArg Fin.val h2
    simp only at h1' h2'
    omega

variable {X : Type*} [Group X]

theorem ker_eq_bot_of_coxeter {m : ℕ} (hm : 2 ≤ m) (π : X →* Perm (Fin (m + 1)))
    (hker : π.ker ≤ Subgroup.center X) {d₀ : X}
    (hC : IsOddTransp {g | IsConj d₀ g}) (hgen : Subgroup.closure {g | IsConj d₀ g} = ⊤)
    {s : ℕ → Perm (Fin (m + 1))} (hs : IsCoxeterA m s) (h01 : s 0 ≠ s 1)
    (h02 : 3 ≤ m → s 0 ≠ s 2) (hsC : ∀ i < m, s i ∈ π '' {g | IsConj d₀ g}) : π.ker = ⊥ := by
  obtain ⟨d, hd⟩ := exists_lifts π hsC
  obtain ⟨ψs, hψs⟩ := exists_hom_perm m s hs
  have hψsinj := injective_of_adjSwap_images hm hψs h01 h02
  have hne : ∀ i < m, ∀ j < m, i ≠ j → s i ≠ s j := fun i hi j hj hij h =>
    hij (adjSwap_injOn hi hj (hψsinj (by rw [hψs i hi, hψs j hj, h])))
  have hcox : IsCoxeterA m d :=
    isCoxeterA_lift π hker hC hs hne (fun i hi => (hd i hi).1) fun i hi => (hd i hi).2
  obtain ⟨ψ, hψ⟩ := exists_hom_perm m d hcox
  have hφ : ∀ i < m, (π.comp ψ) (adjSwap m i) = s i := fun i hi => by
    simp [hψ i hi, (hd i hi).2]
  have hφinj : Function.Injective (π.comp ψ) :=
    injective_of_adjSwap_images hm hφ h01 h02
  have hφsurj : Function.Surjective (π.comp ψ) := Finite.injective_iff_surjective.1 hφinj
  have hS : ∀ x : X, ∃ t ∈ ψ.range, t⁻¹ * x ∈ π.ker := fun x => by
    obtain ⟨g, hg⟩ := hφsurj (π x)
    refine ⟨ψ g, ⟨g, rfl⟩, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    rw [MonoidHom.comp_apply] at hg
    rw [hg, inv_mul_cancel]
  have hd0 : d 0 ∈ ψ.range := ⟨adjSwap m 0, hψ 0 (by omega)⟩
  have hCle : {g | IsConj d₀ g} ⊆ ψ.range := fun c hc =>
    mem_of_isConj_of_ker_le_center π hker hS hd0
      (((hd 0 (by omega)).1 : IsConj d₀ (d 0)).symm.trans hc)
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le _).2 hCle
  refine eq_bot_iff.2 fun k hk => ?_
  obtain ⟨g, rfl⟩ : k ∈ ψ.range := hrange ▸ Subgroup.mem_top k
  have hg1 : g = 1 := hφinj (by rw [MonoidHom.comp_apply, map_one]; exact MonoidHom.mem_ker.1 hk)
  rw [hg1, map_one]
  exact Subgroup.one_mem _

end Core

section Triples

def triples : Fin 5 → Perm (Fin 6) :=
  ![swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 4 * swap 3 5,
    swap 0 1 * swap 2 5 * swap 3 4, swap 0 2 * swap 1 3 * swap 4 5,
    swap 0 1 * swap 2 4 * swap 3 5]

def tripleSys (i : ℕ) : Perm (Fin 6) := if h : i < 5 then triples ⟨i, h⟩ else 1

theorem tripleSys_of_lt {i : ℕ} (h : i < 5) : tripleSys i = triples ⟨i, h⟩ := dif_pos h

theorem triples_sq : ∀ i, triples i * triples i = 1 := by decide +kernel

theorem triples_braid : ∀ i j : Fin 5, j.val = i.val + 1 →
    triples i * triples j * triples i = triples j * triples i * triples j := by decide +kernel

theorem triples_comm : ∀ i j : Fin 5, i.val + 2 ≤ j.val →
    triples i * triples j = triples j * triples i := by decide +kernel

theorem triples_card : ∀ i, (triples i).support.card = 6 := by decide +kernel

theorem triples_ne_zero_one : triples 0 ≠ triples 1 := by decide +kernel

theorem triples_ne_zero_two : triples 0 ≠ triples 2 := by decide +kernel

theorem isCoxeterA_tripleSys : IsCoxeterA 5 tripleSys :=
  ⟨fun i hi => by rw [tripleSys_of_lt hi]; exact triples_sq _,
    fun i hi => by
      rw [tripleSys_of_lt (by omega : i < 5), tripleSys_of_lt hi]
      exact triples_braid _ _ rfl,
    fun i j hij hj => by
      rw [tripleSys_of_lt (by omega : i < 5), tripleSys_of_lt hj]
      exact triples_comm _ _ hij⟩

theorem cycleType_triples (i : Fin 5) : (triples i).cycleType = Multiset.replicate 3 2 := by
  have hsq := triples_sq i
  have hne : triples i ≠ 1 := fun h => by
    have := triples_card i
    rw [h] at this
    simp at this
  have hord : orderOf (triples i) = 2 := orderOf_eq_prime (by rwa [sq]) hne
  obtain ⟨k, hk⟩ := exists_cycleType_replicate_two hord
  have hsum := sum_cycleType (triples i)
  rw [triples_card, hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hk]
  congr 1
  omega

end Triples

end CentralSymSplit

open Equiv Equiv.Perm CentralSymSplit in
theorem isSwap_or_triple_of_isOddTransp {n : ℕ} (hn : 5 ≤ n) {C : Set (Equiv.Perm (Fin n))}
    (hC : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp C)
    (hcls : ∃ σ₀ : Equiv.Perm (Fin n), C = {g | IsConj σ₀ g})
    (hgen : Subgroup.closure C = ⊤) :
    (∀ σ ∈ C, σ.IsSwap) ∨ (n = 6 ∧ ∀ σ ∈ C, σ.cycleType = Multiset.replicate 3 2) := by
  obtain ⟨σ₀, rfl⟩ := hcls
  have hmem : σ₀ ∈ {g | IsConj σ₀ g} := IsConj.refl σ₀
  have hord : orderOf σ₀ = 2 := hC.1 σ₀ hmem
  obtain ⟨k, hk⟩ := exists_cycleType_replicate_two hord
  obtain ⟨m, hm⟩ := odd_of_closure_eq_top (by omega) hk hgen
  have hsupp : σ₀.support.card = 2 * (k + 1) := by
    rw [← sum_cycleType, hk, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hcompl : σ₀.supportᶜ.card = n - 2 * (k + 1) := by
    rw [Finset.card_compl, Fintype.card_fin, hsupp]
  have hle : σ₀.support.card ≤ n := by
    simpa using Finset.card_le_univ σ₀.support
  have hsq : σ₀ * σ₀ = 1 := mul_self_eq_one_of_mem hC hmem
  have hinv : ∀ x, σ₀ (σ₀ x) = x := fun x => by
    simpa using congrArg (fun f : Perm (Fin n) => f x) hsq
  have hcyc : ∀ σ ∈ {g | IsConj σ₀ g}, σ.cycleType = Multiset.replicate (k + 1) 2 :=
    fun σ h => by rw [← hk]; exact (isConj_iff_cycleType_eq.1 h).symm
  by_cases hk0 : k = 0
  · left
    intro σ hσ
    refine Perm.card_support_eq_two.1 ?_
    rw [← sum_cycleType, hcyc σ hσ, hk0]
    simp
  · right
    by_cases hf2 : 2 ≤ n - 2 * (k + 1)
    · exfalso
      obtain ⟨τ, hτ, h4⟩ := exists_conj_four_dvd_of_two_fixed hinv (by omega) (by omega)
      exact false_of_dvd_orderOf_mul hC hmem hτ h4 (by norm_num) (by norm_num)
    by_cases hf1 : n - 2 * (k + 1) = 1
    · exfalso
      obtain ⟨τ, hτ, h6⟩ := exists_conj_six_dvd_of_one_fixed hinv (by omega) (by omega)
      exact false_of_dvd_orderOf_mul hC hmem hτ h6 (by norm_num) (by norm_num)
    by_cases hk2 : k = 2
    · exact ⟨by omega, fun σ hσ => by rw [hcyc σ hσ, hk2]⟩
    · exfalso
      obtain ⟨τ, hτ, h4⟩ := exists_conj_four_dvd_of_four_pairs hinv (by omega)
      exact false_of_dvd_orderOf_mul hC hmem hτ h4 (by norm_num) (by norm_num)

theorem isSwap_of_isOddTransp_class_three {C : Set (Equiv.Perm (Fin 3))}
    (hC : IsOddTransp C) : ∀ σ ∈ C, σ.IsSwap := by
  intro σ hσ
  have hord : orderOf σ = 2 := hC.1 σ hσ
  have hne : σ ≠ 1 := by rintro rfl; rw [orderOf_one] at hord; omega
  have hsq : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hord, pow_two] at h
  exact CFSG.GroupTheory.isSwap_of_mul_self_eq_one_fin_three σ hne hsq

theorem isSwap_of_isOddTransp_class_four {C : Set (Equiv.Perm (Fin 4))}
    (hC : IsOddTransp C) (hcls : ∃ σ₀ : Equiv.Perm (Fin 4), C = {g | IsConj σ₀ g})
    (hgen : Subgroup.closure C = ⊤) : ∀ σ ∈ C, σ.IsSwap := by
  obtain ⟨σ₀, rfl⟩ := hcls
  intro σ hσ
  by_contra hns
  have hord : orderOf σ = 2 := hC.1 σ hσ
  have hne : σ ≠ 1 := by rintro rfl; rw [orderOf_one] at hord; omega
  have hsq : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hord, pow_two] at h
  have hsupp4 := CFSG.GroupTheory.card_support_eq_four_of_mul_self_eq_one_not_isSwap_fin_four
    σ hne hsq hns
  obtain ⟨k, hk⟩ := CentralSymSplit.exists_cycleType_replicate_two hord
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hk, hsupp4, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk1 : k = 1 := by omega
  have hcyc : σ.cycleType = Multiset.replicate 2 2 := by rw [hk, hk1]
  have hcyc0 : σ₀.cycleType = Multiset.replicate 2 2 :=
    (Equiv.Perm.isConj_iff_cycleType_eq.mp hσ).trans hcyc
  have hodd := CentralSymSplit.odd_of_closure_eq_top (n := 4) (by norm_num) hcyc0 hgen
  exact absurd hodd (by rintro ⟨k, hk⟩; omega)

open Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter CentralSymSplit in
theorem ker_eq_bot_of_isSwap {X : Type*} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (π : X →* Equiv.Perm (Fin (m + 1))) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) {d₀ : X} (hodd : IsOddTransp {g | IsConj d₀ g})
    (hgen : Subgroup.closure {g | IsConj d₀ g} = ⊤) (hsw : (π d₀).IsSwap) : π.ker = ⊥ := by
  obtain ⟨x, y, hxy, hπd₀⟩ := hsw
  have hcls := image_isConj_class π hπ d₀
  refine ker_eq_bot_of_coxeter hm π hker hodd hgen (isCoxeterA_adjSwap m)
    (fun h => ?_) (fun h3 h => ?_) fun i hi => ?_
  · have := adjSwap_injOn (by omega) (by omega) h
    omega
  · have := adjSwap_injOn (by omega) (by omega) h
    omega
  · rw [hcls, Set.mem_setOf_eq, adjSwap_of_lt hi, hπd₀]
    exact isConj_swap hxy (by simp [Fin.ext_iff])

open Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter CentralSymSplit in
theorem ker_eq_bot_of_isOddTranspClass {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : 5 ≤ n)
    (π : X →* Equiv.Perm (Fin n)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) {C : Set X}
    (hC : CFSG.Timmesfeld.Bridge.Asc72.IsOddTranspClass C) :
    π.ker = ⊥ := by
  obtain ⟨⟨d₀, rfl⟩, hodd, hgen⟩ := hC
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hodd' := isOddTransp_image π hodd fun c hc => map_ne_one_of_isConj π hπ hgen hc
  have hcls := image_isConj_class π hπ d₀
  have hgen' := closure_image_eq_top π hπ hgen
  have hmem : π d₀ ∈ π '' {g | IsConj d₀ g} := ⟨d₀, IsConj.refl d₀, rfl⟩
  rcases isSwap_or_triple_of_isOddTransp hn hodd' ⟨π d₀, hcls⟩ hgen' with hsw | ⟨h6, htr⟩
  · exact ker_eq_bot_of_isSwap (by omega) π hπ hker hodd hgen (hsw _ hmem)
  · obtain rfl : m = 5 := by omega
    refine ker_eq_bot_of_coxeter (by omega) π hker hodd hgen isCoxeterA_tripleSys
      (fun h => ?_) (fun _ h => ?_) fun i hi => ?_
    · rw [tripleSys_of_lt (by norm_num), tripleSys_of_lt (by norm_num)] at h
      exact triples_ne_zero_one h
    · rw [tripleSys_of_lt (by norm_num), tripleSys_of_lt (by norm_num)] at h
      exact triples_ne_zero_two h
    · rw [hcls, Set.mem_setOf_eq, tripleSys_of_lt hi]
      exact isConj_iff_cycleType_eq.2 ((htr _ hmem).trans (cycleType_triples ⟨i, hi⟩).symm)

open CentralSymSplit in
theorem ker_eq_bot_of_isOddTranspClass_of_three_le {X : Type*} [Group X] [Finite X] {n : ℕ}
    (hn : 3 ≤ n) (π : X →* Equiv.Perm (Fin n)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) {C : Set X}
    (hC : CFSG.Timmesfeld.Bridge.Asc72.IsOddTranspClass C) : π.ker = ⊥ := by
  rcases le_or_gt 5 n with h5 | h5
  · exact ker_eq_bot_of_isOddTranspClass h5 π hπ hker hC
  obtain ⟨⟨d₀, rfl⟩, hodd, hgen⟩ := hC
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Nontrivial (Fin (m + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hodd' := isOddTransp_image π hodd fun c hc => map_ne_one_of_isConj π hπ hgen hc
  have hmem : π d₀ ∈ π '' {g | IsConj d₀ g} := ⟨d₀, IsConj.refl d₀, rfl⟩
  obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
  · exact ker_eq_bot_of_isSwap le_rfl π hπ hker hodd hgen
      (isSwap_of_isOddTransp_class_three hodd' _ hmem)
  · exact ker_eq_bot_of_isSwap (by norm_num) π hπ hker hodd hgen
      (isSwap_of_isOddTransp_class_four hodd' ⟨π d₀, image_isConj_class π hπ d₀⟩
        (closure_image_eq_top π hπ hgen) _ hmem)

end CFSG.OddTranspositions.PartThree

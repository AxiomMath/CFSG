module

public import CFSG.Timmesfeld.Bridge.RootStructTwoLocalCount

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

theorem pow_eq_one_iff_even_of_mul_self {G : Type*} [Group G] {a : G} (ha1 : a ≠ 1)
    (haa : a * a = 1) {n : ℕ} : a ^ n = 1 ↔ Even n := by
  have h2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq, haa]) ha1
  rw [← orderOf_dvd_iff_pow_eq_one, h2, even_iff_two_dvd]

theorem conj_list_prod {G : Type*} [Group G] [DecidableEq G] {a c : G} (l : List G)
    (hal : ∀ y ∈ l, Commute a y) (hc : ∀ y ∈ l, c * y * c⁻¹ = y ∨ c * y * c⁻¹ = a * y) :
    c * l.prod * c⁻¹ = a ^ (l.countP fun y => c * y * c⁻¹ ≠ y) * l.prod := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have ih' := ih (fun z hz => hal z (List.mem_cons_of_mem _ hz))
      (fun z hz => hc z (List.mem_cons_of_mem _ hz))
    have hay := hal y List.mem_cons_self
    rw [List.prod_cons, List.countP_cons]
    have e : c * (y * l.prod) * c⁻¹ = (c * y * c⁻¹) * (c * l.prod * c⁻¹) := by group
    rw [e, ih']
    by_cases hy : c * y * c⁻¹ = y
    · simp only [hy, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        add_zero]
      rw [← mul_assoc, ← (hay.pow_left _).eq, mul_assoc]
    · have hy' : c * y * c⁻¹ = a * y := (hc y List.mem_cons_self).resolve_left hy
      simp only [hy, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      rw [hy', pow_succ, mul_assoc a, ← mul_assoc y, ← (hay.pow_left _).eq]
      group

theorem list_prod_conj {G : Type*} [Group G] [DecidableEq G] {a x : G} (l : List G)
    (hal : ∀ y ∈ l, Commute a y)
    (hl : ∀ y ∈ l, y * x * y⁻¹ = x ∨ y * x * y⁻¹ = a * x) :
    l.prod * x * l.prod⁻¹ = a ^ (l.countP fun y => y * x * y⁻¹ ≠ x) * x := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have ih' := ih (fun z hz => hal z (List.mem_cons_of_mem _ hz))
      (fun z hz => hl z (List.mem_cons_of_mem _ hz))
    have hay := hal y List.mem_cons_self
    rw [List.prod_cons, List.countP_cons]
    have e : y * l.prod * x * (y * l.prod)⁻¹ = y * (l.prod * x * l.prod⁻¹) * y⁻¹ := by group
    rw [e, ih']
    set n := l.countP fun y => y * x * y⁻¹ ≠ x
    have e' : y * (a ^ n * x) * y⁻¹ = a ^ n * (y * x * y⁻¹) := by
      calc y * (a ^ n * x) * y⁻¹ = y * a ^ n * x * y⁻¹ := by group
        _ = a ^ n * y * x * y⁻¹ := by rw [← (hay.pow_left n).eq]
        _ = a ^ n * (y * x * y⁻¹) := by group
    rw [e']
    by_cases hy : y * x * y⁻¹ = x
    · simp only [hy, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        add_zero]
    · have hy' : y * x * y⁻¹ = a * x := (hl y List.mem_cons_self).resolve_left hy
      simp only [hy, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      rw [hy', pow_succ, mul_assoc]

theorem countP_ne_eq {G : Type*} [DecidableEq G] {l : List G} (hl : l.Nodup) (x : G) :
    (l.countP fun y => y ≠ x) = l.length - (if x ∈ l then 1 else 0) := by
  have h := List.length_eq_countP_add_countP (l := l) (fun y => decide (y ≠ x))
  have e : List.countP (fun y => decide ¬decide (y ≠ x) = true) l = l.count x := by
    rw [List.count_eq_countP]
    congr 1
    ext y
    by_cases hyx : y = x <;> simp [hyx]
  have h2 : l.count x = if x ∈ l then 1 else 0 := by
    split_ifs with hx
    · exact List.count_eq_one_of_mem hl hx
    · exact List.count_eq_zero_of_not_mem hx
  omega

namespace TwoLocalSetting

variable {G : Type*} [Group G] {D : Set G} (S : TwoLocalSetting G D)
include S

theorem ncard_le_of_pairwise {a : G} (ha : a ∈ D) {Q : Set G}
    (hQ : ∀ x ∈ Q, x ∈ D ∧ Commute a x ∧ x ≠ a) (hnc : Q.Pairwise fun x y => ¬ Commute x y) :
    Q.ncard ≤ (rootLines D a).ncard := by
  have := S.hyp.finite
  refine Set.ncard_le_ncard_of_injOn (fun x => rootGroup D a ⊔ rootGroup D x) ?_ ?_
    (Set.toFinite _)
  · intro x hx
    exact (S.mem_rootLines_iff ha).2 ⟨x, (hQ x hx).1, (hQ x hx).2.1, (hQ x hx).2.2, rfl⟩
  · intro x hx y hy hxy
    have hxy' : rootGroup D a ⊔ rootGroup D x = rootGroup D a ⊔ rootGroup D y := hxy
    by_contra hne
    apply hnc hx hy hne
    have hmem : y ∈ rootGroup D a ⊔ rootGroup D x := by
      rw [hxy']
      exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self (hQ y hy).1))
    rcases (S.mem_line_iff ha (hQ x hx).1 (hQ x hx).2.1 (hQ y hy).1).1 hmem with h | h | h
    · exact absurd h (hQ y hy).2.2
    · rw [h]
    · rw [h]
      exact (hQ x hx).2.1.symm.mul_right (Commute.refl x)

theorem conj_eq_or {a z y : G} (ha : a ∈ D) (hz : z ∈ D) (hy : y ∈ D) (haz : Commute a z)
    (hay : Commute a y) (hza : z ≠ a) (hya : y ≠ a) :
    z * y * z⁻¹ = y ∨ z * y * z⁻¹ = a * y := by
  by_cases hzy : Commute z y
  · left
    rw [hzy.eq, mul_inv_cancel_right]
  · exact Or.inr (S.conj_eq_mul_of_not_commute ha hz hy haz hay hza hya hzy)

theorem list_prod_commute [DecidableEq G] {a : G} (ha : a ∈ D) {l : List G}
    (hl : ∀ y ∈ l, y ∈ D ∧ Commute a y ∧ y ≠ a) (hnd : l.Nodup)
    (hnc : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ Commute x y) (hodd : Odd l.length)
    (hcov : ∀ z ∈ D, Commute a z → z ≠ a → ∃ y ∈ l, Commute z y) {z : G} (hz : z ∈ D)
    (haz : Commute a z) (hza : z ≠ a) : Commute z l.prod := by
  have hD := S.root
  obtain ⟨y₀, hy₀, hzy₀⟩ := hcov z hz haz hza
  have hconj := conj_list_prod l (fun y hy => (hl y hy).2.1) fun y hy =>
    S.conj_eq_or ha hz (hl y hy).1 haz (hl y hy).2.1 hza (hl y hy).2.2
  have hcount : (l.countP fun y => z * y * z⁻¹ ≠ y) = l.countP fun y => y ≠ y₀ := by
    refine List.countP_congr fun y hy => ?_
    simp only [ne_eq, decide_eq_true_eq]
    constructor
    · rintro hmove rfl
      exact hmove (by rw [hzy₀.eq, mul_inv_cancel_right])
    · intro hne hfix
      have hzy : Commute z y := mul_inv_eq_iff_eq_mul.1 hfix
      obtain ⟨hyD, hay, hya⟩ := hl y hy
      obtain ⟨hy₀D, hay₀, hy₀a⟩ := hl y₀ hy₀
      have h1 := (S.commute_iff_eq_or_eq_mul ha hz hyD haz hay hza hya).1 hzy
      have h2 := (S.commute_iff_eq_or_eq_mul ha hz hy₀D haz hay₀ hza hy₀a).1 hzy₀
      have hyy₀ : Commute y y₀ := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
        · exact haz.symm.mul_right (Commute.refl _)
        · exact haz.mul_left (Commute.refl _)
      exact hnc y hy y₀ hy₀ hne hyy₀
  rw [hcount, countP_ne_eq hnd] at hconj
  simp only [hy₀, ↓reduceIte] at hconj
  obtain ⟨m, hm⟩ := hodd
  rw [hm, Nat.add_sub_cancel, pow_mul, sq, hD.mul_self_eq_one ha, one_pow, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

end TwoLocalSetting

end CFSG.Timmesfeld.Bridge

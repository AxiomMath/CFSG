module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.PairSwapEightSubgroup

private theorem card_sup_le
    {G : Type*} [CommGroup G] [Finite G] (H K : Subgroup G) :
    Nat.card (H ⊔ K : Subgroup G) ≤ Nat.card H * Nat.card K := by
  let f : H × K → (H ⊔ K : Subgroup G) := fun t =>
    ⟨t.1.val * t.2.val, (H ⊔ K).mul_mem (Subgroup.mem_sup_left t.1.property) (Subgroup.mem_sup_right t.2.property)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨h, hh, k, hk, he⟩ := Subgroup.mem_sup.mp hg
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext he⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

theorem card_closure_le_eight
    {G : Type*} [CommGroup G] [Finite G] (a p q : G)
    (ha : a ^ 2 = 1) (hp : p ^ 2 = 1) (hq : q ^ 2 = 1) :
    Nat.card (Subgroup.closure ({a, p, q} : Set G)) ≤ 8 := by
  let A := Subgroup.zpowers a
  let P := Subgroup.zpowers p
  let Q := Subgroup.zpowers q
  have hA : Nat.card A ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one ha)
  have hP : Nat.card P ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hp)
  have hQ : Nat.card Q ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hq)
  have hle : Subgroup.closure ({a, p, q} : Set G) ≤ A ⊔ (P ⊔ Q) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    · rw [hg]; exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers p))
    · rw [hg]; exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers q))
  calc
    _ ≤ Nat.card (A ⊔ (P ⊔ Q) : Subgroup G) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card A * Nat.card (P ⊔ Q : Subgroup G) := card_sup_le A (P ⊔ Q)
    _ ≤ 2 * (2 * 2) := Nat.mul_le_mul hA ((card_sup_le P Q).trans (Nat.mul_le_mul hP hQ))
    _ = 8 := rfl

theorem eight_le_card_closure
    {G F : Type*} [Group G] [Finite G] [DecidableEq F]
    (f : G →* Equiv.Perm F) (e : Fin 6 ↪ F) (a p q : G)
    (ha : a ≠ 1) (hfa : f a = 1)
    (hp : f p = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3))
    (hq : f q = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5)) :
    8 ≤ Nat.card (Subgroup.closure ({a, p, q} : Set G)) := by
  let L := Subgroup.closure ({a, p, q} : Set G)
  have haL : a ∈ L := Subgroup.subset_closure (by simp)
  have hpL : p ∈ L := Subgroup.subset_closure (by simp)
  have hqL : q ∈ L := Subgroup.subset_closure (by simp)
  let v : Bool × Bool × Bool → L := fun t =>
    ⟨(if t.1 then a else 1) * (if t.2.1 then p else 1) * (if t.2.2 then q else 1), by
      apply L.mul_mem
      · apply L.mul_mem
        · split <;> first | exact haL | exact L.one_mem
        · split <;> first | exact hpL | exact L.one_mem
      · split <;> first | exact hqL | exact L.one_mem⟩
  have h2 (t : Bool × Bool × Bool) : f (v t).val (e 2) = if t.2.1 then e 3 else e 2 := by
    rcases t with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [v, map_mul, hfa, hp, hq, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have h4 (t : Bool × Bool × Bool) : f (v t).val (e 4) = if t.2.2 then e 5 else e 4 := by
    rcases t with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [v, map_mul, hfa, hp, hq, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hv : Function.Injective v := by
    intro s t he
    have he2 := congrArg (fun g : L => f g.val (e 2)) he
    have he4 := congrArg (fun g : L => f g.val (e 4)) he
    rw [h2, h2] at he2
    rw [h4, h4] at he4
    have hsp : s.2.1 = t.2.1 := by
      cases hs : s.2.1 <;> cases ht : t.2.1 <;> simp_all [e.injective.eq_iff]
    have hsq : s.2.2 = t.2.2 := by
      cases hs : s.2.2 <;> cases ht : t.2.2 <;> simp_all [e.injective.eq_iff]
    have he' := congrArg Subtype.val he
    change (if s.1 then a else 1) * (if s.2.1 then p else 1) * (if s.2.2 then q else 1) =
      (if t.1 then a else 1) * (if t.2.1 then p else 1) * (if t.2.2 then q else 1) at he'
    rw [hsp, hsq] at he'
    have hea := mul_right_cancel (mul_right_cancel he')
    have hsa : s.1 = t.1 := by
      cases hs : s.1 <;> cases ht : t.1 <;> simp_all
    exact Prod.ext hsa (Prod.ext hsp hsq)
  have hc := Nat.card_le_card_of_injective v hv
  norm_num only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool] at hc
  exact hc

end FiveTransitive.PairSwapEightSubgroup

end CFSG

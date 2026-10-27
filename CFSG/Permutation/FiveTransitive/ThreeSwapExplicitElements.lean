module

public import CFSG.Permutation.FiveTransitive.CyclicTwoCommutativeGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapExplicitElements

theorem exists_bits {F : Type*} [Finite F] [DecidableEq F] (e : Fin 6 ↪ F)
    (u : ThreeSwapTwoGroup.subgroup e) :
    ∃ b c d : Bool, u.val =
      (if b then Equiv.swap (e 0) (e 1) else 1) *
      (if c then Equiv.swap (e 2) (e 3) else 1) *
      (if d then Equiv.swap (e 4) (e 5) else 1) := by
  let V := ThreeSwapTwoGroup.subgroup e
  let t0 := Equiv.swap (e 0) (e 1)
  let t1 := Equiv.swap (e 2) (e 3)
  let t2 := Equiv.swap (e 4) (e 5)
  have hm0 : t0 ∈ V := Subgroup.subset_closure (by change t0 ∈ ({t0, t1, t2} : Set _); exact Set.mem_insert _ _)
  have hm1 : t1 ∈ V := Subgroup.subset_closure (by change t1 ∈ ({t0, t1, t2} : Set _); exact Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hm2 : t2 ∈ V := Subgroup.subset_closure (by change t2 ∈ ({t0, t1, t2} : Set _); exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  let f : Bool × Bool × Bool → V := fun p =>
    ⟨(if p.1 then t0 else 1) * (if p.2.1 then t1 else 1) * (if p.2.2 then t2 else 1), by
      apply V.mul_mem
      · apply V.mul_mem
        · split <;> first | exact hm0 | exact V.one_mem
        · split <;> first | exact hm1 | exact V.one_mem
      · split <;> first | exact hm2 | exact V.one_mem⟩
  have h0 (p : Bool × Bool × Bool) : (f p).val (e 0) = if p.1 then e 1 else e 0 := by
    rcases p with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [f, t0, t1, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have h1 (p : Bool × Bool × Bool) : (f p).val (e 2) = if p.2.1 then e 3 else e 2 := by
    rcases p with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [f, t0, t1, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have h2 (p : Bool × Bool × Bool) : (f p).val (e 4) = if p.2.2 then e 5 else e 4 := by
    rcases p with ⟨b, c, d⟩
    cases b <;> cases c <;> cases d <;>
      simp [f, t0, t1, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hf : Function.Injective f := by
    intro p q hpq
    have hp0 := congrArg (fun v : V => v.val (e 0)) hpq
    have hp1 := congrArg (fun v : V => v.val (e 2)) hpq
    have hp2 := congrArg (fun v : V => v.val (e 4)) hpq
    rw [h0, h0] at hp0
    rw [h1, h1] at hp1
    rw [h2, h2] at hp2
    have he0 : p.1 = q.1 := by
      cases hp : p.1 <;> cases hq : q.1 <;> simp [hp, hq, e.injective.eq_iff] at hp0 ⊢
    have he1 : p.2.1 = q.2.1 := by
      cases hp : p.2.1 <;> cases hq : q.2.1 <;> simp [hp, hq, e.injective.eq_iff] at hp1 ⊢
    have he2 : p.2.2 = q.2.2 := by
      cases hp : p.2.2 <;> cases hq : q.2.2 <;> simp [hp, hq, e.injective.eq_iff] at hp2 ⊢
    exact Prod.ext he0 (Prod.ext he1 he2)
  have hsur : Function.Surjective f := (hf.bijective_of_nat_card_le (by
    rw [CyclicTwoCommutativeGroup.local_card]
    norm_num only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool])).surjective
  obtain ⟨⟨b,c,d⟩, he⟩ := hsur u
  exact ⟨b,c,d,(congrArg Subtype.val he).symm⟩

end FiveTransitive.ThreeSwapExplicitElements

end CFSG

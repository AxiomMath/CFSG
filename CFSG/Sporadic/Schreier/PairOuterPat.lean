module

public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairClasses

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

theorem patRel_map (conds : List (List Bool × ℕ)) (α : MulAut G) {x y : G} :
    PatRel conds (α x) (α y) ↔ PatRel conds x y := by
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  have h : (c.1.map fun b => if b then α y else α x) =
      (c.1.map fun b => if b then y else x).map α := by
    rw [List.map_map]
    refine List.map_congr_left fun b _ => ?_
    cases b <;> rfl
  rw [h, ← map_list_prod, MulEquiv.orderOf_eq]

theorem patRel_coe {H : Subgroup G} (conds : List (List Bool × ℕ)) (x y : H) :
    PatRel conds (x : G) (y : G) ↔ PatRel conds x y := by
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  rw [← Subgroup.orderOf_coe, Subgroup.val_list_prod, List.map_map]
  have e : (Subtype.val ∘ fun b : Bool => if b then y else x) =
      fun b => if b then (y : G) else x := by
    funext b
    cases b <;> rfl
  rw [e]

theorem aut_card_le_patRel [Finite G] {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (conds : List (List Bool × ℕ)) (hab : PatRel conds a b) :
    Nat.card (MulAut G) ≤ Nat.card {p : G × G // orderOf p.1 = orderOf a ∧
      orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} := by
  refine Nat.card_le_card_of_injective (fun α => ⟨(α a, α b), MulEquiv.orderOf_eq α a,
    MulEquiv.orderOf_eq α b, (patRel_map conds α).2 hab⟩) ?_
  intro α β h
  have h1 : α a = β a := congrArg (fun p : {p : G × G // orderOf p.1 = orderOf a ∧
    orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} => p.1.1) h
  have h2 : α b = β b := congrArg (fun p : {p : G × G // orderOf p.1 = orderOf a ∧
    orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} => p.1.2) h
  have heq : α.toMonoidHom = β.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro x hx
    rcases hx with rfl | hx
    · exact h1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h2
  exact MulEquiv.ext fun g => DFunLike.congr_fun heq g

theorem outer_card_le_of_patCounts [Finite G] (hs : IsSimpleGroup G) {a b : G}
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hcomm : a * b ≠ b * a)
    (conds : List (List Bool × ℕ)) (hab : PatRel conds a b) {N T k : ℕ} (hN : Nat.card G = N)
    (hN0 : 0 < N)
    (hT : Nat.card {p : G × G // orderOf p.1 = orderOf a ∧ orderOf p.2 = orderOf b ∧
      PatRel conds p.1 p.2} = T)
    (hk : T ≤ k * N) : Nat.card (Outer G) ≤ k := by
  have haut := aut_card_le_patRel hgen conds hab
  have hquot := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [card_inner_of_center_eq_bot (center_eq_bot_of_simple hs hcomm)] at hquot
  have h : Nat.card (Outer G) * Nat.card G ≤ T := by
    change Nat.card (MulAut G ⧸ inner G) * Nat.card G ≤ _
    rw [← hquot, ← hT]
    exact haut
  rw [hN] at h
  exact Nat.le_of_mul_le_mul_right (h.trans hk) hN0

end CFSG.Sporadic.Schreier

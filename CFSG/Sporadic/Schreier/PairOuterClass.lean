module

public import CFSG.Sporadic.Schreier.PairOuterPat

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

theorem card_isConj_map (α : MulAut G) (a : G) :
    Nat.card {x : G // IsConj (α a) x} = Nat.card {x : G // IsConj a x} := by
  refine (Nat.card_congr (α.toEquiv.subtypeEquiv fun x => ?_)).symm
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact isConj_iff.2 ⟨α c, by
      change α c * α a * (α c)⁻¹ = α x
      rw [← map_inv, ← map_mul, ← map_mul, hc]⟩
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨α.symm c, α.injective ?_⟩
    change α (α.symm c * a * (α.symm c)⁻¹) = α x
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc

theorem card_pairs_le_of_class [Finite G] {A : G → Prop} {R : G → G → Prop} {m : ℕ}
    (h : ∀ x, A x → Nat.card {y // R x y} ≤ m) :
    Nat.card {p : G × G // A p.1 ∧ R p.1 p.2} ≤ Nat.card {x // A x} * m := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let e : {p : G × G // A p.1 ∧ R p.1 p.2} ≃ Σ x : {x // A x}, {y // R x y} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma, Nat.card_eq_fintype_card (α := {x // A x}),
    ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun x _ => h x.1 x.2

theorem aut_card_le_classPat [Finite G] {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (conds : List (List Bool × ℕ)) (hab : PatRel conds a b) :
    Nat.card (MulAut G) ≤ Nat.card {p : G × G //
      Nat.card {x : G // IsConj p.1 x} = Nat.card {x : G // IsConj a x} ∧
      orderOf p.1 = orderOf a ∧ orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} := by
  refine Nat.card_le_card_of_injective (fun α => ⟨(α a, α b), card_isConj_map α a,
    MulEquiv.orderOf_eq α a, MulEquiv.orderOf_eq α b, (patRel_map conds α).2 hab⟩) ?_
  intro α β h
  have h1 : α a = β a := congrArg (fun p : {p : G × G //
    Nat.card {x : G // IsConj p.1 x} = Nat.card {x : G // IsConj a x} ∧
      orderOf p.1 = orderOf a ∧ orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} => p.1.1) h
  have h2 : α b = β b := congrArg (fun p : {p : G × G //
    Nat.card {x : G // IsConj p.1 x} = Nat.card {x : G // IsConj a x} ∧
      orderOf p.1 = orderOf a ∧ orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} => p.1.2) h
  have heq : α.toMonoidHom = β.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    intro x hx
    rcases hx with rfl | hx
    · exact h1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact h2
  exact MulEquiv.ext fun g => DFunLike.congr_fun heq g

theorem outer_card_le_of_classPatCounts [Finite G] (hs : IsSimpleGroup G) {a b : G}
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (hcomm : a * b ≠ b * a)
    (conds : List (List Bool × ℕ)) (hab : PatRel conds a b) {N T k : ℕ} (hN : Nat.card G = N)
    (hN0 : 0 < N)
    (hT : Nat.card {p : G × G //
      Nat.card {x : G // IsConj p.1 x} = Nat.card {x : G // IsConj a x} ∧
      orderOf p.1 = orderOf a ∧ orderOf p.2 = orderOf b ∧ PatRel conds p.1 p.2} ≤ T)
    (hk : T ≤ k * N) : Nat.card (Outer G) ≤ k := by
  have haut := aut_card_le_classPat hgen conds hab
  have hquot := (inner G).card_eq_card_quotient_mul_card_subgroup
  rw [card_inner_of_center_eq_bot (center_eq_bot_of_simple hs hcomm)] at hquot
  have h : Nat.card (Outer G) * Nat.card G ≤ T := by
    change Nat.card (MulAut G ⧸ inner G) * Nat.card G ≤ _
    rw [← hquot]
    exact haut.trans hT
  rw [hN] at h
  exact Nat.le_of_mul_le_mul_right (h.trans hk) hN0

end CFSG.Sporadic.Schreier

end

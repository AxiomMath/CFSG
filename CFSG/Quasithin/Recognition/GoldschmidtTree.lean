module

public import CFSG.Quasithin.Recognition.GoldschmidtCompletion

public section

namespace CFSG.Quasithin

section CosetGraph

variable {D : Type*} [Group D]

@[expose] def goldCosetRel (A B : Subgroup D) :
    (D ⧸ A) ⊕ (D ⧸ B) → (D ⧸ A) ⊕ (D ⧸ B) → Prop
  | .inl x, .inr y => ∃ g : D, (g : D ⧸ A) = x ∧ (g : D ⧸ B) = y
  | _, _ => False

@[expose] def goldCosetGraph (A B : Subgroup D) : SimpleGraph ((D ⧸ A) ⊕ (D ⧸ B)) :=
  SimpleGraph.fromRel (goldCosetRel A B)

theorem goldCosetGraph_adj_inl_inr (A B : Subgroup D) (x : D ⧸ A) (y : D ⧸ B) :
    (goldCosetGraph A B).Adj (.inl x) (.inr y) ↔ ∃ g : D, (g : D ⧸ A) = x ∧ (g : D ⧸ B) = y := by
  simp [goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel]

theorem goldCosetGraph_adj_base (A B : Subgroup D) (g : D) :
    (goldCosetGraph A B).Adj (.inl (g : D ⧸ A)) (.inr (g : D ⧸ B)) :=
  (goldCosetGraph_adj_inl_inr A B _ _).mpr ⟨g, rfl, rfl⟩

theorem goldCosetGraph_connected (A B : Subgroup D) (h : A ⊔ B = ⊤) :
    (goldCosetGraph A B).Connected := by
  have hbase : ∀ g : D,
      (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A)) (.inl (g : D ⧸ A)) := by
    intro g
    have hg : g ∈ A ⊔ B := h ▸ Subgroup.mem_top g
    rw [Subgroup.sup_eq_closure] at hg
    have key : ∀ x ∈ Subgroup.closure ((A : Set D) ∪ B), ∀ g : D,
        (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A)) (.inl (g : D ⧸ A)) →
        (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A)) (.inl ((g * x : D) : D ⧸ A)) ∧
        (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A))
          (.inl ((g * x⁻¹ : D) : D ⧸ A)) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        intro g hgR
        have step : ∀ y ∈ (A ∪ B : Set D), ∀ g : D,
            (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A)) (.inl (g : D ⧸ A)) →
            (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A))
              (.inl ((g * y : D) : D ⧸ A)) := by
          intro y hy g hgR
          rcases hy with hyA | hyB
          · have : ((g * y : D) : D ⧸ A) = (g : D ⧸ A) := QuotientGroup.mk_mul_of_mem g hyA
            rw [this]
            exact hgR
          · have h1 : ((g * y : D) : D ⧸ B) = (g : D ⧸ B) := QuotientGroup.mk_mul_of_mem g hyB
            refine hgR.trans ?_
            refine (SimpleGraph.Adj.reachable (goldCosetGraph_adj_base A B g)).trans ?_
            have := (goldCosetGraph_adj_base A B (g * y)).reachable.symm
            rw [h1] at this
            exact this
        refine ⟨step x hx g hgR, step x⁻¹ ?_ g hgR⟩
        rcases hx with hxA | hxB
        · exact Or.inl (inv_mem hxA)
        · exact Or.inr (inv_mem hxB)
      | one =>
        intro g hgR
        simp only [mul_one, inv_one]
        exact ⟨hgR, hgR⟩
      | mul x y hx hy ihx ihy =>
        intro g hgR
        obtain ⟨h1, _⟩ := ihx g hgR
        obtain ⟨h3, _⟩ := ihy (g * x) h1
        obtain ⟨_, h6⟩ := ihy g hgR
        obtain ⟨_, h8⟩ := ihx (g * y⁻¹) h6
        refine ⟨by simpa [mul_assoc] using h3, ?_⟩
        simpa [mul_assoc] using h8
      | inv x hx ihx =>
        intro g hgR
        obtain ⟨h1, h2⟩ := ihx g hgR
        exact ⟨by simpa using h2, by simpa using h1⟩
    have := (key g hg 1 (SimpleGraph.Reachable.refl _)).1
    simpa using this
  have hall : ∀ v, (goldCosetGraph A B).Reachable (.inl ((1 : D) : D ⧸ A)) v := by
    rintro (q | q)
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact hbase g
    · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact (hbase g).trans (goldCosetGraph_adj_base A B g).reachable
  have : Nonempty ((D ⧸ A) ⊕ (D ⧸ B)) := ⟨.inl ((1 : D) : D ⧸ A)⟩
  exact ⟨fun v w => (hall v).symm.trans (hall w)⟩

theorem goldCosetGraph_neighborSet_inl (A B : Subgroup D) (g : D) :
    (goldCosetGraph A B).neighborSet (.inl (g : D ⧸ A)) =
      Set.range (fun a : A => (Sum.inr ((g * a : D) : D ⧸ B) : (D ⧸ A) ⊕ (D ⧸ B))) := by
  ext v
  rw [SimpleGraph.mem_neighborSet]
  rcases v with q | y
  · simp [goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel]
  · rw [goldCosetGraph_adj_inl_inr]
    constructor
    · rintro ⟨g', hg', rfl⟩
      have : g⁻¹ * g' ∈ A := by
        rw [← QuotientGroup.eq]
        exact hg'.symm
      exact ⟨⟨g⁻¹ * g', this⟩, by simp⟩
    · rintro ⟨a, ha⟩
      have hy : ((g * a : D) : D ⧸ B) = y := Sum.inr_injective ha
      exact ⟨g * a, QuotientGroup.mk_mul_of_mem g a.2, hy⟩

theorem goldCosetGraph_ncard_neighborSet_inl (A B : Subgroup D) (g : D) :
    ((goldCosetGraph A B).neighborSet (.inl (g : D ⧸ A))).ncard = B.relIndex A := by
  rw [goldCosetGraph_neighborSet_inl]
  let F : A ⧸ B.subgroupOf A → (D ⧸ A) ⊕ (D ⧸ B) :=
    Quotient.lift (fun a : A => (Sum.inr ((g * a : D) : D ⧸ B) : (D ⧸ A) ⊕ (D ⧸ B))) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ B.subgroupOf A := QuotientGroup.leftRel_apply.mp hab
      have : ((g * a : D) : D ⧸ B) = ((g * b : D) : D ⧸ B) := by
        rw [QuotientGroup.eq]
        have h1 : ((a : D)⁻¹ * (b : D)) ∈ B := hab'
        simpa [mul_assoc] using h1
      exact congrArg Sum.inr this)
  have hFinj : Function.Injective F := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
      induction q using Quotient.inductionOn with
      | h b =>
        have h1 : ((g * a : D) : D ⧸ B) = ((g * b : D) : D ⧸ B) := Sum.inr_injective hpq
        rw [QuotientGroup.eq] at h1
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        show ((a : D)⁻¹ * (b : D)) ∈ B
        simpa [mul_assoc] using h1
  have hrange : Set.range (fun a : A => (Sum.inr ((g * a : D) : D ⧸ B) : (D ⧸ A) ⊕ (D ⧸ B))) =
      Set.range F := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Quotient.mk _ a, rfl⟩
    · rintro ⟨p, rfl⟩
      induction p using Quotient.inductionOn with
      | h a => exact ⟨a, rfl⟩
  rw [hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hFinj]
  rfl

theorem goldCosetGraph_neighborSet_inr (A B : Subgroup D) (g : D) :
    (goldCosetGraph A B).neighborSet (.inr (g : D ⧸ B)) =
      Set.range (fun b : B => (Sum.inl ((g * b : D) : D ⧸ A) : (D ⧸ A) ⊕ (D ⧸ B))) := by
  ext v
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.adj_comm]
  rcases v with x | q
  · rw [goldCosetGraph_adj_inl_inr]
    constructor
    · rintro ⟨g', rfl, hg'⟩
      have : g⁻¹ * g' ∈ B := by
        rw [← QuotientGroup.eq]
        exact hg'.symm
      exact ⟨⟨g⁻¹ * g', this⟩, by simp⟩
    · rintro ⟨b, hb⟩
      have hx : ((g * b : D) : D ⧸ A) = x := Sum.inl_injective hb
      exact ⟨g * b, hx, QuotientGroup.mk_mul_of_mem g b.2⟩
  · simp [goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel]

theorem goldCosetGraph_ncard_neighborSet_inr (A B : Subgroup D) (g : D) :
    ((goldCosetGraph A B).neighborSet (.inr (g : D ⧸ B))).ncard = A.relIndex B := by
  rw [goldCosetGraph_neighborSet_inr]
  let F : B ⧸ A.subgroupOf B → (D ⧸ A) ⊕ (D ⧸ B) :=
    Quotient.lift (fun b : B => (Sum.inl ((g * b : D) : D ⧸ A) : (D ⧸ A) ⊕ (D ⧸ B))) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ A.subgroupOf B := QuotientGroup.leftRel_apply.mp hab
      have : ((g * a : D) : D ⧸ A) = ((g * b : D) : D ⧸ A) := by
        rw [QuotientGroup.eq]
        have h1 : ((a : D)⁻¹ * (b : D)) ∈ A := hab'
        simpa [mul_assoc] using h1
      exact congrArg Sum.inl this)
  have hFinj : Function.Injective F := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | h a =>
      induction q using Quotient.inductionOn with
      | h b =>
        have h1 : ((g * a : D) : D ⧸ A) = ((g * b : D) : D ⧸ A) := Sum.inl_injective hpq
        rw [QuotientGroup.eq] at h1
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        show ((a : D)⁻¹ * (b : D)) ∈ A
        simpa [mul_assoc] using h1
  have hrange : Set.range (fun b : B => (Sum.inl ((g * b : D) : D ⧸ A) : (D ⧸ A) ⊕ (D ⧸ B))) =
      Set.range F := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Quotient.mk _ a, rfl⟩
    · rintro ⟨p, rfl⟩
      induction p using Quotient.inductionOn with
      | h a => exact ⟨a, rfl⟩
  rw [hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hFinj]
  rfl

end CosetGraph

namespace GoldAmalgam

variable {A C B : Type*} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}
  {D : Type*} [Group D] (Φ : GoldCompletion X D)

namespace GoldCompletion

abbrev cosetGraph : SimpleGraph ((D ⧸ Φ.ψA.range) ⊕ (D ⧸ Φ.ψB.range)) :=
  goldCosetGraph Φ.ψA.range Φ.ψB.range

theorem cosetGraph_connected : Φ.cosetGraph.Connected :=
  goldCosetGraph_connected _ _ Φ.gen

end GoldCompletion

end GoldAmalgam

end CFSG.Quasithin

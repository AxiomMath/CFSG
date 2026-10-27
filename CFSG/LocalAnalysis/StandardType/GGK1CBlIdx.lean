module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal SpPrimaryBlocks spSupported
  symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

theorem ggK1CBl_map_getD_range {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun k => l.getD k d) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      rw [show ((fun k => (a :: t).getD k d) ∘ Nat.succ) = fun k => t.getD k d from by
        funext k; exact List.getD_cons_succ]
      rw [List.getD_cons_zero, ih]

theorem ggK1CBl_map_filter_eq {α β : Type*} (l : List α) (g : α → β)
    (q : β → Bool) :
    (l.map g).filter q = (l.filter (fun a => q (g a))).map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.filter_cons, ih]
      split <;> rfl

theorem ggK1CBl_filter_map_getD {α β : Type*} (l : List α) (d : α)
    (p : α → Bool) (f : α → β) :
    (l.filter p).map f =
      ((List.range l.length).filter (fun k => p (l.getD k d))).map (fun k => f (l.getD k d)) := by
  conv_lhs => rw [← ggK1CBl_map_getD_range l d]
  rw [ggK1CBl_map_filter_eq (List.range l.length) (fun k => l.getD k d) p, List.map_map]
  rfl

theorem ggK1CBl_tail_filter_map {α : Type*} (l : List ℕ) (f : ℕ → α) :
    ((List.range l.length).filter (fun j => decide (1 ≤ j ∧ 1 ≤ l.getD j 0))).map
        (fun j => f (l.getD j 0))
      = (l.drop 1 |>.filter (fun x => decide (x ≠ 0))).map f := by
  cases l with
  | nil => rfl
  | cons a t =>
      rw [show (a :: t).drop 1 = t from rfl]
      conv_rhs => rw [ggK1CBl_filter_map_getD t 0 (fun x => decide (x ≠ 0)) f]
      rw [List.length_cons, List.range_succ_eq_map, List.filter_cons]
      have hq0 : ¬ ((fun j => decide (1 ≤ j ∧ 1 ≤ (a :: t).getD j 0)) 0 = true) := by simp
      rw [if_neg hq0]
      rw [ggK1CBl_map_filter_eq (List.range t.length) Nat.succ
            (fun j => decide (1 ≤ j ∧ 1 ≤ (a :: t).getD j 0)), List.map_map]
      congr 1
      · apply List.filter_congr
        intro k _
        simp [Function.comp_apply, List.getD_cons_succ, Nat.one_le_iff_ne_zero]

theorem ggK1CBl_univ_map_subtype_val {α β : Type*} (s : Finset α) (g : α → β) :
    (Finset.univ : Finset ↥s).val.map (fun x => g x.val) = s.val.map g := by
  rw [Finset.univ_eq_attach, Finset.attach_val]
  rw [show (fun x : ↥s => g x.val) = g ∘ (Subtype.val : ↥s → α) from rfl, ← Multiset.map_map]
  congr 1
  exact congrArg Finset.val (Finset.attach_map_val (s := s))

@[expose] abbrev ggK1CBl_Id1 (K : Type) [Field K] (P : Finset K[X]) (m : List ℕ) : Type :=
  ↥P ⊕ Subtype (fun _ : Unit => m.headD 0 ≠ 0)

@[expose] abbrev ggK1CBl_Id2 (K : Type) [Field K] {r : ℕ} (x : ↥(StatedSp r K))
    (m : List ℕ) : Type :=
  ↥(ggK1CSelfDualFactors x) ⊕ Subtype (fun _ : Unit => m.headD 0 ≠ 0)

@[expose] noncomputable def ggK1CBl_A1 {r : ℕ} {K : Type} [Field K]
    (x : ↥(StatedSp r K)) (P : Finset K[X]) (m : List ℕ) :
    ggK1CBl_Id1 K P m → Subgroup (StatedSp r K)
  | Sum.inl h => spSupported x ({h.1, reciprocalPolynomial h.1} : Set K[X])
  | Sum.inr _ => spSupported x ({X - 1} : Set K[X])

@[expose] noncomputable def ggK1CBl_kind1 {r : ℕ} {K : Type} [Field K]
    (d : ℕ) (x : ↥(StatedSp r K)) (P : Finset K[X]) (m : List ℕ) :
    ggK1CBl_Id1 K P m → ggK1CCo_Kind
  | Sum.inl h => if d = 1 then ggK1CCo_Kind.sl (primaryMultiplicity (spEnd x) h.1)
      else ggK1CCo_Kind.su (primaryMultiplicity (spEnd x) h.1)
  | Sum.inr _ => ggK1CCo_Kind.sp (m.headD 0)

@[expose] noncomputable def ggK1CBl_A2 {r : ℕ} {K : Type} [Field K]
    (x : ↥(StatedSp r K)) (m : List ℕ) :
    ggK1CBl_Id2 K x m → Subgroup (StatedSp r K)
  | Sum.inl h => spSupported x ({h.1} : Set K[X])
  | Sum.inr _ => spSupported x ({X - 1} : Set K[X])

@[expose] noncomputable def ggK1CBl_kind2 {r : ℕ} {K : Type} [Field K]
    (x : ↥(StatedSp r K)) (m : List ℕ) :
    ggK1CBl_Id2 K x m → ggK1CCo_Kind
  | Sum.inl h => ggK1CCo_Kind.su (primaryMultiplicity (spEnd x) h.1)
  | Sum.inr _ => ggK1CCo_Kind.sp (m.headD 0)

end CFSG.StandardType

end

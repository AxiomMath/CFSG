module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Count

variable {G ι : Type*} [Group G] [Finite G]

theorem card_eq_mul_card_of_conj_tuples (N : Subgroup G) (a : ι → G) (T : Finset (ι → G))
    (hT : ∀ n ∈ N, (fun i => n * a i * n⁻¹) ∈ T) {m : ℕ} (hm : T.card = m) (w : Fin m → G)
    (hw : ∀ k, w k ∈ N) (hinj : Function.Injective fun k => fun i => w k * a i * (w k)⁻¹) :
    Nat.card ↥N = m * Nat.card ↥(N ⊓ centralizer (Set.range a)) := by
  set C : Subgroup G := N ⊓ centralizer (Set.range a) with hC
  have hCN : C ≤ N := inf_le_left
  set C' : Subgroup ↥N := C.subgroupOf N with hC'
  have hmemC : ∀ n : ↥N, n ∈ C' ↔ ∀ i, (n : G) * a i = a i * (n : G) := by
    intro n
    rw [hC', mem_subgroupOf, hC, mem_inf, mem_centralizer_iff]
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ⟨fun h => fun i => (h.2 i).symm, fun h => ⟨n.2, fun i => (h i).symm⟩⟩
  let F : ↥N ⧸ C' → (ι → G) :=
    Quotient.lift (fun n : ↥N => fun i => (n : G) * a i * (n : G)⁻¹) (by
      intro n n' h
      have h' : n⁻¹ * n' ∈ C' := by
        have := QuotientGroup.leftRel_apply.1 h
        exact this
      have hc := (hmemC _).1 h'
      funext i
      have hc' : (n : G)⁻¹ * (n' : G) * a i = a i * ((n : G)⁻¹ * (n' : G)) := by
        simpa using hc i
      calc (n : G) * a i * (n : G)⁻¹
          = (n : G) * (a i * ((n : G)⁻¹ * (n' : G))) * (n' : G)⁻¹ := by group
        _ = (n : G) * ((n : G)⁻¹ * (n' : G) * a i) * (n' : G)⁻¹ := by rw [hc']
        _ = (n' : G) * a i * (n' : G)⁻¹ := by group)
  have hFinj : Function.Injective F := by
    intro q q' h
    induction q using QuotientGroup.induction_on with
    | H n =>
      induction q' using QuotientGroup.induction_on with
      | H n' =>
        apply QuotientGroup.eq.2
        rw [hmemC]
        intro i
        have hi := congrFun h i
        simp only [F] at hi
        change (n : G) * a i * (n : G)⁻¹ = (n' : G) * a i * (n' : G)⁻¹ at hi
        have : (n : G)⁻¹ * (n' : G) * a i = a i * ((n : G)⁻¹ * (n' : G)) := by
          calc (n : G)⁻¹ * (n' : G) * a i
              = (n : G)⁻¹ * ((n' : G) * a i * (n' : G)⁻¹) * (n' : G) := by group
            _ = (n : G)⁻¹ * ((n : G) * a i * (n : G)⁻¹) * (n' : G) := by rw [hi]
            _ = a i * ((n : G)⁻¹ * (n' : G)) := by group
        simpa using this
  have hindex : Nat.card (↥N ⧸ C') = m := by
    subst hm
    apply le_antisymm
    ·
      let g : (↥N ⧸ C') → T := fun q => ⟨F q, by
        induction q using QuotientGroup.induction_on with
        | H n => exact hT n n.2⟩
      have hg : Function.Injective g := fun q q' h => hFinj (congrArg Subtype.val h)
      have := Nat.card_le_card_of_injective g hg
      simpa using this
    ·
      let g : Fin T.card → (↥N ⧸ C') := fun k => (QuotientGroup.mk ⟨w k, hw k⟩ : ↥N ⧸ C')
      have hg : Function.Injective g := by
        intro k l h
        apply hinj
        have := congrArg F h
        exact this
      have := Nat.card_le_card_of_injective g hg
      simpa using this
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  rw [hindex, hC', Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at h1
  exact h1

end Count

end CFSG.Sporadic.Recognition.LyonsSims

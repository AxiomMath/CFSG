module

public import CFSG.Foundations.MaxOrderThompsonDefs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PGroups

open Subgroup

variable {S : Type*} [Group S] [Finite S]

theorem card_le_maxAbelianOrder {A : Subgroup S} (hA : IsMulCommutative A) :
    Nat.card A ≤ maxAbelianOrder S :=
  le_csSup ⟨Nat.card S, fun _ ⟨B, _, hB⟩ => hB ▸ Subgroup.card_le_card_group B⟩ ⟨A, hA, rfl⟩

theorem exists_mem_maxOrderAbelianFamily : ∃ A, A ∈ maxOrderAbelianFamily S := by
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem (s := {n : ℕ | ∃ A : Subgroup S, IsMulCommutative A ∧
      Nat.card A = n}) ⟨1, ⊥, inferInstance, by rw [card_bot]⟩
    ⟨Nat.card S, fun _ ⟨B, _, hB⟩ => hB ▸ Subgroup.card_le_card_group B⟩
  exact ⟨A, hA, hcard⟩

omit [Finite S] in
theorem isMulCommutative_sup_zpowers {A : Subgroup S} (hA : IsMulCommutative A) {x : S}
    (hx : x ∈ centralizer (A : Set S)) : IsMulCommutative (A ⊔ zpowers x : Subgroup S) := by
  have hAA : A ≤ centralizer (A : Set S) := le_centralizer_iff_isMulCommutative.2 hA
  have hZA : zpowers x ≤ centralizer (A : Set S) := zpowers_le.2 hx
  have hZZ : zpowers x ≤ centralizer (zpowers x : Set S) :=
    le_centralizer_iff_isMulCommutative.2 inferInstance
  have hAZ : A ≤ centralizer (zpowers x : Set S) := le_centralizer_iff.2 hZA
  refine le_centralizer_iff_isMulCommutative.1 (sup_le ?_ ?_)
  · exact le_centralizer_iff.2 (sup_le hAA hZA)
  · exact le_centralizer_iff.2 (sup_le hAZ hZZ)

theorem zj_center_intersection : orderZJ S = sInf (maxOrderAbelianFamily S) := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_sInf]
    intro A hA
    have hAJ : A ≤ orderThompson S := le_sSup hA
    have hxA : (z : S) ∈ centralizer (A : Set S) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h := mem_center_iff.1 hz ⟨a, hAJ ha⟩
      exact congrArg Subtype.val h
    have hB := isMulCommutative_sup_zpowers hA.1 hxA
    have hle : A ≤ A ⊔ zpowers (z : S) := le_sup_left
    have hEq : A = A ⊔ zpowers (z : S) := by
      refine eq_of_le_of_card_ge hle ?_
      rw [hA.2]
      exact card_le_maxAbelianOrder hB
    rw [hEq]
    exact mem_sup_right (mem_zpowers _)
  · intro x hx
    rw [mem_sInf] at hx
    obtain ⟨A₀, hA₀⟩ := exists_mem_maxOrderAbelianFamily (S := S)
    have hxJ : x ∈ orderThompson S := (le_sSup hA₀ : A₀ ≤ orderThompson S) (hx A₀ hA₀)
    have hJ : orderThompson S ≤ centralizer (zpowers x : Set S) := by
      refine sSup_le fun A hA => le_centralizer_iff.2 (zpowers_le.2 ?_)
      exact le_centralizer_iff_isMulCommutative.2 hA.1 (hx A hA)
    refine ⟨⟨x, hxJ⟩, mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.1 (hJ g.2) x (mem_zpowers x)).symm

end CFSG.RankThree.PGroups

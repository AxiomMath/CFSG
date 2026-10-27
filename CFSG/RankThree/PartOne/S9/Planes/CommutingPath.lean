module

import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.Planes.Transfer
import CFSG.RankThree.PartOne.S9.Planes.NormalPlane
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.Planes

open Subgroup

variable {G : Type*} [Group G]

theorem isElementaryAbelian_inf_centralizer_sup {p : ℕ} {A V : Subgroup G}
    (hA : IsElementaryAbelian p A) (hV : IsElementaryAbelian p V) :
    IsElementaryAbelian p ↥((A ⊓ centralizer (V : Set G)) ⊔ V) := by
  have := hV
  have : IsElementaryAbelian p ↥(A ⊓ centralizer (V : Set G)) :=
    isElementaryAbelian_of_le inf_le_left hA
  rw [sup_comm]
  exact IsElementaryAbelian.sup_of_le_centralizer (E := V) (C := A ⊓ centralizer (V : Set G))
    inf_le_right

theorem le_centralizer_of_isElementaryAbelian {p : ℕ} {V : Subgroup G}
    (hV : IsElementaryAbelian p V) : V ≤ centralizer (V : Set G) := fun x hx =>
  mem_centralizer_iff.2 fun h hh => ((isElementaryAbelian_iff p V).1 hV).1 h hh x hx

end CFSG.RankThree.PartOne.Planes

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped commutatorElement

theorem oddPLargeElementaryCommutingPath :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      IsPGroup p P → 3 ≤ CFSG.Assembly.pRank p P → ∀ E F : Subgroup G, E ≤ P → F ≤ P →
      IsElementaryAbelian p E → IsElementaryAbelian p F → p ^ 2 ≤ Nat.card E →
      p ^ 2 ≤ Nat.card F → 3 ≤ CFSG.Assembly.pRank p (P ⊓ Subgroup.centralizer (E : Set G)) →
      3 ≤ CFSG.Assembly.pRank p (P ⊓ Subgroup.centralizer (F : Set G)) →
      ∃ n : ℕ, n ≤ 4 ∧ ∃ X : ℕ → Subgroup G, X 0 = E ∧ X n = F ∧
        (∀ i, i ≤ n → X i ≤ P ∧ IsElementaryAbelian p (X i) ∧ p ^ 2 ≤ Nat.card (X i) ∧
          3 ≤ CFSG.Assembly.pRank p (P ⊓ Subgroup.centralizer (X i : Set G))) ∧
        ∀ i, i < n → ⁅X i, X (i + 1)⁆ = ⊥ := by
  intro G _ _ p hp hp2 P hP hrk E F hEP hFP hE hF hEc hFc hCE hCF
  have hpF : Fact p.Prime := ⟨hp⟩
  have hp23 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
  obtain ⟨A₀, hA₀P, hA₀, hA₀c⟩ := (Planes.le_pRank_iff hp P 3).1 hrk
  have hnc : ¬ IsCyclic P :=
    Planes.not_isCyclic_of_isElementaryAbelian hp hA₀P hA₀ (by rw [hA₀c]; exact hp23)
  obtain ⟨U, V, -, hVP, -, -, hV, hVc, hVn, -⟩ :=
    pgOddNoncyclicSecondCenterNormalPlane G p hp hp2 P hP hnc
  have hVC : V ≤ centralizer (V : Set G) := Planes.le_centralizer_of_isElementaryAbelian hV
  have hrkV : 3 ≤ CFSG.Assembly.pRank p (P ⊓ centralizer (V : Set G)) := by
    obtain ⟨-, hU⟩ := Planes.normalPlane_concrete hp hP hVP hVn hV hVc hA₀P hA₀ hA₀c
    refine Planes.le_pRank_of_le_card hp ?_
      (Planes.isElementaryAbelian_inf_centralizer_sup hA₀ hV) hU
    exact sup_le (inf_le_inf_right _ hA₀P) (le_inf hVP hVC)
  have key : ∀ Y : Subgroup G, 3 ≤ CFSG.Assembly.pRank p (P ⊓ centralizer (Y : Set G)) →
      ∃ B : Subgroup G, B ≤ P ∧ IsElementaryAbelian p B ∧ p ^ 2 ≤ Nat.card B ∧ ⁅Y, B⁆ = ⊥ ∧
        ⁅B, V⁆ = ⊥ ∧ 3 ≤ CFSG.Assembly.pRank p (P ⊓ centralizer (B : Set G)) := by
    intro Y hY
    obtain ⟨A, hAle, hAe, hAc⟩ := (Planes.le_pRank_iff hp _ 3).1 hY
    have hAP : A ≤ P := hAle.trans inf_le_left
    obtain ⟨hB, -⟩ := Planes.normalPlane_concrete hp hP hVP hVn hV hVc hAP hAe hAc
    have hAcomm := ((Planes.isElementaryAbelian_iff p A).1 hAe).1
    refine ⟨A ⊓ centralizer (V : Set G), inf_le_left.trans hAP,
      Planes.isElementaryAbelian_of_le inf_le_left hAe, hB, ?_, ?_, ?_⟩
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
      exact inf_le_left.trans (hAle.trans inf_le_right)
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact inf_le_right
    · refine (Planes.le_pRank_iff hp _ 3).2 ⟨A, le_inf hAP ?_, hAe, hAc⟩
      exact fun x hx => mem_centralizer_iff.2 fun h hh => hAcomm h hh.1 x hx
  obtain ⟨BE, hBEP, hBE, hBEc, hEBE, hBEV, hBEr⟩ := key E hCE
  obtain ⟨BF, hBFP, hBF, hBFc, hFBF, hBFV, hBFr⟩ := key F hCF
  refine ⟨4, le_rfl, fun i => match i with | 0 => E | 1 => BE | 2 => V | 3 => BF | _ => F, rfl,
    rfl, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact ⟨hEP, hE, hEc, hCE⟩
    · exact ⟨hBEP, hBE, hBEc, hBEr⟩
    · exact ⟨hVP, hV, hVc.ge, hrkV⟩
    · exact ⟨hBFP, hBF, hBFc, hBFr⟩
    · exact ⟨hFP, hF, hFc, hCF⟩
  · intro i hi
    interval_cases i
    · exact hEBE
    · exact hBEV
    · rw [Subgroup.commutator_comm]
      exact hBFV
    · rw [Subgroup.commutator_comm]
      exact hFBF

end CFSG.RankThree.PartOne

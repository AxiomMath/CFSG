module

import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.Planes.Transfer
import CFSG.RankThree.PartOne.S9.Planes.NormalPlane
import CFSG.RankThree.PartOne.S9.Planes.CommutingPath
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup

theorem productRankNormalPlaneWitness :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ P U : Subgroup G,
      IsPGroup p P → U ≤ P → 2 ≤ CFSG.Assembly.pRank p U →
      3 ≤ CFSG.Assembly.pRank p (U ⊔ (P ⊓ Subgroup.centralizer (U : Set G))) →
      ∃ E : Subgroup G, E ≤ U ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 ∧
        U ≤ Subgroup.normalizer (E : Set G) ∧
        ∀ g ∈ Subgroup.normalizer (U : Set G), conjugate E g ≤ U ∧
          U ⊔ (P ⊓ Subgroup.centralizer (U : Set G)) ≤
            Subgroup.normalizer (conjugate E g : Set G) ∧
          3 ≤ CFSG.Assembly.pRank p (P ⊓ Subgroup.centralizer (conjugate E g : Set G)) ∧
          ∃ A : Subgroup G, IsElementaryAbelian p A ∧ Nat.card A = p ^ 3 ∧ conjugate E g ≤ A ∧
            A ≤ (U ⊔ (P ⊓ Subgroup.centralizer (U : Set G))) ⊓
              Subgroup.centralizer (conjugate E g : Set G) := by
  intro G _ _ p hp hp2 P U hP hUP hU2 hQ3
  have hpF : Fact p.Prime := ⟨hp⟩
  have hQP : U ⊔ (P ⊓ centralizer (U : Set G)) ≤ P := sup_le hUP inf_le_left
  have hUle : U ≤ U ⊔ (P ⊓ centralizer (U : Set G)) := le_sup_left
  obtain ⟨E₂, hE₂U, hE₂, hE₂c⟩ := (Planes.le_pRank_iff hp U 2).1 hU2
  have hUnc : ¬ IsCyclic U :=
    Planes.not_isCyclic_of_isElementaryAbelian hp hE₂U hE₂ (by rw [hE₂c])
  obtain ⟨-, E, -, hEU, -, -, hE, hEc, hEn, -⟩ :=
    pgOddNoncyclicSecondCenterNormalPlane G p hp hp2 U (hP.to_le hUP) hUnc
  obtain ⟨A₀, hA₀Q, hA₀, hA₀c⟩ := (Planes.le_pRank_iff hp _ 3).1 hQ3
  refine ⟨E, hEU, hE, hEc, hEn, fun g hg => ?_⟩
  have hEgU : conjugate E g ≤ U := Planes.conjugate_le_of_mem_normalizer hEU hg
  have hEg : IsElementaryAbelian p (conjugate E g) := Planes.isElementaryAbelian_conjugate hp hE g
  have hEgc : Nat.card (conjugate E g) = p ^ 2 := by rw [Planes.card_conjugate, hEc]
  have hUn : U ≤ normalizer (conjugate E g : Set G) := by
    intro u hu
    rw [mem_normalizer_iff]
    intro x
    rw [Planes.mem_conjugate_iff, Planes.mem_conjugate_iff]
    have hu' : g * u * g⁻¹ ∈ U := (mem_normalizer_iff.1 hg u).1 hu
    rw [mem_normalizer_iff.1 (hEn hu') (g * x * g⁻¹)]
    have : g * u * g⁻¹ * (g * x * g⁻¹) * (g * u * g⁻¹)⁻¹ = g * (u * x * u⁻¹) * g⁻¹ := by group
    rw [this]
  have hCn : P ⊓ centralizer (U : Set G) ≤ normalizer (conjugate E g : Set G) := fun c hc =>
    centralizer_le_normalizer (conjugate E g : Set G)
      (mem_centralizer_iff.2 fun x hx => mem_centralizer_iff.1 hc.2 x (hEgU hx))
  have hQn : U ⊔ (P ⊓ centralizer (U : Set G)) ≤ normalizer (conjugate E g : Set G) :=
    sup_le hUn hCn
  obtain ⟨-, hW3⟩ := Planes.normalPlane_concrete hp (hP.to_le hQP) (hEgU.trans hUle) hQn hEg hEgc
    hA₀Q hA₀ hA₀c
  have hWe := Planes.isElementaryAbelian_inf_centralizer_sup hA₀ hEg
  have hWle : (A₀ ⊓ centralizer (conjugate E g : Set G)) ⊔ conjugate E g ≤
      (U ⊔ (P ⊓ centralizer (U : Set G))) ⊓ centralizer (conjugate E g : Set G) :=
    sup_le (inf_le_inf_right _ hA₀Q)
      (le_inf (hEgU.trans hUle) (Planes.le_centralizer_of_isElementaryAbelian hEg))
  obtain ⟨K, hKc, hEK, hKW⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 3)
    (H := conjugate E g) (L := (A₀ ⊓ centralizer (conjugate E g : Set G)) ⊔ conjugate E g)
    (by rw [hEgc]; exact pow_dvd_pow p (by norm_num)) (Planes.pow_dvd_card_of_le_card hp hWe hW3)
    le_sup_right
  have hKC : K ≤ (U ⊔ (P ⊓ centralizer (U : Set G))) ⊓ centralizer (conjugate E g : Set G) :=
    hKW.trans hWle
  refine ⟨hEgU, hQn, ?_, K, Planes.isElementaryAbelian_of_le hKW hWe, hKc, hEK, hKC⟩
  exact (Planes.le_pRank_iff hp _ 3).2 ⟨K, hKC.trans (inf_le_inf_right _ hQP),
    Planes.isElementaryAbelian_of_le hKW hWe, hKc⟩

end CFSG.RankThree.PartOne

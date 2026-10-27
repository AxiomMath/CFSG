module

public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoStatement
public import CFSG.OddTranspositions.HypothesisC
public import Certificates.Certificate43
public import Certificates.Certificate113

import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoBlocks
import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoWreath
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.GroupTheory.PCore.SolvableRadical
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_thirdKind_of_uQ_subset
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {w v : G} (htri : IsTriangle D hC.d w v) (hv : v ∈ DalphaStar D hC.alpha)
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) (hord : orderOf (hC.d * v * w) = 2 * n)
    {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * hC.d * k⁻¹ = x)
    (hQ : ¬ CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hα : ∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * hC.d * (q : G)⁻¹ ∈ hC.alpha) :
    ∃ q ∈ CFSG.pCore 2 (localGroup D z), ∃ c : G,
      IsTriangle D hC.d c ((q : G) * hC.d * (q : G)⁻¹) ∧
        IsThirdKind hC.d c ((q : G) * hC.d * (q : G)⁻¹) := by
  classical
  have hS := hC.setup
  have hD := hS.oddT
  have hN := hS.normal
  have hblock := hC.isBlock_alpha
  have huα := hC.d_mem_alpha
  obtain ⟨huC, -, -, -⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at huC
  obtain ⟨q, hq, hqu⟩ := exists_pCore_conj_ne_of_not_le_center htrans hQ
  refine ⟨q, hq, ?_⟩
  set a : G := (q : G) * hC.d * (q : G)⁻¹ with ha_def
  have haα : a ∈ hC.alpha := hα q hq
  have hua : Commute hC.d a := (commute_conj_pCore hS huC hq).symm
  have hne : hC.d ≠ a := Ne.symm hqu
  have hF : FaithfulOnBlocks hC.alpha :=
    faithfulOnBlocks_of_thirdKind_of_mem_alpha hC hrad huα htri ⟨n, hn, hn1, hord⟩ hv haα hqu
  have hua1 : hC.d * a ≠ 1 := by
    intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_right h, hD.inv_eq hC.hd]
  obtain ⟨γ, hγ, hγmove⟩ : ∃ γ ∈ blockClass hC.alpha,
      (fun y => hC.d * a * y * (hC.d * a)⁻¹) '' γ ≠ γ := by
    by_contra hcon
    push Not at hcon
    exact hua1 (hF _ hcon)
  have hγA : γ ∈ Aalpha D hC.alpha := by
    refine ⟨hγ, fun hγp => hγmove ?_⟩
    rcases mem_perp_iff.mp hγp with hγD | rfl
    · have hfix : ∀ x ∈ γ, hC.d * a * x * (hC.d * a)⁻¹ = x := by
        intro x hx
        rw [((hγD.2.2.2 _ huα x hx).mul_left (hγD.2.2.2 a haα x hx)).eq]
        group
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change hC.d * a * x * (hC.d * a)⁻¹ ∈ γ
        rw [hfix x hx]
        exact hx
      · exact fun hy => ⟨y, hy, hfix y hy⟩
    · exact Subgroup.mem_normalizer_iff_conj_image_eq.mp (Subgroup.mul_mem _
        (mem_normalizer_of_mem_alpha hblock huα) (mem_normalizer_of_mem_alpha hblock haα))
  obtain ⟨b, hb⟩ := blockClass_nonempty hblock.nonempty hγ
  have htri' : IsTriangle D hC.d b a :=
    isTriangle_of_mem_Aalpha hD hN hblock hγA huα haα hua hne hb
  rcases htri'.orderOf_cases hD hN with ⟨hodd, -⟩ | h4 | hthird
  ·
    exfalso
    have huaD : hC.d * a ∈ D := htri'.mul_mem_of_odd hD hN hodd
    have hmem : a * hC.d⁻¹ ∈ (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype :=
      conj_mul_inv_mem_pCore (mem_localGroup_of_mem huC) hq rfl
    rw [hD.inv_eq hC.hd, ← hua.eq] at hmem
    obtain ⟨x, hxQ, hxeq⟩ := Subgroup.mem_map.mp hmem
    have huaC : hC.d * a ∈ centSet D z := by
      refine ⟨huaD, ?_⟩
      rw [← hxeq]
      exact commute_of_mem_localGroup x.2
    refine centSet_not_mem_solvableRadical hS htri hn hn1 hord hzdef htrans huaC ?_
    have hx : x = ⟨hC.d * a, mem_localGroup_of_mem huaC⟩ := Subtype.ext hxeq
    rw [← hx]
    exact CFSG.pCore_le_solvableRadical 2 (localGroup D z) hxQ
  ·
    by_cases hno : ∀ x ∈ D, x ∈ Subgroup.closure {hC.d, b} → IsTriangle D hC.d x a →
        ¬ IsThirdKind hC.d x a
    · exfalso
      have hy := conj_mul_mem_of_mem_Aalpha hC hγA huα haα hua hne hb h4 hno
      exact hγmove (eq_of_mem_of_mem_blockClass hblock (conj_image_mem_blockClass hγ _) hγ
        ⟨_, ⟨b, hb, rfl⟩, hy⟩)
    · push Not at hno
      obtain ⟨x, -, -, htrix, hthirdx⟩ := hno
      exact ⟨x, htrix, hthirdx⟩
  · exact ⟨b, htri', hthird⟩

end CFSG.OddTranspositions.PartThree

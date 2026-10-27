module

public import CFSG.OddTranspositions.PartThree.EightEight.Shapes
public import CFSG.OddTranspositions.SixNineUnconditional

import CFSG.OddTranspositions.PartThree.AlmostSimpleTransport
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
import CFSG.OddTranspositions.PartThree.HalphaConj

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def starSigma (D : Set G) (x w y : G) (n : ℕ) : Set G :=
  {r | r ∈ centSet D ((x * y * w) ^ n) ∧ r ∉ conjOrbit (localGroup D ((x * y * w) ^ n)) x}

@[expose] def starN (D β Sig : Set G) : Set G :=
  Sig ∩ DalphaStar D β

@[expose] def StarZbarMem (hC : HypothesisC D) (z : G) : Prop :=
  ∃ d ∈ DalphaStar D hC.alpha, ∃ m ∈ (CFSG.solvableRadical (Halpha D hC.alpha)).map
    (Halpha D hC.alpha).subtype, z = d * m

theorem starZbarMem_iff (hC : HypothesisC D) {z : G} (hz : z ∈ Halpha D hC.alpha) :
    StarZbarMem hC z ↔
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨z, hz⟩ ∈ imageClass hC := by
  constructor
  · rintro ⟨d, hdD, m, hmM, rfl⟩
    have hdH : d ∈ Halpha D hC.alpha := Subgroup.subset_closure hdD
    have hmH : m ∈ Halpha D hC.alpha :=
      Subgroup.map_subtype_le (CFSG.solvableRadical (Halpha D hC.alpha)) hmM
    have hmM' : (⟨m, hmH⟩ : Halpha D hC.alpha) ∈
        CFSG.solvableRadical (Halpha D hC.alpha) := by
      obtain ⟨m₀, hm₀, hm₀eq⟩ := Subgroup.mem_map.mp hmM
      have heq : (⟨m, hmH⟩ : Halpha D hC.alpha) = m₀ := Subtype.ext hm₀eq.symm
      rwa [← heq] at hm₀
    have hmq :
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨m, hmH⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨m, hmH⟩ : Halpha D hC.alpha)).mpr hmM'
    refine ⟨⟨d, hdH⟩, hdD, ?_⟩
    have hprod : (⟨d * m, hz⟩ : Halpha D hC.alpha) =
        (⟨d, hdH⟩ : Halpha D hC.alpha) * ⟨m, hmH⟩ := Subtype.ext rfl
    rw [hprod, map_mul, hmq, mul_one]
  · rintro ⟨x, hx, hxeq⟩
    have hxG : (x : G) ∈ DalphaStar D hC.alpha := (mem_DstarH_iff hC).mp hx
    have hxm : x⁻¹ * ⟨z, hz⟩ ∈ CFSG.solvableRadical (Halpha D hC.alpha) :=
      (QuotientGroup.eq).mp hxeq
    refine ⟨(x : G), hxG, (((x⁻¹ * ⟨z, hz⟩ : Halpha D hC.alpha) : G)), ?_, ?_⟩
    · exact ⟨x⁻¹ * ⟨z, hz⟩, hxm, rfl⟩
    · show z = (x : G) * (((x⁻¹ * ⟨z, hz⟩ : Halpha D hC.alpha) : G))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem almostSimpleCase_conj_iff (hC : HypothesisC D) (g : G) :
    AlmostSimpleCase (Halpha D (hC.conj g).alpha ⧸
        CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (imageClass (hC.conj g)) ↔
      AlmostSimpleCase (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
        (imageClass hC) := by
  let R := CFSG.solvableRadical (Halpha D hC.alpha)
  let R' := CFSG.solvableRadical (Halpha D (hC.conj g).alpha)
  let e : (Halpha D hC.alpha ⧸ R) ≃* (Halpha D (hC.conj g).alpha ⧸ R') :=
    QuotientGroup.congr R R' (conjEquiv hC g) (conjRadical_map hC g)
  have hconj : e '' imageClass hC = imageClass (hC.conj g) := by
    simpa [e, R, R'] using imageClass_conj hC g
  have hsymm : e.symm '' imageClass (hC.conj g) = imageClass hC := by
    rw [← hconj]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  constructor
  · intro h
    have h' := AlmostSimpleCase.of_mulEquiv e.symm h
    rwa [hsymm] at h'
  · intro h
    have h' := AlmostSimpleCase.of_mulEquiv e h
    rwa [hconj] at h'

@[expose] def StandingAS (hC : HypothesisC D) : Prop :=
  (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) ∧
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∧
    ¬ Group.IsSolvable (Halpha D hC.alpha) ∧ FaithfulOnBlocks hC.alpha ∧ ¬ O4PairData G D ∧
    derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 ≠
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 ∧
    AlmostSimpleCase (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
      (imageClass hC)

theorem StandingAS.conj {hC : HypothesisC D} (h : StandingAS hC) (g : G) :
    StandingAS (hC.conj g) := by
  obtain ⟨hrad, h3, hns, hF, hO4, hne, hAS⟩ := h
  exact ⟨hrad, h3, not_isSolvable_Halpha_conj hC g hns, faithfulOnBlocks_conj_alpha hC g hF,
    hO4, derivedSeries_quotient_Halpha_conj_ne hC g hne,
    (almostSimpleCase_conj_iff hC g).mpr hAS⟩

end CFSG.OddTranspositions.PartThree.EightEight

end

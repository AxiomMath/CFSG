module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCountBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem existsUnique_conj_of_existsUnique_conj_inv {X : Subgroup G} {a b : G}
    (h : ∃! x : X, (x : G)⁻¹ * a * x = b) : ∃! x : X, (x : G) * a * (x : G)⁻¹ = b := by
  obtain ⟨x, hx, huniq⟩ := h
  refine ⟨x⁻¹, by simpa only [InvMemClass.coe_inv, inv_inv] using hx, fun y hy => ?_⟩
  have : y⁻¹ = x := huniq y⁻¹ (by simpa only [InvMemClass.coe_inv, inv_inv] using hy)
  rw [← this, inv_inv]

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem X_regular (d : FinalHyps H z beta t) :
    ∀ a ∈ minimalLocalFailurePairActionPointHull H z, a ≠ 1 →
      ∀ b ∈ minimalLocalFailurePairActionPointHull H z, b ≠ 1 →
        ∃! x : rightInvolutionCommutatorSubgroup t (pairOddCore H beta),
          (x : G) * a * (x : G)⁻¹ = b := by
  obtain ⟨-, -, -, -, -, -, -, -, hreg, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses d.failure d.comm d.smallerR1 d.beta_ne
      d.flip d.proper
  intro a ha ha1 b hb hb1
  exact existsUnique_conj_of_existsUnique_conj_inv (hreg a ⟨ha, ha1⟩ b ⟨hb, hb1⟩)

theorem X_commute_J (d : FinalHyps H z beta t) {x j : G}
    (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta))
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)) :
    x * j = j * x := by
  obtain ⟨-, -, -, -, -, -, -, hXK, -⟩ := d.point_data
  exact Subgroup.mem_centralizer_iff.mp hj x (hXK hx)

theorem section_basic (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    A ≤ H ∧ H ≤ Subgroup.normalizer (A : Set G) ∧ minimalLocalFailurePairActionPointHull H z ≤ A ∧
      A ≤ TwoCoreGrowth.pointTwoCoreImage H ∧
      (∀ a ∈ A, ∀ y ∈ minimalLocalFailurePairActionPointHull H z, a * y = y * a) ∧
      IsPGroup 2 A := by
  obtain ⟨hAH, hAn, hQA, hAM, -⟩ := hA
  obtain ⟨-, hM, -⟩ := d.core_data
  refine ⟨hAH, (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn, hQA.le, hAM,
    fun a ha y hy => ?_, (TwoCoreGrowth.pointTwoCoreImage_isPGroup H).to_le hAM⟩
  have haC : a ∈ H ⊓ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
    hM ▸ hAM ha
  exact (Subgroup.mem_centralizer_iff.mp haC.2 y hy).symm

theorem section_centralizer_X
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hAM : A ≤ TwoCoreGrowth.pointTwoCoreImage H) {x : G}
    (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) (hx1 : x ≠ 1) :
    A ⊓ Subgroup.centralizer ({x} : Set G) =
      A ⊓ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) := by
  rw [← d.two_core_centralizer_X hx hx1, ← inf_assoc, inf_eq_left.mpr hAM]

theorem section_centralizer_J
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hQA : minimalLocalFailurePairActionPointHull H z ≤ A)
    (hAM : A ≤ TwoCoreGrowth.pointTwoCoreImage H) {j : G}
    (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hj1 : j ≠ 1) :
    A ⊓ Subgroup.centralizer ({j} : Set G) = minimalLocalFailurePairActionPointHull H z ⊔
      (A ⊓ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)) := by
  obtain ⟨hQH, hQn, -, -, -, hBH, -⟩ := d.point_data
  obtain ⟨-, -, hJB, -⟩ := d.core_data
  have hC := d.two_core_centralizer_J hj hj1
  apply le_antisymm
  · intro a ⟨haA, haj⟩
    have ha : a ∈ minimalLocalFailurePairActionPointHull H z ⊔
        Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) :=
      hC ▸ ⟨hAM haA, haj⟩
    obtain ⟨y, hy, k, hk, rfl⟩ := exists_mul_of_mem_sup hQH hQn (hJB.trans hBH) ha
    have hkA : k ∈ A := by
      have : k = y⁻¹ * (y * k) := by group
      rw [this]
      exact mul_mem (inv_mem (hQA hy)) haA
    exact mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right ⟨hkA, hk⟩)
  · have hQj := (le_sup_left.trans hC.symm.le).trans
      (inf_le_right : TwoCoreGrowth.pointTwoCoreImage H ⊓ Subgroup.centralizer ({j} : Set G) ≤ _)
    have hJj := (le_sup_right.trans hC.symm.le).trans
      (inf_le_right : TwoCoreGrowth.pointTwoCoreImage H ⊓ Subgroup.centralizer ({j} : Set G) ≤ _)
    exact sup_le (le_inf hQA hQj) (inf_le_inf_left A hJj)

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain

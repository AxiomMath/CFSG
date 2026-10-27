module

public import CFSG.Open.StatedDefs
import CFSG.LieType.ChevTwo.Orthogonal
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaTransv
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Bridges1
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAut
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import Certificates.Kernel.J4Count.Cent11Base
import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LieType.ChevTwo
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.GLTheoremB.MovingAround (fixSub)

theorem nonempty_mulEquiv_statedSp_minus {n : ℕ} (hn : n = 2 ∨ n = 3)
    (α : MulAut ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1))) (hα : α * α = 1)
    (hαout : α ∉ (MulAut.conj : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) →*
      MulAut ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1))).range)
    (Y : Subgroup ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)))
    (hY : ∀ y, y ∈ Y ↔ α y = y) (h5 : 5 ∣ Nat.card Y) :
    Nonempty (↥Y ≃* ↥(StatedSp n (ZMod 2))) := by
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> omega
  let ι : Type := Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2
  let Q : (ι → ZMod 2) → ZMod 2 := StatedQuadMinus (n + 1) (ZMod 2) 1 1
  have hind : InducedByIso Q α := (omegaTwoAutInduced.1 n hn1) α
  obtain ⟨g, hgκ⟩ : ∃ g : isoGrp Q, kappa Q g = α :=
    MonoidHom.mem_range.1 ((inducedByIso_iff_mem_range Q α).1 hind)
  have hG : GoodQ Q := goodQ_minus (n := n) hn1
  have hg2 : g * g = 1 := by
    apply hG.kappa_injective
    rw [map_mul, hgκ, hα, map_one]
  let G : GL ι (ZMod 2) := (isoGrp Q).subtype g
  have hgΩ : G ∉ StatedOmega Q := by
    intro hmem
    exact hαout (hgκ ▸ (hG.kappa_mem_inner_iff g).2 hmem)
  have hgne : g ≠ 1 := by
    intro hg1
    exact hgΩ (by simpa [G, hg1] using (StatedOmega Q).one_mem)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨d, hd5⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 5 h5
  let D : GL ι (ZMod 2) := (StatedOmega Q).subtype (Y.subtype d)
  have hD5 : orderOf D = 5 := by
    have h1 : orderOf (Y.subtype d) = orderOf d :=
      orderOf_injective Y.subtype Y.subtype_injective d
    have h2 : orderOf D = orderOf (Y.subtype d) :=
      orderOf_injective (StatedOmega Q).subtype (StatedOmega Q).subtype_injective (Y.subtype d)
    rw [h2, h1]
    exact hd5
  have hαd : α (Y.subtype d) = Y.subtype d := (hY (Y.subtype d)).1 d.2
  have hconj : G * D * G⁻¹ = D := by
    have h1 := congrArg (fun z : ↥(StatedOmega Q) => (z : GL ι (ZMod 2))) hαd
    rw [← hgκ] at h1
    rw [kappa_apply_val] at h1
    exact h1
  have hcomm : G * D = D * G := (mul_inv_eq_iff_eq_mul).1 hconj
  have hgg : G * G = 1 := by
    change (isoGrp Q).subtype g * (isoGrp Q).subtype g = 1
    rw [← map_mul, hg2, map_one]
  have hcard : Fintype.card ι = 2 * n + 2 := by
    change Fintype.card (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) = 2 * n + 2
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hcard_le : Fintype.card ι ≤ 8 := by
    rw [hcard]
    rcases hn with rfl | rfl <;> omega
  have hrank_disj := rank_sub_one_le_of_commute_orderOf_five hcard_le hgg hD5 hcomm
  have hne_rank : (((G : Matrix ι ι (ZMod 2)) - 1).rank) ≠ 0 := by
    intro h0
    have hbot : LinearMap.range (((G : Matrix ι ι (ZMod 2)) - 1).mulVecLin) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      simpa [Matrix.rank] using h0
    have hlin : (((G : Matrix ι ι (ZMod 2)) - 1).mulVecLin) = 0 :=
      (LinearMap.range_eq_bot).1 hbot
    have hmat : ((G : Matrix ι ι (ZMod 2)) - 1) = 0 := by
      apply Matrix.toLin'.injective
      have h1 : Matrix.toLin' (((G : Matrix ι ι (ZMod 2)) - 1)) = 0 :=
        (Matrix.toLin'_apply' _).trans hlin
      exact h1.trans (map_zero Matrix.toLin').symm
    have hunit : G = 1 := by
      apply Units.ext
      simpa using sub_eq_zero.mp hmat
    exact hgne (Subtype.ext hunit)
  have hr : (((G : Matrix ι ι (ZMod 2)) - 1).rank) = 1 := by
    rcases hn with rfl | rfl
    · rcases hrank_disj with hle | hcon
      · rw [hcard] at hle
        norm_num at hle
        omega
      · exfalso
        rw [hcard] at hcon
        exact absurd hcon.1 (by norm_num)
    · have hodd : Odd (((G : Matrix ι ι (ZMod 2)) - 1).rank) := by
        by_contra hnot
        rw [Nat.not_odd_iff_even] at hnot
        apply hgΩ
        have hnd : (QuadraticMap.polarBilin (quadMinus 4 (ZMod 2) 1 1)).Nondegenerate :=
          nondegenerate_polarBilin_quadMinus_of_finite 4 (ZMod 2) hirr_one_one
        have hT : ∃ T : Submodule (ZMod 2) ((Fin 3 ⊕ Fin 3 ⊕ Fin 2) → ZMod 2),
            Module.finrank (ZMod 2) T = 3 ∧
              ∀ x ∈ T, quadMinus 4 (ZMod 2) 1 1 x = 0 := by
          refine pd_exists_totallySingular_of (quadMinus 4 (ZMod 2) 1 1)
            (fun k : Fin 3 => (Sum.inl k : Fin 3 ⊕ Fin 3 ⊕ Fin 2)) Sum.inl_injective ?_
          intro v hv
          rw [quadMinus_apply]
          have h1 : ∀ i : Fin 3, v (Sum.inr (Sum.inl i)) = 0 := fun i => hv _ (by simp)
          have h2 : ∀ x : Fin 2, v (Sum.inr (Sum.inr x)) = 0 := fun x => hv _ (by simp)
          simp [h1, h2]
        have hA : ∀ v, quadMinus 4 (ZMod 2) 1 1
              (Matrix.mulVec (G : Matrix ι ι (ZMod 2)) v) =
            quadMinus 4 (ZMod 2) 1 1 v := by
          intro v
          rw [coe_quadMinus 4 (ZMod 2) 1 1]
          exact g.2 v
        have hmem := pdMem_statedOmega_of_even (quadMinus 4 (ZMod 2) 1 1) hnd hT hA hnot
        rwa [coe_quadMinus 4 (ZMod 2) 1 1] at hmem
      rcases hrank_disj with hle | hcon
      · rw [hcard] at hle
        norm_num at hle
        obtain ⟨k, hk⟩ := hodd
        omega
      · exact absurd hcon.2 (Nat.not_even_iff_odd.mpr hodd)
  have ht : G ∈ Subgroup.normalizer (StatedOmega Q) := isoGrp_le_normalizer Q g.2
  have hT : CFSG.LocalAnalysis.GLTheoremB.IsTransvection G :=
    isTransvection_of_rank_sub_one_eq_one hgg hr
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts.transv_minus
    (n := n) hn1 ht g.2 hT
  have hYeq : Y = fixSub α := Subgroup.ext hY
  have hfix : fixSub α = fixSub ((StatedOmega Q).normalizerMonoidHom ⟨G, ht⟩) :=
    congrArg fixSub hgκ.symm
  exact ⟨(MulEquiv.subgroupCongr (hYeq.trans hfix)).trans e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

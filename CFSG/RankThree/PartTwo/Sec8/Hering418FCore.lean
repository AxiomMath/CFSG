module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FDich

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

section Core

theorem noThetaNormal_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ¬ Group.IsSolvable Q) : NoThetaNormal Q := by
  intro N hN hNs _
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    exact hQ (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := Q)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := Q)).symm.injective)

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}

theorem Cfg.exists_mulEquiv_of_imageModTheta_eq (c : Cfg L K a b)
    {Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hY : Sec8.imageModTheta L K = Y)
    (hN : NoThetaNormal ↥Y) :
    ∃ Ψ : (K ⧸ aschbacherSolvableCore 3 K) ≃* ↥Y,
      ∀ y : K ⧸ aschbacherSolvableCore 3 K,
        ((Ψ (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y) : ↥Y) :
          L ⧸ aschbacherSolvableCore 3 L) = c.alpha (Ψ y : L ⧸ aschbacherSolvableCore 3 L) := by
  have hrange : (Item87Res2Proof.toQuot c.hKL).range = Y :=
    (Item87Res2Proof.range_toQuot c.hKL).trans hY
  have hNT : NoThetaNormal ↥(Item87Res2Proof.toQuot c.hKL).range := by
    rw [hrange]
    exact hN
  have hker := ker_toQuot_eq_of_noThetaNormal c.hKL hNT
  let Ψ0 : (K ⧸ aschbacherSolvableCore 3 K) ≃* ↥(Item87Res2Proof.toQuot c.hKL).range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange (Item87Res2Proof.toQuot c.hKL))
  refine ⟨Ψ0.trans (MulEquiv.subgroupCongr hrange), fun y => ?_⟩
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [Sec4.thetaQuotMulAut_mk]
    change Item87Res2Proof.toQuot c.hKL _ = _
    rfl

theorem Cfg.exists_mulEquiv_of_simple_core (c : Cfg L K a b)
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}))
    {Q : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hQC : Q ≤ Sec8.barCentralizer (Subgroup.zpowers b) L)
    (hQcomm : ⁅Sec8.barCentralizer (Subgroup.zpowers b) L,
      Sec8.barCentralizer (Subgroup.zpowers b) L⁆ ≤ Q)
    (hQs : IsSimpleGroup ↥Q) (hQns : ¬ Group.IsSolvable ↥Q) :
    ∃ Ψ : (K ⧸ aschbacherSolvableCore 3 K) ≃* ↥Q,
      ∀ y : K ⧸ aschbacherSolvableCore 3 K,
        ((Ψ (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y) : ↥Q) :
          L ⧸ aschbacherSolvableCore 3 L) = c.alpha (Ψ y : L ⧸ aschbacherSolvableCore 3 L) := by
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hle : Sec8.imageModTheta L K ≤ Sec8.barCentralizer (Subgroup.zpowers b) L :=
    imageModTheta_le_barCentralizer_of_le c.hbL c.hb3 c.hKL c.hKb
  haveI hP := isPerfect_imageModTheta hK
  have hcomm : ⁅Sec8.imageModTheta L K, Sec8.imageModTheta L K⁆ = Sec8.imageModTheta L K :=
    Subgroup.commutator_eq_self
  have hleQ : Sec8.imageModTheta L K ≤ Q := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono hle hle).trans hQcomm
  have hsub : ((Sec8.imageModTheta L K).subgroupOf
      (Sec8.barCentralizer (Subgroup.zpowers b) L)).IsSubnormal :=
    imageModTheta_isSubnormal_barCentralizer c.hbL c.hb3 hK
  have hsubQ : ((Sec8.imageModTheta L K).subgroupOf Q).IsSubnormal := by
    have h2 : (Sec8.imageModTheta L K).subgroupOf Q =
        Subgroup.comap (Subgroup.inclusion hQC) ((Sec8.imageModTheta L K).subgroupOf
          (Sec8.barCentralizer (Subgroup.zpowers b) L)) := by
      ext x
      rfl
    rw [h2]
    exact hsub.comap (Subgroup.inclusion hQC)
  have hne : Sec8.imageModTheta L K ≠ ⊥ := imageModTheta_ne_bot c.hKL hKq
  have hY : Sec8.imageModTheta L K = Q := by
    haveI := hQs
    rcases hsubQ.eq_bot_or_top_of_isSimpleGroup hQs with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hleQ hx⟩ : ↥Q) ∈ (Sec8.imageModTheta L K).subgroupOf Q :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · refine le_antisymm hleQ fun x hx => ?_
      have : (⟨x, hx⟩ : ↥Q) ∈ (Sec8.imageModTheta L K).subgroupOf Q := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp this
  haveI := hQs
  exact c.exists_mulEquiv_of_imageModTheta_eq hY (noThetaNormal_of_isSimpleGroup hQns)

end Core

end CFSG.RankThree.PartTwo.Sec8.Hering418

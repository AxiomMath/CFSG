module

import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MInd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  CFSG.RankThree.LocalRank Ronan148M Main148

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem img148_closure_le_centralizer {S : Set G} (hS : S ⊆ (Y ⊔ A : Subgroup G))
    {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h : ∀ g (hg : g ∈ S), QuotientGroup.mk' (ker148 A Y) (⟨g, hS hg⟩ : ↥(Y ⊔ A)) ∈
      Subgroup.centralizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    img148 A Y (Subgroup.closure S) ≤
      Subgroup.centralizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  set P : Subgroup G := ((Subgroup.centralizer (T : Set (↥(Y ⊔ A) ⧸ ker148 A Y))).comap
    (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype with hP
  have hSP : Subgroup.closure S ≤ P := by
    rw [Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, hS hg⟩, h g hg, rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgS, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hSP hgS
  have : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← this]
  exact hm

theorem card_theta_quot_le_card_img148 {H : Subgroup G} (hHM : H ≤ Y ⊔ A)
    (hHp : Group.IsPerfect H) (hHq : IsQuasisimple (↥H ⧸ aschbacherSolvableCore 3 ↥H))
    (h3H : 3 ∣ Nat.card H) :
    Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H) ≤ Nat.card (img148 A Y H) := by
  set ι := phi148 (A := A) (Y := Y) hHM with hι
  have hker3 : ¬ 3 ∣ Nat.card ι.ker := not_three_dvd_card_ker_phi148 hHM
  have hrp : Group.IsPerfect ι.range :=
    Group.IsPerfect.ofSurjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective
  have hker' : ι.rangeRestrict.ker = ι.ker := MonoidHom.ker_rangeRestrict ι
  rw [← range_phi148 hHM]
  rcases Res148.ker_le_theta_or_subsingleton ι.rangeRestrict ι.rangeRestrict_surjective hrp hHq
      (by rw [hker']; exact hker3) with hle | hsub
  · rw [hker'] at hle
    have e1 : Nat.card ↥H = Nat.card ι.range * Nat.card ι.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ι.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ι).toEquiv]
    have e2 : Nat.card ↥H = Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H) *
        Nat.card (aschbacherSolvableCore 3 ↥H) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hk : Nat.card ι.ker ≤ Nat.card (aschbacherSolvableCore 3 ↥H) :=
      Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card (aschbacherSolvableCore 3 ↥H) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card (↥H ⧸ aschbacherSolvableCore 3 ↥H) * Nat.card (aschbacherSolvableCore 3 ↥H)
        = Nat.card ι.range * Nat.card ι.ker := by rw [← e1, ← e2]
      _ ≤ Nat.card ι.range * Nat.card (aschbacherSolvableCore 3 ↥H) := Nat.mul_le_mul_left _ hk
  · exfalso
    apply hker3
    have htop : ι.ker = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have := Subsingleton.elim (ι.rangeRestrict y) 1
      exact congrArg Subtype.val this
    rw [htop, Subgroup.card_top]
    exact h3H

theorem img148_deltaZero_le_of_hyperplanes_of_le {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) {Y' : Subgroup G} (hY' : Y' ≤ Y) {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h : ∀ E : Subgroup G, IsHyperplane A E → ∀ R ∈ scriptQZero A LB,
      R ≤ Y' ⊓ Subgroup.centralizer (E : Set G) → img148 A Y R ≤ T) :
    img148 A Y (deltaZero A LB Y') ≤ T := by
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype
    with hT'
  have hle : deltaZero A LB Y' ≤ T' := by
    rw [deltaZero_eq_iSup hA Y']
    refine iSup₂_le fun E hE => sSup_le fun R hR => ?_
    obtain ⟨hR0, hRY⟩ := hR
    intro g hg
    have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left (hY' (hRY hg).1)
    exact ⟨⟨g, hgM⟩, h E hE R hR0 hRY (mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩), rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hle hgD
  have : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← this]
  exact hm

end CFSG.RankThree.PartTwo.Sec14.Ronan148J

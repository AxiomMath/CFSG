module

import CFSG.RankThree.PartTwo.Sec8.Hering418FDich
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item65One
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


namespace Hering88E

theorem eq_inSubgroup_perfectResidual_of_isSubnormal {Q : Type} [Group Q] [Finite Q]
    {R N : Subgroup Q} (hNR : N ≤ R) (hN : Group.IsPerfect N)
    (hsub : (N.subgroupOf R).IsSubnormal) (hne : N ≠ ⊥)
    (hS : IsSimpleGroup (inSubgroup perfectResidual R)) :
    N = inSubgroup perfectResidual R := by
  have hNS : N ≤ inSubgroup perfectResidual R := KFacts.le_inSubgroup_perfectResidual hN hNR
  have hSR : inSubgroup perfectResidual R ≤ R := Item87Proof.residual_le R
  have hsubS : (N.subgroupOf (inSubgroup perfectResidual R)).IsSubnormal := by
    have h2 : N.subgroupOf (inSubgroup perfectResidual R) =
        Subgroup.comap (Subgroup.inclusion hSR) (N.subgroupOf R) := by
      ext x
      rfl
    rw [h2]
    exact hsub.comap (Subgroup.inclusion hSR)
  rcases hsubS.eq_bot_or_top_of_isSimpleGroup hS with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNS hx⟩ : ↥(inSubgroup perfectResidual R)) ∈
        N.subgroupOf (inSubgroup perfectResidual R) := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · refine le_antisymm hNS fun x hx => ?_
    have : (⟨x, hx⟩ : ↥(inSubgroup perfectResidual R)) ∈
        N.subgroupOf (inSubgroup perfectResidual R) := by rw [h]; trivial
    exact Subgroup.mem_subgroupOf.mp this

section Pair

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
  {X : Subgroup G} {n : ℕ}

theorem sec8I_mem_thetaComponentsIn_centralizer (hC : KF87Cent) (h : Sec8Pair G A c L a b X n)
    (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) (hI : sec8I L a ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIY : sec8I L a ≤ Y) :
    sec8I L a ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  obtain ⟨-, -, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hIdef : sec8I L a =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  have hcases := Item87Proof.residual_centralizer_cases hC h.mem_thetaComponentsAt hn
    (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) ha3 h.inducesStdKind
  rw [← hIdef] at hcases
  rcases hcases with h0 | hm
  · exact absurd h0 hI
  · obtain ⟨hIM, hIp⟩ := mem_thetaComponentsIn_iff.mp hm
    have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) :=
      (PartOne.mem_thetaComponentsAt_iff.mp hY).1
    have hsub : Y ⊓ Subgroup.centralizer ({c} : Set G) ≤
        Subgroup.centralizer {c} ⊓ Subgroup.centralizer {a} :=
      le_inf inf_le_right (inf_le_left.trans hYa)
    have hle : sec8I L a ≤ Y ⊓ Subgroup.centralizer ({c} : Set G) :=
      le_inf hIY (hIM.trans inf_le_left)
    exact mem_thetaComponentsIn_iff.mpr
      ⟨hle, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle hsub hIp⟩

theorem sec8J_mem_thetaComponentsIn_centralizer (hC : KF87Cent) (h84 : Pair84A)
    (h : Sec8Pair G A c L a b X n) (hJ : sec8J X a ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hJY : sec8J X a ≤ Y) :
    sec8J X a ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  obtain ⟨d, m, hdm⟩ := h.mem_pairOmega.2.2.2.2.2
  obtain ⟨-, -, hm, -⟩ := Item87Proof.isGammaIndex_cases hdm
  have hcases := Item87Proof.residual_centralizer_cases hC hX hm
    (Item87Proof.isGammaType_of_isGammaIndex hdm) ha3 (h84 G A c L a b X n h)
  have hJdef : sec8J X a =
      inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) := rfl
  rw [← hJdef] at hcases
  rcases hcases with h0 | hm'
  · exact absurd h0 hJ
  · obtain ⟨hJM, hJp⟩ := mem_thetaComponentsIn_iff.mp hm'
    have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) :=
      (PartOne.mem_thetaComponentsAt_iff.mp hY).1
    have hsub : Y ⊓ Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.centralizer {b} ⊓ Subgroup.centralizer {a} :=
      le_inf inf_le_right (inf_le_left.trans hYa)
    have hle : sec8J X a ≤ Y ⊓ Subgroup.centralizer ({b} : Set G) :=
      le_inf hJY (hJM.trans inf_le_left)
    exact mem_thetaComponentsIn_iff.mpr
      ⟨hle, PartOne.subgroupOf_mem_thetaComponents_of_le Nat.prime_three hle hsub hJp⟩

theorem imageModTheta_sec8I_eq_perfectResidual (hC : KF87Cent) (h : Sec8Pair G A c L a b X n)
    (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) (hI : sec8I L a ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIY : sec8I L a ≤ Y)
    (hcY : c ∈ Subgroup.normalizer (Y : Set G))
    (hS : IsSimpleGroup (inSubgroup perfectResidual
      (barCentralizer (Subgroup.zpowers c) Y))) :
    imageModTheta Y (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers c) Y) := by
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hK := sec8I_mem_thetaComponentsIn_centralizer hC h hUn hI hY hIY
  obtain ⟨hKM, -⟩ := mem_thetaComponentsIn_iff.mp hK
  exact eq_inSubgroup_perfectResidual_of_isSubnormal
    (Hering418.imageModTheta_le_barCentralizer_of_le hcY hc3 (hKM.trans inf_le_left)
      (hKM.trans inf_le_right))
    (Hering418.isPerfect_imageModTheta hK)
    (Hering418.imageModTheta_isSubnormal_barCentralizer hcY hc3 hK)
    (Hering418.imageModTheta_ne_bot (hKM.trans inf_le_left)
      (Sec6.isQuasisimple_of_mem_thetaComponentsIn hK)) hS

theorem imageModTheta_sec8J_eq_perfectResidual (hC : KF87Cent) (h84 : Pair84A)
    (h : Sec8Pair G A c L a b X n) (hJ : sec8J X a ≠ ⊥)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hJY : sec8J X a ≤ Y)
    (hbY : b ∈ Subgroup.normalizer (Y : Set G))
    (hS : IsSimpleGroup (inSubgroup perfectResidual
      (barCentralizer (Subgroup.zpowers b) Y))) :
    imageModTheta Y (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers b) Y) := by
  have hbA : b ∈ A := (Item87Proof.isGammaIndex_cases h.isGammaIndex).1
  have hb3 : b ^ 3 = 1 := h.mem_partTwoF.1.2 b hbA
  have hK := sec8J_mem_thetaComponentsIn_centralizer hC h84 h hJ hY hJY
  obtain ⟨hKM, -⟩ := mem_thetaComponentsIn_iff.mp hK
  exact eq_inSubgroup_perfectResidual_of_isSubnormal
    (Hering418.imageModTheta_le_barCentralizer_of_le hbY hb3 (hKM.trans inf_le_left)
      (hKM.trans inf_le_right))
    (Hering418.isPerfect_imageModTheta hK)
    (Hering418.imageModTheta_isSubnormal_barCentralizer hbY hb3 hK)
    (Hering418.imageModTheta_ne_bot (hKM.trans inf_le_left)
      (Sec6.isQuasisimple_of_mem_thetaComponentsIn hK)) hS

end Pair

section G2Simple

variable {Q : Type} [Group Q] [Finite Q]

theorem isSimpleGroup_perfectResidual_of_isoGTwoEven {R : Subgroup Q} {m : ℕ} (hm : 2 ≤ m)
    (h : IsoGTwoEven R m) : IsSimpleGroup (inSubgroup perfectResidual R) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3
  haveI hsg := Sec11.KS11Lie2Proof.isSimpleGroup_g2 hK3
  haveI : IsSimpleGroup R := MulEquiv.isSimpleGroup e
  haveI : Group.IsPerfect R := by
    have hqR : IsQuasisimple R := LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    exact hqR.1
  rw [inSubgroup_perfectResidual_of_isPerfect (R := R) inferInstance]
  exact inferInstance

end G2Simple

section Case1

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
  {X : Subgroup G} {n : ℕ}

theorem imageModTheta_sec8I_eq_perfectResidual_of_isoGTwoEven (hC : KF87Cent)
    (h : Sec8Pair G A c L a b X n) (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3)
    (hI : sec8I L a ≠ ⊥) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    (hIY : sec8I L a ≤ Y) (hcY : c ∈ Subgroup.normalizer (Y : Set G)) {m : ℕ} (hm : 2 ≤ m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) m) :
    imageModTheta Y (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers c) Y) :=
  imageModTheta_sec8I_eq_perfectResidual hC h hUn hI hY hIY hcY
    (isSimpleGroup_perfectResidual_of_isoGTwoEven hm hG2)

theorem imageModTheta_sec8J_eq_perfectResidual_of_isoGTwoEven (hC : KF87Cent) (h84 : Pair84A)
    (h : Sec8Pair G A c L a b X n) (hJ : sec8J X a ≠ ⊥) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hJY : sec8J X a ≤ Y)
    (hbY : b ∈ Subgroup.normalizer (Y : Set G)) {m : ℕ} (hm : 2 ≤ m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers b) Y) m) :
    imageModTheta Y (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers b) Y) :=
  imageModTheta_sec8J_eq_perfectResidual hC h84 h hJ hY hJY hbY
    (isSimpleGroup_perfectResidual_of_isoGTwoEven hm hG2)

end Case1


end Hering88E

end CFSG.RankThree.PartTwo.Sec8

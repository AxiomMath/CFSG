module

import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88D

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem le_theta_of_imageModTheta_eq_bot {G : Type} [Group G] [Finite G] {Y U : Subgroup G}
    (hUY : U ≤ Y) (h : imageModTheta Y U = ⊥) :
    U ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
  intro u hu
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨u, hUY hu⟩ ∈ imageModTheta Y U :=
    ⟨⟨u, hUY hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨u, hUY hu⟩, h1, rfl⟩

theorem not_le_theta_residual_centralizer (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n) {Y : Subgroup G}
    (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) :
    ¬ inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      inSubgroup (aschbacherSolvableCore 3) Y := by
  have hAel := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hK
  set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
  set T := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) with hT
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
      ((Item87Proof.residual_le _).trans inf_le_right)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
      rcases hw with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk' d hdcl).symm
  have hKX : K ≤ X := h.pairRel.2.2.2.1
  have hTK : T ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := Item87Proof.residual_le _
  have hTp : Group.IsPerfect T := Item87Proof.isPerfect_residual _
  have hTJ : T ≤ sec8J X a :=
    KFacts.le_inSubgroup_perfectResidual hTp
      (le_inf (hTK.trans (inf_le_left.trans hKX)) (hTK.trans inf_le_right))
  have hTU : T ≤ U :=
    KFacts.le_inSubgroup_perfectResidual hTp
      (le_inf (hTJ.trans (le_sup_right.trans hIJ)) (hTK.trans (inf_le_left.trans hKd)))
  have hT1 : T ≠ ⊥ := by
    refine Item87Res2Proof.residual_centralizer_ne_bot_of_field hn2 ?_ ha3
      (hF G A c L a b X n h)
    rcases Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex with ⟨hRee, hSU⟩ | hL2
    · exact Or.inl ⟨Item87Res2Proof.odd_of_isGammaTypeRee hRee, hSU⟩
    · exact Or.inr hL2
  intro hle
  exact Item87Res2Proof.not_le_theta_of_isPerfect hTp hT1 (M := Y) (hTU.trans hle)

theorem imageModTheta_residual_centralizer_ne_bot (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n) {Y : Subgroup G}
    (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) :
    imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≠ ⊥ :=
  fun hbot => not_le_theta_residual_centralizer hF h hn2 hIJ hdcl
    (le_theta_of_imageModTheta_eq_bot ((Item87Proof.residual_le _).trans inf_le_left) hbot)

end Hering88D

end CFSG.RankThree.PartTwo.Sec8

module

public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof4443
public import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


section Certs


structure DiagSetting (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L : Subgroup G) : Prop where
  ctx : Ctx4443 G A M H s
  mem : L ∈ thetaComponents 3 G
  three_dvd : 3 ∣ Nat.card L
  not_le : ¬ L ≤ M
  I_norm : inSubgroup perfectResidual H ≤ Subgroup.normalizer (L : Set G)
  I_le : (inSubgroup perfectResidual H).map (starQuot G) ≤ L.map (starQuot G) ⊔
    Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))
  I_nc : ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
    Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))
  s_norm : s ∈ Subgroup.normalizer (L : Set G)
  s_nc : ¬ (Subgroup.zpowers s).map (starQuot G) ≤
    Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))
  I_iso : Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃* projSL 3 (GaloisField 2 2))
  I_not_le : ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤ L.map (starQuot G)

theorem item4_44_3Diag_iff : Item4_44_3Diag ↔ ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L : Subgroup G),
    DiagSetting G A M H s L → Concl4443 M H := by
  unfold Item4_44_3Diag
  constructor
  · intro hD G _ _ A M H s L h
    exact hD G A M H s L h.ctx h.mem h.three_dvd h.not_le h.I_norm h.I_le h.I_nc h.s_norm
      h.s_nc h.I_iso h.I_not_le
  · intro hD G _ _ A M H s L hctx hmem h3 hnle hIn hIle hInc hs hsnc hiso hInl
    exact hD G A M H s L ⟨hctx, hmem, h3, hnle, hIn, hIle, hInc, hs, hsnc, hiso, hInl⟩

theorem exists_thetaComponent_lift_of_moved (hSz : KFacts.KPSz) (h45 : Item4_5)
    {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G} {L : Subgroup G}
    (h : DiagSetting G A M H s L) {K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)} (hK : CFSG.IsComponent K)
    (hmoved : ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤ Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    ∃ J ∈ thetaComponents 3 G, J.map (starQuot G) = K ∧ 3 ∣ Nat.card J ∧ A ≤ Subgroup.normalizer (J : Set G) ∧
      inSubgroup perfectResidual H ≤ Subgroup.normalizer (J : Set G) ∧ ⁅J, inSubgroup perfectResidual H⁆ = J := by
  obtain ⟨J, hJ, hJK⟩ := exists_mem_thetaComponents_map_eq hSz h.ctx.ctx444.sectionFourHyp.kGroup
    (localRank_theta_quotient_le h.ctx.ctx444.sectionFourHyp) hK
  have h3K : 3 ∣ Nat.card K :=
    CFSG.RankThree.PartTwo.Sec4.three_dvd_card_of_isComponent
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) 3) hK
  have h3 : 3 ∣ Nat.card J := by
    rw [← hJK] at h3K
    exact h3K.trans (Subgroup.card_map_dvd J (starQuot G))
  have hA : A ≤ Subgroup.normalizer (J : Set G) :=
    Ctx444.le_normalizer_of_mem_thetaComponents h45 h.ctx.ctx444 hJ
  have hI : inSubgroup perfectResidual H ≤ Subgroup.normalizer (J : Set G) :=
    Item4443SL.Ctx4443.le_normalizer_of_commutator_eq h45 h.ctx
      (Item4443SL.Ctx4443.commutator_A_eq_general h.ctx) hJ
  have hc : ⁅J, inSubgroup perfectResidual H⁆ = J := by
    refine commutator_eq_self_of_not_le_centralizer hJ h3 hI ?_
    rw [hJK]
    exact hmoved
  exact ⟨J, hJ, hJK, h3, hA, hI, hc⟩

theorem DiagSetting.commutator_I_eq {Y : Type} [Group Y] [Finite Y] (H : Subgroup Y) :
    ⁅inSubgroup perfectResidual H, inSubgroup perfectResidual H⁆ =
      inSubgroup perfectResidual H :=
  CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual H

theorem DiagSetting.localRank_three_quotient_le {G : Type} [Group G] [Finite G]
    (h : SectionFourHyp G) :
    CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ CFSG.pPrimeCore 3 G) ≤ 3 := by
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le (G := G) (p := 3) Nat.prime_three
    (by norm_num) (CFSG.pPrimeCore 3 G) (not_three_dvd_card_pPrimeCore (G := G))
  have h2 := CFSG.RankThree.OddKernel.localRank_le_evenRank (G := G) (r := 3) Nat.prime_three
    (by norm_num)
  exact h1.trans (h2.trans h.evenRank_le)

theorem isQuasisimple_projSL_three_four : CFSG.IsQuasisimple (projSL 3 (GaloisField 2 2)) := by
  have hs : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  have hq : IsSimpleGroup (projSL 3 (GaloisField 2 2) ⧸
      Subgroup.center (projSL 3 (GaloisField 2 2))) :=
    ((QuotientGroup.quotientMulEquivOfEq center_projSL_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup
  refine ⟨isPerfect_projSL, hq, ?_⟩
  by_contra hab
  push Not at hab
  haveI : Group.IsPerfect (projSL 3 (GaloisField 2 2)) := isPerfect_projSL
  have hperf : Group.IsPerfect (projSL 3 (GaloisField 2 2) ⧸
      Subgroup.center (projSL 3 (GaloisField 2 2))) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Nontrivial (projSL 3 (GaloisField 2 2) ⧸
      Subgroup.center (projSL 3 (GaloisField 2 2))) := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable _ (Group.isSolvable_of_comm hab)

theorem DiagSetting.I_le_layer {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L : Subgroup G} (hSz : KFacts.KPSz) (hS : SchreierFor CFSG.Assembly.InCatalog)
    (h45 : Item4_5) (h : DiagSetting G A M H s L) :
    (inSubgroup perfectResidual H).map (starQuot G) ≤ CFSG.layer (G ⧸ CFSG.pPrimeCore 3 G) := by
  obtain ⟨e⟩ := h.I_iso
  have hIq : CFSG.IsQuasisimple
      (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_projSL_three_four
  exact Item4443SL.Ctx4443.map_le_layer hSz hS h45 h.ctx
    (Item4443SL.Ctx4443.commutator_A_eq_general h.ctx) hIq

theorem DiagSetting.center_isPGroup_three {X : Type} [Group X] [Finite X]
    (hX : CFSG.pPrimeCore 3 X = ⊥) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    IsPGroup 3 ((Subgroup.center K).map K.subtype) := by
  have hKL : K ≤ CFSG.layer X := by
    rw [CFSG.layer.eq_sSup X]
    exact le_sSup (show K ∈ {K : Subgroup X | CFSG.IsComponent K} from hK)
  have hZ : (Subgroup.center K).map K.subtype ≤
      (Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hcomp : ∀ K' : Subgroup X, CFSG.IsComponent K' →
        K' ≤ Subgroup.centralizer ({(z : X)} : Set X) := by
      intro K' hK'
      rcases CFSG.LocalCores.distinct_components_commute hK hK' with hEq | hcommut
      · subst hEq
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff.mp ht]
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
        simp only [Subgroup.coe_mul] at h1
        exact h1.symm
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff.mp ht]
        have hzK : (z : X) ∈ K := z.2
        have hz' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommut hzK
        exact (Subgroup.mem_centralizer_iff.mp hz' y hy).symm
    have hLc : CFSG.layer X ≤ Subgroup.centralizer ({(z : X)} : Set X) := by
      rw [CFSG.layer.eq_sSup X]
      exact sSup_le fun K' hK' => hcomp K' hK'
    have hzL : (z : X) ∈ CFSG.layer X := hKL z.2
    refine ⟨⟨z, hzL⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h2 := Subgroup.mem_centralizer_iff.mp (hLc g.2) (z : X) (Set.mem_singleton _)
    simp only [Subgroup.coe_mul]
    exact h2.symm
  exact (CFSG.pCore_isPGroup (p := 3) (G := X)).to_le
    (hZ.trans ((CFSG.WholeGroup.center_layer_le_fittingSubgroup (G := X)).trans
      (fittingSubgroup_le_pCore_three_of_pPrimeCore_eq_bot hX)))

end Certs

end CFSG.RankThree.PartTwo.Sec4

end

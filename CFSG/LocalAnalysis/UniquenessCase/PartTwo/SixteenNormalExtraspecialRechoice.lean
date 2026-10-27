module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Rechoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ZpFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem commSub_top_eq_top_and_conc4_136W_of_normal_isPOnePlusTwo
    {W : Type} [CommGroup W]
    {A Z H : Subgroup (MulAut W)} {t : MulAut W}
    (hZ : Conc4_136W A t Z)
    (hZcard : Nat.card ↥Z = 3)
    (hrk : rk ↥(⊤ : Subgroup W) = 6)
    (hHA : H ≤ A)
    (hHnormal : (H.subgroupOf A).Normal)
    (hZH : Z ≤ H)
    (hH : IsPOnePlusTwo 3 ↥H) :
    commSub (⊤ : Subgroup W) H = ⊤ ∧ Conc4_136W A t H := by
  have hAN : A ≤ normalizer (H : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHA).mp hHnormal
  have hconjZ : ∀ g ∈ A, Z.map (MulAut.conj g).toMonoidHom ≤ H := by
    intro g hg x hx
    obtain ⟨z, hz, rfl⟩ := hx
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.1 (hAN hg) z).1 (hZH hz)
  have hfull : commSub ⊤ H = ⊤ := by
    refine eq_top_iff.2 (hZ.1.symm.trans_le ?_)
    refine iSup₂_le fun X hX => ?_
    obtain ⟨g, hg, rfl⟩ := hX
    calc (commSub ⊤ Z).map g.toMonoidHom
        = commSub ⊤ (Z.map (MulAut.conj g).toMonoidHom) :=
          (s15_Infra_commSub_top_map_conj Z g).symm
      _ ≤ commSub ⊤ H := commSub_mono le_rfl (hconjZ g hg)
  have hHp : IsPGroup 3 ↥H :=
    @CFSG.IsExtraspecial.isPGroup 3 ⟨Nat.prime_three⟩ ↥H inferInstance hH.1
  have hHcore : H ≤ CFSG.Open.pCoreOf 3 A :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.le_pCoreOf_of_normal hHA hHnormal hHp
  obtain ⟨-, -, -, hZt, -⟩ := s16h_conc4_133_of_prime_card Nat.prime_three hZcard hZ
  have hHt : ⁅H, Subgroup.zpowers t⁆ ≠ ⊥ := fun hbot =>
    hZt (eq_bot_iff.2 (hbot ▸ Subgroup.commutator_mono hZH le_rfl))
  have hconj : conjSubs A (commSub ⊤ H) = {⊤} := by
    rw [hfull]
    ext X
    simp only [conjSubs, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, -, rfl⟩
      exact Subgroup.map_top_of_surjective _ g.surjective
    · rintro rfl
      exact ⟨1, A.one_mem, (Subgroup.map_top_of_surjective _ (1 : MulAut W).surjective).symm⟩
  refine ⟨hfull, ?_, fun g hg hgn => (hgn (hAN hg)).elim, Or.inl ?_⟩
  · rw [hconj]
    simp
  · refine ⟨3, Nat.prime_three, hHcore, hHt, ?_,
      Or.inr (Or.inr (Or.inl ⟨hH, by rw [hfull]; exact hrk⟩))⟩
    rw [hconj]
    exact sSupIndep_singleton _

theorem exists_rechoice_case162_4_case168_3_of_normal_isPOnePlusTwo
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h16 : Hyp16 D V₀ V)
    (hconc : Conc4_136 D V₀ V hV L)
    (hLcard : Nat.card ↥(lBar V₀ V hV L) = 3)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6)
    (hsig : D.sig = {3})
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hHA : H ≤ Mbar D.M V₀ V hV)
    (hHnormal : (H.subgroupOf (Mbar D.M V₀ V hV)).Normal)
    (hLH : lBar V₀ V hV L ≤ H)
    (hH : IsPOnePlusTwo 3 ↥H) :
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧
      barSub V₀ V hV L' ≠ ⊥ ∧ Conc4_136 D V₀ V hV L' ∧
      lBar V₀ V hV L' = H ∧
      Case162_4 D V₀ V hV L' ∧ Case168_3 D V₀ V hV L' := by
  obtain ⟨t, htM, ht2, ht1, htr, hW⟩ := hconc
  obtain ⟨hfull, hHW⟩ :=
    commSub_top_eq_top_and_conc4_136W_of_normal_isPOnePlusTwo
      hW hLcard hrk hHA hHnormal hLH hH
  obtain ⟨L', hS', hbar, hconc', -⟩ :=
    s16e_d5_rechoice D hV h16 htM ht2 ht1 htr hHW
  have hlbar : lBar V₀ V hV L' = H := hbar
  have hwt : wTil V₀ V hV L' = ⊤ := by
    change commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L') = ⊤
    rw [hlbar]
    exact hfull
  have hbarSub : barSub V₀ V hV L' ≠ ⊥ := by
    rw [hbar]
    exact hHW.ne_bot
  have hcase2 : Case162_4 D V₀ V hV L' :=
    ⟨hlbar ▸ hH, by rw [hwt]; exact hrk,
      Nat.succ_le_of_lt (s15_Eleven_pos_s D hS'.hyp151 hV)⟩
  have hcase3 : Case168_3 D V₀ V hV L' := ⟨hlbar ▸ hH, hrk, hsig⟩
  exact ⟨L', hS', hbarSub, hconc', hlbar, hcase2, hcase3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

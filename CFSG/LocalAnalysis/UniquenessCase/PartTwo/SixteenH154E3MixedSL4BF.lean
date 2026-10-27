module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BFA
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABGA2A
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_sl4_E9_normalizes_sup {W : Type} [CommGroup W] [Finite W]
    {X L L' T : Subgroup (MulAut W)} (F : s16h_SL4TwoFrame X L L' T)
    (hL : IsAlt ↥L 5) (hLL' : L ≠ L') :
    ∃ E : Subgroup (MulAut W), E ≤ L ⊔ L' ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧
      E ≤ Subgroup.normalizer ((T ⊓ (L ⊔ L') : Subgroup (MulAut W)) : Set (MulAut W)) := by
  classical
  obtain ⟨hTLsyl, hTL'syl⟩ := s16h_sl4_bf_sylow_inf F
  have hdisjLL' := s16h_sl4_bf_inf_eq_bot F hL hLL'
  have hEq := s16h_sl4_bf_inf_sup_eq F hL hLL'
  obtain ⟨e⟩ := hL
  have hL' : IsAlt ↥L' 5 := by
    obtain ⟨t, -, htL⟩ := F.swap
    have htL' : L.map (↑(MulAut.conj t) : MulAut W →* MulAut W) = L' := by
      simpa only [MulEquiv.toMonoidHom_eq_coe] using htL
    exact ⟨((MulEquiv.subgroupMap (MulAut.conj t) L).trans
      (MulEquiv.subgroupCongr htL')).symm.trans e⟩
  obtain ⟨e'⟩ := hL'
  obtain ⟨b, hbL, hb3, hb1, hbN⟩ :=
    s16h_sl4_bf_exists_order_three (X := MulAut W) (H := L) (S := T ⊓ L) e hTLsyl
  obtain ⟨b', hb'L', hb'3, hb'1, hb'N⟩ :=
    s16h_sl4_bf_exists_order_three (X := MulAut W) (H := L') (S := T ⊓ L') e' hTL'syl
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers b', x * y = y * x := by
    intro x hx y hy
    exact F.comm x (Subgroup.zpowers_le_of_mem hbL hx) y (Subgroup.zpowers_le_of_mem hb'L' hy)
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers b' = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf (Subgroup.zpowers_le_of_mem hbL)
      (Subgroup.zpowers_le_of_mem hb'L')).trans (le_of_eq hdisjLL')
  have hE := s16h_zpowers_sup_noncyclic_of_prime (X := MulAut W) (p := 3)
    (by norm_num) hb3 hb'3 hb1 hb'1 hcomm hdisj
  have hbC : b ∈ Subgroup.centralizer ((T ⊓ L') : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (F.comm b hbL y hy.2).symm
  have hbN' : b ∈ Subgroup.normalizer ((T ⊓ L') : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer _ hbC
  have hbJoin : b ∈ Subgroup.normalizer (((T ⊓ L) ⊔ (T ⊓ L') : Subgroup (MulAut W)) :
      Set (MulAut W)) :=
    s16h_normalizer_inf_le_normalizer_join (A := T ⊓ L) (B := T ⊓ L') ⟨hbN, hbN'⟩
  have hbTop : b ∈ Subgroup.normalizer ((T ⊓ (L ⊔ L') : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
    rw [hEq]
    exact hbJoin
  have hb'C : b' ∈ Subgroup.centralizer ((T ⊓ L) : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact F.comm y hy.2 b' hb'L'
  have hb'N'' : b' ∈ Subgroup.normalizer ((T ⊓ L) : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer _ hb'C
  have hb'Join : b' ∈ Subgroup.normalizer (((T ⊓ L) ⊔ (T ⊓ L') : Subgroup (MulAut W)) :
      Set (MulAut W)) :=
    s16h_normalizer_inf_le_normalizer_join (A := T ⊓ L) (B := T ⊓ L') ⟨hb'N'', hb'N⟩
  have hb'Top : b' ∈ Subgroup.normalizer ((T ⊓ (L ⊔ L') : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
    rw [hEq]
    exact hb'Join
  refine ⟨Subgroup.zpowers b ⊔ Subgroup.zpowers b', ?_, hE.1, hE.2, ?_⟩
  · exact sup_le ((Subgroup.zpowers_le_of_mem hbL).trans le_sup_left)
      ((Subgroup.zpowers_le_of_mem hb'L').trans le_sup_right)
  · exact sup_le (Subgroup.zpowers_le_of_mem hbTop) (Subgroup.zpowers_le_of_mem hb'Top)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

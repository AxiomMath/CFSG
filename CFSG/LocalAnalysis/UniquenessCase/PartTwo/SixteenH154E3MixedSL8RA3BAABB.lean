module

public import CFSG.ClassicalGroups.SL2Sp4SylowNormalizer
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_sylow_two_borel_seven {Ω : Type} [Group Ω] [Finite Ω] {A U : Subgroup Ω}
    (hA : IsSLn ↥A 2 3) (hU : CFSG.ABGLocalTools.IsSylowOf 2 U A) :
    IsElemAbelian 2 U ∧ Nat.card ↥U = 8 ∧
      ∃ b ∈ A, b ∈ Subgroup.normalizer (U : Set Ω) ∧ orderOf b = 7 := by
  classical
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eA⟩⟩ := hA
  letI := hKf
  letI := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    refine charP_of_card_eq_prime_pow (p := 2) (f := 3) ?_
    rw [← Nat.card_eq_fintype_card, hKcard]
  have hK8 : Nat.card K = 8 := by rw [hKcard]; norm_num
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_eq_subgroupOf
  have hQmap : (Q : Subgroup ↥A).map A.subtype = U := by
    rw [hQ, Subgroup.subgroupOf_map_subtype, inf_of_le_left hU.le]
  let eK : Matrix.SpecialLinearGroup (Fin 2) K ≃* StatedSL 2 K :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K
  let eAK : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) K := eA.trans eK.symm
  let U'' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Q.mapSurjective (f := eAK.toMonoidHom) eAK.surjective
  have hU''coe : (U'' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) =
      (Q : Subgroup ↥A).map eAK.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eAK.toMonoidHom) (p := 2) (hf := eAK.surjective) Q
  obtain ⟨g, hg⟩ :=
    CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow
      (CFSG.CGT.Timmesfeld75.utriSylow K) U''
  have hU''el : IsElemAbelian 2 (U'' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) := by
    rw [← hg, CFSG.CGT.Timmesfeld75.coe_utriSylow]
    exact CFSG.CGT.Timmesfeld75.isElemAbelian_conjSubgroup
      (CFSG.CGT.Timmesfeld75.isElemAbelian_utri (F := K)) g
  have hQel : IsElemAbelian 2 (Q : Subgroup ↥A) := by
    have h1 : IsElemAbelian 2
        ((U'' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)).comap eAK.toMonoidHom) :=
      IsElemAbelian.comap hU''el eAK.injective
    rw [hU''coe, Subgroup.comap_map_eq_self_of_injective eAK.injective (Q : Subgroup ↥A)] at h1
    exact h1
  have hElemU : IsElemAbelian 2 U := by
    rw [← hQmap]
    exact IsElemAbelian.map hQel A.subtype
  have hcardU'' : Nat.card (U'' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) = 8 := by
    rw [← hg, CFSG.CGT.Timmesfeld75.coe_utriSylow,
      CFSG.CGT.Timmesfeld75.card_conjSubgroup, CFSG.CGT.Timmesfeld75.card_utri, hK8]
  have hcardQ : Nat.card (Q : Subgroup ↥A) = 8 := by
    rw [← Subgroup.card_map_of_injective (f := eAK.toMonoidHom) eAK.injective,
      ← hU''coe, hcardU'']
  have hcardU : Nat.card ↥U = 8 := by
    have h1 : Nat.card (U.subgroupOf A) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.le).toEquiv
    rw [← h1, ← hQ, hcardQ]
  let U' : Sylow 2 (StatedSL 2 K) := Q.mapSurjective (f := eA.toMonoidHom) eA.surjective
  have hU'coe : (U' : Subgroup (StatedSL 2 K)) = (Q : Subgroup ↥A).map eA.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eA.toMonoidHom) (p := 2) (hf := eA.surjective) Q
  obtain ⟨d, hdN, hdord⟩ :=
    CFSG.ClassicalGroups.exists_orderOf_eq_card_sub_one_mem_normalizer_sylow_sl2 U'
  have hdA : eA.symm d ∈ Subgroup.normalizer ((U.subgroupOf A : Subgroup ↥A) : Set ↥A) := by
    have hmap := Subgroup.map_equiv_normalizer_eq ((U.subgroupOf A) : Subgroup ↥A) eA
    have hmem : d ∈ (Subgroup.normalizer ((U.subgroupOf A) : Subgroup ↥A)).map eA.toMonoidHom := by
      rw [hmap]
      have heq : (U.subgroupOf A).map eA.toMonoidHom = (U' : Subgroup (StatedSL 2 K)) := by
        rw [hU'coe, ← hQ]
      rw [heq]
      exact hdN
    exact Subgroup.mem_map_equiv.mp hmem
  have hbnorm : ((eA.symm d : ↥A) : Ω) ∈ Subgroup.normalizer (U : Set Ω) := by
    have hsub : eA.symm d ∈ (Subgroup.normalizer (U : Set Ω)).subgroupOf A := by
      rw [Subgroup.subgroupOf_normalizer_eq hU.le]
      exact hdA
    exact Subgroup.mem_subgroupOf.mp hsub
  have hborder : orderOf ((eA.symm d : ↥A) : Ω) = 7 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hdord, hK8]
  exact ⟨hElemU, hcardU, ⟨((eA.symm d : ↥A) : Ω), (eA.symm d).2, hbnorm, hborder⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

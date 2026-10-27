module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NThreePart
public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJType
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLinkFacts
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.Quasithin.Background.FFC2G2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)


theorem perfectResidual_g2_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    perfectResidual (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) =
        commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) ∧
      IsSimpleGroup (commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) ∧
      (commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)).index = 2 := by
  set Q := CFSG.Blueprint.Chevalley.adjointGroup .G2 K
  obtain ⟨eU⟩ := Item89Res2.nonempty_commutator_g2_two_mulEquiv hK
  have hUs : IsSimpleGroup (projSU 3 3 1) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 3 1 le_rfl (by norm_num)
  have hcs : IsSimpleGroup (commutator Q) := eU.isSimpleGroup
  have hnc : ∃ x y : commutator Q, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := (CFSG.Quasithin.FFC.commutator_data_g2 hK
      (Subgroup.topEquiv.trans
        (Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK).some)).2.1
    refine ⟨(MulEquiv.subgroupCongr (commutator_def Q)).symm x,
      (MulEquiv.subgroupCongr (commutator_def Q)).symm y, fun h' => hxy ?_⟩
    have := congrArg (MulEquiv.subgroupCongr (commutator_def Q)) h'
    simpa using this
  have hcp : Group.IsPerfect (commutator Q) :=
    Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
  exact ⟨Item89Res2.perfectResidual_eq_commutator hcp, hcs,
    Item8KFacts2Proof.index_commutator_g2_two hK⟩

variable {Q : Type} [Group Q] [Finite Q]

theorem isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one {R : Subgroup Q}
    (h : IsoGTwoEven R 1) : IsSimpleGroup (inSubgroup perfectResidual R) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨hres, hs, -⟩ := perfectResidual_g2_two hK2
  have e₁ : ↥(inSubgroup perfectResidual R) ≃*
      ↥(commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) :=
    ((perfectResidual ↥R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
      ((Item89Res2.perfectResidualEquiv e).trans (MulEquiv.subgroupCongr hres))
  haveI := hs
  exact e₁.isSimpleGroup

theorem card_eq_two_mul_card_inSubgroup_perfectResidual_of_isoGTwoEven_one {R : Subgroup Q}
    (h : IsoGTwoEven R 1) : Nat.card R = 2 * Nat.card (inSubgroup perfectResidual R) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨hres, -, hidx⟩ := perfectResidual_g2_two hK2
  have h1 : Nat.card (inSubgroup perfectResidual R) =
      Nat.card (commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) := by
    rw [show inSubgroup perfectResidual R = (perfectResidual ↥R).map R.subtype from rfl,
      Subgroup.card_map_of_injective R.subtype_injective]
    exact Nat.card_congr ((Item89Res2.perfectResidualEquiv e).trans
      (MulEquiv.subgroupCongr hres)).toEquiv
  rw [h1, Nat.card_congr e.toEquiv, ← Subgroup.card_mul_index
    (commutator (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)), hidx, mul_comm]

theorem normal_subgroupOf_inSubgroup_perfectResidual (R : Subgroup Q) :
    ((inSubgroup perfectResidual R).subgroupOf R).Normal := by
  have heq : (inSubgroup perfectResidual R).subgroupOf R = perfectResidual ↥R :=
    Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
  rw [heq]
  have := (CFSG.perfect_residual_characterization (G := ↥R)).2.1
  infer_instance

theorem factorization_card_inf_perfectResidual_of_isoGTwoEven_one {R : Subgroup Q}
    (h : IsoGTwoEven R 1) (S : Subgroup Q) :
    (Nat.card ↥(inSubgroup perfectResidual R ⊓ S)).factorization 3 =
      (Nat.card ↥(R ⊓ S)).factorization 3 := by
  have hNR : inSubgroup perfectResidual R ≤ R := Item87Proof.residual_le R
  have h1 := factorization_card_inf_of_card_eq_two_mul hNR
    (normal_subgroupOf_inSubgroup_perfectResidual R)
    (card_eq_two_mul_card_inSubgroup_perfectResidual_of_isoGTwoEven_one h)
    (inf_le_left : R ⊓ S ≤ R)
  rwa [← inf_assoc, inf_of_le_left hNR] at h1

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end

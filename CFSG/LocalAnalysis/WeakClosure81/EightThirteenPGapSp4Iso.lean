module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)
open CFSG.Assembly.LowTwoRank (StatedSp)

theorem exists_mulEquiv_statedSp_of_isSp4 {G : Type} [Group G] (h : IsSp4 G 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (G ≃* StatedSp 2 F) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := 2) (K := K)
  let g : StatedProj (StatedSp 2 K) ≃* StatedSp 2 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨K, inferInstance, inferInstance, by rw [hK]; norm_num, ⟨e.trans g⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.Timmesfeld.Transvection.ModelTransMul
public import CFSG.RankThree.GF2n.Tim79aRootTransport
public import CFSG.RankThree.GF2n.Tim79aSpRootS1
public import CFSG.Timmesfeld.Transvection.ModelSpCore
public import CFSG.RankThree.GF2n.Tim79aSpRootIrr
public import CFSG.Timmesfeld.Transvection.ModelSpRigid
public import CFSG.RankThree.GF2n.Tim79aSpRootS2

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank

theorem noTwoPowerStmt_holds (n : ℕ) (F : Type) [Field F] [CharP F 2] : NoTwoPowerStmt n F :=
  fun {_ _} hpq {_ _} hc hc' {_} hg k => ne_one_pow_two_pow_of_spTrans_mul hpq hc hc' hg k

theorem spCoreStmt_holds (n : ℕ) (F : Type) [Field F] [CharP F 2] [Finite F] :
    SpCoreStmt n F :=
  spCoreStmt_of_noTwoPower (noTwoPowerStmt_holds n F)

theorem spModelS1_holds : SpModelS1 := fun _ _ _ _ _ _ _ ha hT => rootS1Model_sp ha hT

theorem spModelIrr_holds : SpModelIrr := fun n F _ _ _ _ _ ha hT =>
  rootIrrModel_sp (spCoreStmt_holds n F) ha hT

theorem spModelS2_holds : SpModelS2 := fun n F _ _ _ _ _ ha hT =>
  rootS2Model_sp (spCoreStmt_holds n F) spRadCommStmt_holds (spMapTransStmt_holds n F)
    (spRigidStmt_holds n F) ha hT

theorem spModelInner_holds : SpModelInner := fun n F _ _ _ _ _ ha hT =>
  rootInnerModel_sp_of_s2 (spCoreStmt_holds n F) ha hT (spModelS2_holds n F _ _ ha hT)

theorem classicalRootSpS1Statement_holds : ClassicalRootSpS1Statement :=
  classicalRootSpS1Statement_of_model spModelS1_holds

theorem classicalRootSpIrrStatement_holds : ClassicalRootSpIrrStatement :=
  classicalRootSpIrrStatement_of_model spModelIrr_holds

theorem classicalRootSpS2Statement_holds : ClassicalRootSpS2Statement :=
  classicalRootSpS2Statement_of_model spModelS2_holds

theorem classicalRootSpInnerStatement_holds : ClassicalRootSpInnerStatement :=
  classicalRootSpInnerStatement_of_model spModelInner_holds

end CFSG.RankThree.GF2n.Tim79a

module

public import CFSG.Quasithin.Vol2.Ch5Sec3L532Rig
public import CFSG.Quasithin.Vol2.Ch5Sec3L532Ext
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Rec
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4

public section

namespace CFSG.Quasithin.H13.L532

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

theorem modelAt_f4 :
    ModelAt .twistedF4 0 := by
  intro Y _ f hpar hY
  have oct : ∀ (K : Type) [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
      (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1)), 1 ≤ a → TwoF4.OctInput K a hK :=
    fun K _ _ _ a hK ha =>
      haveI := TwoF4.isSimpleGroup_gm ha hK
      TwoF4.octInputOf hK (TwoF4.octRGD2 hK)
  have hm := TwoF4.f431ModelFacts_f4 f
  refine ⟨(hm Y hY).1, (hm Y hY).2, fun TY P₁ P₂ hpair => ⟨?_, ?_⟩⟩
  · exact ((Sec53F.lieModelFacts_f4 Y f hpar hY).2 TY P₁ P₂ hpair).2.1
  · exact amalgamRigid_of_f48 hm (TwoF4.f431Facts45_f4 f oct hm) (TwoF4.f431Generation_f4 f)
      (fun D _ hD A => Or.inl (TwoF4.cartanFPF_f4 f hm oct D hD A))
      (fun D _ hD A => TwoF4.faithfulOnType_f4 f hm oct D hD A _) Y hY hpair

theorem stmt5_3_2At_f4
    (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) : Stmt5_3_2At .twistedF4 0 :=
  stmt5_3_2At_of_modelAt h527 h531 modelAt_f4

end CFSG.Quasithin.H13.L532

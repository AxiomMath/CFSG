module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.S6
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Setting
public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Base
public import CFSG.Quasithin.Recognition.SzVBEvenSetting
public import CFSG.Quasithin.Recognition.SzVBS5Main

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem ctx_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S))
    (hb : 3 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) :
    ∃ z : G, Ctx (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) S (conjClosure Zs L2) z := by
  obtain ⟨z, hC⟩ := SzVB.exists_geoCtx_of_setting rankOneListedFacts h
  have hab : IsElemAbelian 2 (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    have := isElemAbelian_Vv_γ₁ hC.hyp (SzVB.V_ne_bot hC) (by omega)
    rwa [Vv_γ₁ hC.hyp.le₂ hC.hyp.normalizes] at this
  have hP := prim_of_setting h hL hA5 hab hC.klein
  exact ⟨z,
    { toGeoCtx := hC
      two_fixed := hP.two_fixed
      comm_big := hP.comm_big
      quad_pair := hP.quad_pair
      simple := simple_of_setting h hL hA5
      twin := twin_of_setting h }⟩

theorem vbOddL24FarA5_core (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S))
    (hb : 7 ≤ critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) :
    ¬ Odd (critDist (K1 ⊔ L2 ⊔ S) (L2 ⊔ S) (K1 ⊔ S) (conjClosure Zs L2)) := fun hodd => by
  obtain ⟨z, C⟩ := ctx_of_setting h hL hA5 (by omega)
  exact C.false_of_odd hb hodd

theorem vbOddL24FarA5_holds : SzVB.VBOddL24FarA5Statement := by
  intro G _ _ K1 L2 S Zs h hL hA5 _ hb
  exact vbOddL24FarA5_core h hL hA5 hb

end CFSG.Quasithin.Kleidman.VBOdd

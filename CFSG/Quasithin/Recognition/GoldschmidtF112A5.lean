module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RL34
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSp44
public import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
public import CFSG.Quasithin.Recognition.GoldschmidtF112RU42Ext
public import CFSG.Quasithin.Recognition.GoldschmidtF112RJ2
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyNorm
public import CFSG.GH74.QTGen4.U42.CentralExtB
public import CFSG.GH74.QTGen4.U42.ElemAb16
public import CFSG.GH74.QTGen4.U42.MSplitB
public import CFSG.GH74.QTGen4.U42.ModelP1
public import CFSG.GH74.QTGen4.U42.ModelPairCore
public import CFSG.Quasithin.Recognition.GoldschmidtF112ROmega4
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Psi
public import Certificates.Data.GF4

public section

namespace CFSG.Quasithin.F112R

@[expose] def F112SliceA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112Hyp L1 L2 S →
    (VA5 L1 ∧ VA5 L2) ∨ (VS3 L1 ∧ VA5 L2) ∨ (VA5 L1 ∧ VS3 L2) → F112ConclC L1 L2 S

theorem f112SliceA5_of_id
    (hA : IdA5A5) (hS : IdS3A5) : F112SliceA5 := by
  intro G _ _ L1 L2 S hF hp
  rcases hp with ⟨h1, h2⟩ | hp
  · exact f112ConclC_of_A5A5 hA y9L34 y9Sp44 y9G24 G L1 L2 S hF h1 h2
  · exact f112ConclC_of_A5S3_pair hS y9U42 y9J2 y9AutJ2 G L1 L2 S hF hp

end CFSG.Quasithin.F112R

end

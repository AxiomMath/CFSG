module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMap
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie

public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.Sec53F.BA

set_option linter.unusedSectionVars false


theorem borelAutData_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    BorelAutData (posUnipotentSub Tag.G2 K) (torusSub Tag.G2 K) (fieldAut K).range where
  center := g2_center
  sylow := g2_sylow
  H_comm := g2_H_comm
  H_le := g2_H_le
  U_inf_H := g2_U_inf_H
  B_eq := g2_B_eq
  F_U := g2_F_U
  F_H := g2_F_H
  F_comm := g2_F_comm
  F_faithful := g2_F_faithful
  normal_form := fun α hα => g2_normal_form hf hK α hα

theorem lieBorelFacts_g2 : LieBorelFacts .G2 0 := by
  intro Y _ _ f hpar hY U hU
  obtain ⟨-, hX⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hY
    (by decide)
  obtain ⟨hf, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hX
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  exact (borelAutData_g2 hf hK).exists_of_equiv e hU

theorem lieAutFacts_g2 : LieAutFacts .G2 0 :=
  lieAutFacts_of_lieBorelFacts lieBorelFacts_g2

end CFSG.Quasithin.H13.Sec53F.G2

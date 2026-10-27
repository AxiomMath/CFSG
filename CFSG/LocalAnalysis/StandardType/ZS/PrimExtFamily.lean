module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMain
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelF4
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH3
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH4
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelJ34

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem family_of_primExtSetting (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (S : PrimExtSetting G H d)
    (htab : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1)) (h19 : LemmaOneNineInput)
    (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) (hdeg : DegenerateInput p G 2)
    (h35 : TFDimThreeFive p) (hext : 5 ≤ Module.finrank (ZMod p) U → TFH4Extend p) :
    Family p G := by
  obtain ⟨hn, hd, hp5, α, f, hα, hG⟩ := S.exists_basis_eq_h4BlockMats hp htab h19 hneg hdeg h35
    hext tfH3Model_holds tfH3Pair_holds tfJ34Model_holds tfF4Model_holds tfH4Model5_holds
    tfH4Model_holds
  have hdmax : DMax p G 5 := hd ▸ S.dmax
  rw [hG] at hdmax ⊢
  exact Family.h4 hp5 hn (PrimModel.card_basisClosure_h4BlockMats hp hp5 f hα)
    (PrimModel.neg_mem_basisClosure_h4BlockMats hp hp5 f hα) hdmax
    (tfH4Model_holds U f α hp hp5 hα).1

end CFSG.StandardType.ZS

end

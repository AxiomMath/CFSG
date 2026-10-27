module

public import CFSG.Quasithin.Vol2.Ch12Sec6L30b
public import CFSG.Quasithin.Vol2.Ch12Sec6L30a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S126

theorem lemma12_6_30_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24)
    (h1227 : Lemma12_6_27) (h1229 : Lemma12_6_29) (h36 : Vol2Native.A36CoreForSQTKCat)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h133 : Vol2.Ch11.Tmp1_3_3) : Lemma12_6_30 := by
  intro G _ _ T L V _ F hH hZ
  refine ⟨fun H₂ hH₂ => S126L30.hypF98_of_inHz h1224 h1227 F hH hZ hH₂, fun H K hHK => ?_⟩
  obtain ⟨⟨H₁, hH₁, hK⟩, hKM, rfl⟩ := hHK
  have hq := S126L30.isQuasisimple_of_mem_cComp h331 h1222 h1229 h36 h133 F hH hZ hH₁ hK hKM
  exact ⟨S126L30.qInt_le_two h1224 h1227 F hH hZ
      (S126L30.inHz_of_isHK h1222 F hH hZ hH₁ hK hKM).1,
    S126L30.isQuasisimple_quot_pCoreOf' hq,
    S126L30.hypF918_of_isHK h1222 h1224 h1227 h37 h38 F hH hZ ⟨⟨H₁, hH₁, hK⟩, hKM, rfl⟩ hq⟩

end CFSG.Quasithin.H13

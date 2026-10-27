module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLLabelE
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLLabelT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section CertsZL


theorem ggE6DepZLKnown_holds : GGE6DepZLKnown := by
  intro lab hlab hΛ
  rcases hlab with ⟨htag, h3⟩ | ⟨htag, h3⟩
  · have key := largeEvenLabelAll_e6Div_of (P := fun R _ I => GGE6DepZLProp R I) htag hΛ h3
      (fun K _ _ n hn hK h3' => E6Dep.ZL.ggE6DepZLProp_E ggAbelianLift n hn hK h3')
    exact LargeEvenLabelAll.mono (fun R _ I F h _ _ => h.2) key
  · exact TwE6Delta.labelAll htag
      (Q := fun R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGE6DepZLProp R I)
      (fun K _ _ hK _ _ => E6Dep.ZL.ggE6DepZLProp_T hΛ.1 hK ggAbelianLift h3)

end CertsZL

end CFSG.StandardType

end

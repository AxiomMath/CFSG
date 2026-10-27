module

public import CFSG.RankThree.PartOne.KE.SuzukiOddImage
public import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.RankThree.PartOne.KE.SuzukiLangSp4

public section

namespace CFSG.RankThree.PartOne.KE

theorem suzukiLangStep : SuzukiLangStep := fun L _ _ _ b => antiSp_lang_aut L b

theorem suzukiPrimeFieldCosetDescent : SuzukiPrimeFieldCosetDescent :=
  suzuki_prime_field_coset_descent_of_lang suzukiLangStep

theorem suzuki_normalized_component_local_core_product_odd_image :
    SuzukiNormalizedComponentLocalCoreProductOddImage :=
  suzukiNormalizedComponentLocalCoreProductOddImage_of_descent suzukiPrimeFieldCosetDescent

end CFSG.RankThree.PartOne.KE

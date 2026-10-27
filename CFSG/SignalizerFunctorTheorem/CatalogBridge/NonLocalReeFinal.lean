module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSmallReeMain
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain

public section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem subfieldNonLocalizedSmallRee_of
    (h0 : SubfieldNonLocalizedSmallReeBZero) :
    SubfieldNonLocalizedSmallRee := by
  intro a ha K _ _ _ hK p hp hp3 σ hσ
  by_cases hpa : p = 2 * a + 1
  · exact h0 a ha K hK p hp hp3 hpa σ hσ
  · exact nonLocalized_smallRee_of_ne ha hK hp hp3 hpa σ hσ

theorem subfieldNonLocalizedLargeRee_of
    (h0 : SubfieldNonLocalizedLargeReeBZero) :
    SubfieldNonLocalizedLargeRee := by
  intro a ha K _ _ _ hK p hp hp3 σ hσ
  by_cases hpa : p = 2 * a + 1
  · exact h0 a ha K hK p hp hp3 hpa σ hσ
  · exact nonLocalized_largeRee_of_ne ha hK hp hp3 hpa σ hσ

end CFSG.SignalizerFunctorTheorem.CatalogBridge

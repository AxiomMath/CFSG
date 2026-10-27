module

public import CFSG.Quasithin.Background.F918Fine4PfHat7
public import CFSG.Quasithin.Background.F918Fine4PfM22

public section

namespace CFSG.Quasithin

namespace F918Fine4Pf

theorem f918Fine4_of
    (h310 : D310) (h391 : D391) : F918Fine4 :=
  fun _ _ _ _ _ _ _ _ _ _ h hH hK =>
    ⟨fun _ => not_isHat_alt7 h310 h391 h hH hK, m22_or_hat_of_quot h hK⟩

end F918Fine4Pf

end CFSG.Quasithin

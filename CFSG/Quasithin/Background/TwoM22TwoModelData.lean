module

public import CFSG.Quasithin.Background.TwoM22TwoModelOfGens
public import Certificates.Certificate664010

public section

namespace CFSG.Quasithin.TwoM22

open CFSG.Quasithin.TwoM22.Gens CFSG.Sporadic.Recognition.M22Multiplier


theorem twoM22Gen_snd (i : Fin 2) :
    MonoidHom.snd _ _ (twoM22Gen i) =
      ((m22Gen i : CFSG.Blueprint.NativeSporadic.M22) : Equiv.Perm (Fin 22)) := by
  fin_cases i <;> rfl

theorem isTwoM22TwoModel_twoM22 :
    IsTwoM22TwoModel twoM22M twoM22T := by
  obtain ⟨hrel, hζ, hζ2, hTT, hTconj, hTM, hcent, hS, hScard, hSsq⟩ :=
    Certificates.certificate664010
  exact isTwoM22TwoModel_of_gens twoM22Gen twoM22T (MonoidHom.snd _ _) twoM22Gen_snd hrel hζ hζ2
    hTT hTconj hTM hcent twoM22S hS hScard hSsq

end CFSG.Quasithin.TwoM22

module

public import CFSG.Quasithin.Background.F6CatInputs
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Recognition.CertR2aBridges
public import CFSG.Quasithin.Recognition.CertU33Wreath

public section

namespace CFSG.Quasithin

namespace F6

theorem g22PrimeSylowFact_holds
    : G22PrimeSylowFact := by
  intro W _ _ hW S
  obtain ⟨eW⟩ := isG22Prime_equiv W hW
  obtain ⟨ePres⟩ := u33Pres_mulEquiv_PSU3
  have : Finite U33G := u33Pres_finite_card_le.1
  obtain ⟨S', ⟨ι⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv (eW.trans ePres.symm) S
  obtain ⟨eT⟩ := u33_T_mulEquiv_wreathed
  exact ⟨ι.trans ((Sylow.equiv S' u33SylowT).trans eT)⟩

end F6

end CFSG.Quasithin

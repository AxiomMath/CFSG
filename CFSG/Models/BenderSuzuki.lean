module

public import CFSG.Open.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs

public section

namespace CFSG.Models

theorem benderSzModel_eq_sz (n : ℕ) : CFSG.Theory.Comparator.SzModel n = CFSG.Open.Sz n := by
  simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, CFSG.Open.Sz,
    CFSG.Open.SzGenerators]

theorem benderPSU3Model_eq_psu3 (n : ℕ) :
    CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
  rfl

end CFSG.Models

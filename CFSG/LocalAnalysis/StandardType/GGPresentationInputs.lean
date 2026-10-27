module

public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl
public import CFSG.LieType.Universal.Catalog
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

theorem ggStandardCopy_PSL (n f : ℕ) (hadm : StatedLieAdmissible .PSL n 2 f)
    (hrank : 3 ≤ bnRank .PSL n) : ∃ ν, GGStandardCopy (lieUniversal .PSL n 2 f hadm.1).D ν := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [bnRank] at hrank; omega⟩
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  exact ⟨slWeylLift m h2, slWeylLift_standardCopy m h2⟩

end CFSG.StandardType

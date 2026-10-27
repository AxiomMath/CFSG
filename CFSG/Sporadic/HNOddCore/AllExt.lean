module

public import CFSG.Sporadic.HNOddCore.OddD
public import CFSG.Sporadic.HNOddCore.Fusion
public import Certificates.Certificate2083
public import Certificates.Certificate2084
public import Certificates.Certificate2086
public import Certificates.Certificate2087
public import Certificates.Certificate2088
public import Certificates.Certificate2089
public import Certificates.Certificate2091
public import Certificates.Certificate2093
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

theorem ctuc_hn_all_extension_involution_centralizers_odd_core_trivial :
    (∀ t : JH, t ^ 2 = 1 → t ≠ 1 →
      CFSG.oddCore (Subgroup.centralizer ({t} : Set JH)) = ⊥ ∧
        CFSG.oddCore (Subgroup.centralizer ({jR t} : Set RH)) = ⊥) ∧
    ∀ t : RH, t ^ 2 = 1 → t ≠ 1 → IsOuter t →
      CFSG.oddCore (Subgroup.centralizer ({t} : Set RH)) = ⊥ := by
  refine ⟨fun t h2 h1 => ?_, fun t h2 h1 hout => ?_⟩
  · have h2' : (jR t) ^ 2 = 1 := by rw [← map_pow, h2, map_one]
    have h1' : jR t ≠ 1 := fun e => h1 (jR_injective (e.trans (map_one jR).symm))
    rcases involution_cover_R h2' h1' with hc | hc | hc
    · exact absurd hc (not_isConj_c_jR t)
    · have hJ := isConj_J_of_R t2J_sq t2J_ne_one hc
      exact ⟨oddCore_centralizer_of_isConj hJ oddCore_C2,
        oddCore_centralizer_of_isConj hc oddCore_CR_t2⟩
    · have hJ := isConj_J_of_R t4J_sq' t4J_ne_one hc
      exact ⟨oddCore_centralizer_of_isConj hJ (oddCore_CJ_of_CR oddCore_CR_t4),
        oddCore_centralizer_of_isConj hc oddCore_CR_t4⟩
  · rcases involution_cover_R h2 h1 with hc | hc | hc
    · exact oddCore_centralizer_of_isConj hc oddCore_CR_c
    · exact absurd ((isOuter_of_isConj hc).2 hout) (not_isOuter_jR t2J)
    · exact absurd ((isOuter_of_isConj hc).2 hout) (not_isOuter_jR t4J)

end CFSG.Sporadic.HNOddCore

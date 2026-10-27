module

public import CFSG.Quasithin.Recognition.CertTwoF4Outer
public import Certificates.Certificate7092
public import CFSG.Quasithin.Recognition.RuRank3Tits13Base

public section

namespace CFSG.Quasithin.RuType

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

theorem twoF4M_eq_titsA :
    twoF4M = CFSG.Sporadic.Schreier.Tits.titsA := by
  have hπ : tπ ∈ CFSG.Sporadic.Schreier.Tits.titsA :=
    RuRank3.mem_titsA_of_inTitsA tπ_rep Certificates.certificate7092
  have hle : twoF4M ≤ CFSG.Sporadic.Schreier.Tits.titsA := by
    intro x hx
    have hx' : x ∈ titsD ∨ x * tπ⁻¹ ∈ titsD := hx
    rcases hx' with h | h
    · exact titsD_le_titsA h
    · have := mul_mem (titsD_le_titsA h) hπ
      rwa [inv_mul_cancel_right] at this
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  norm_num [card_titsA, card_twoF4M, card_titsD]

end CFSG.Quasithin.RuType

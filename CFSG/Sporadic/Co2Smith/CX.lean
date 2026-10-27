module

public import CFSG.Sporadic.Co2Smith.CCFacts

public section

namespace CFSG.Sporadic.Co2Smith

theorem c3_facts
    (hc : CCFacts) :
    ∃ w : Cz, w ∈ CFSG.pCore 2 Cz ∧ w ≠ 1 ∧ w * cR 8 = cR 8 * w ∧
      (∃ h : Cz, h * (cR 8 * w) * h⁻¹ = cR 8) ∧
      ∀ hw : w ∈ XC 8, ∀ α : XC 8 ≃* XC 8, α ⟨w, hw⟩ = ⟨w, hw⟩ :=
  hc.c3

end CFSG.Sporadic.Co2Smith

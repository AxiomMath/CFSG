module

public import CFSG.Quasithin.H13.LocDblRuCoverInputs
import Certificates.Kernel.Ru7032.Cover

public section

namespace Certificates

open CFSG.Quasithin.H13.LocDbl.RuCov CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate7032 :
    Nat.card ruS = 2 ^ 14 ∧ ruS ≤ ruVA ∧ ruS ≤ ruVB ∧
      Nat.card ruVA = 245760 ∧ Nat.card ruVB = 344064 ∧
      (∀ Y : Subgroup (CFSG.Sporadic.SmallF2.J ruData), ruS ≤ Y → Y ≠ ⊤ → Y ≤ ruVA ∨ Y ≤ ruVB) ∧
      ∀ g : CFSG.Sporadic.SmallF2.J ruData,
        g ∈ ruVA ∨ g ∈ ruVB ∨ ∃ w ∈ ruTopW, ∃ s ∈ ruS, ∃ t ∈ ruS, g = s * ruWord w * t := CFSG.KD.Ru7032.cover

end Certificates

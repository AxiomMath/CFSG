module

public import Certificates.Kernel.Co1B.Tow2045L0
public import Certificates.Kernel.Co1B.Tow2045L1
public import Certificates.Kernel.Co1B.Tow2045L2
public import Certificates.Kernel.Co1B.Tow2045L3
public import Certificates.Kernel.SporSch.Co1.Packed
public import CFSG.Certificates.Kernel.SporSch.Co1CentSound
public import CFSG.Sporadic.Co1Block.TwoBData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.Co1AutCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Cent2045

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CertificateChecks.KernelSporSch.Co1Packed

theorem kb0 : Nat.beq (D1.M 0) PA = true := by quickRfl
theorem kb1 : Nat.beq (D1.M 1) PB = true := by quickRfl
theorem kb2 : Nat.beq (D1.M 2) PA = true := by quickRfl
theorem kD1 : dagIK D1.M D1.MI 3 43 twoBD1 = true := by quickRfl
theorem kBind : bindK D1.M D2.M twoBBray = true := by quickRfl
theorem kD2 : dagIK D2.M D2.MI 10 22 twoBD2 = true := by quickRfl
theorem kC : commK D1.M PA twoBBray = true := by quickRfl
theorem kI : twoBBray.all (fun j => decide (3 < j) && decide (j ≤ 43)) = true := by quickRfl

theorem f0 : fixesK D2.M (twoBVGens.getD 0 []) twoBVBase 0 = true := by quickRfl
theorem f1 : fixesK D2.M (twoBVGens.getD 1 []) twoBVBase 1 = true := by quickRfl
theorem f2 : fixesK D2.M (twoBVGens.getD 2 []) twoBVBase 2 = true := by quickRfl
theorem f3 : fixesK D2.M (twoBVGens.getD 3 []) twoBVBase 3 = true := by quickRfl

theorem base_eq : [aR, bR, aR] = (List.range 3).map fun i => unpack 24 24 (D1.M i) := by
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_cons, List.map_nil, aR_u, bR_u,
    Nat.eq_of_beq_eq_true kb0, Nat.eq_of_beq_eq_true kb1, Nat.eq_of_beq_eq_true kb2]

theorem twoB_cent_check : centCheckOf aR twoBD1 twoBBray twoBD2 twoBVBase twoBVGens
    twoBVSizes = true := by
  refine centCheckOf_of_K (P := PA) aR_u base_eq kD1 kI kBind kD2 kC ?_ ?_
  · intro i hi
    have : i < 4 := by simpa [twoBVBase] using hi
    interval_cases i <;> decide
  · intro i hi
    have : i < 4 := by simpa [twoBVBase] using hi
    interval_cases i
    · exact ⟨_, _, _, _, _, 512, TW0.hd0, TW0.hc0, TW0.hn0, by decide, TW0.hl0, TW0.hp0, f0⟩
    · exact ⟨_, _, _, _, _, 512, TW1.hd0, TW1.hc0, TW1.hn0, by decide, TW1.hl0, TW1.hp0, f1⟩
    · exact ⟨_, _, _, _, _, 512, TW2.hd0, TW2.hc0, TW2.hn0, by decide, TW2.hl0, TW2.hp0, f2⟩
    · exact ⟨_, _, _, _, _, 512, TW3.hd0, TW3.hc0, TW3.hn0, by decide, TW3.hl0, TW3.hp0, f3⟩

end CertificateChecks.KernelCo1B.Cent2045

end

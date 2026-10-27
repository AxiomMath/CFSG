module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzE
import Certificates.Kernel.S1277.C7255Chk
import Certificates.Kernel.S1277.NmFacts
import CFSG.Certificates.Kernel.S1277K7255Sound
import CFSG.Certificates.Kernel.S1277K7213Sound
public import Aesop.BuiltinRules
import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 100000

namespace Certificates

open CFSG.Quasithin.H13.S127.Mod

open CFSG.Quasithin.H13.S127.Mod in
theorem certificate7255 :
    (∀ c ∈ p1c, c ≠ 0 → (stabC1 c).length ≤ 8) ∧
    (∀ l ∈ perms6, ∀ b < 7, cycOK b (fl l) = true → cycMoved b (fl l) = true →
      l = List.finRange 6) := by
  refine ⟨fun c hc h0 => ?_, CFSG.KS.C7255.cyc_sound CFSG.KP.C7255.cyc7255⟩
  have hs := CFSG.KP.C7255.stab7255
  have hc' : c ∈ [5, 10, 15] := by
    simp only [p1c, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> simp_all
  exact CFSG.KS.C7255.stab_sound _ CFSG.KP.S1277ML.nm6_eqP c
    ((CFSG.KS.C7213.allL_iff _ _).1 hs c hc')

end Certificates

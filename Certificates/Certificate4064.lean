module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterE
import Certificates.Kernel.LocalQT.HSAutO.F4064

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.HSAut in
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native in
theorem certificate4064 : (allBelow 4 fun l => CFSG.Sporadic.SmallOddCore.permOK 3850 (qGenT l) &&
      (qGenT l).size == 3850) = true ∧
    CFSG.QuasithinUnique.Id2519.HSAut.qPerm 1 ∉ CFSG.QuasithinUnique.Id2519.HSAut.outerE ∧
    ∃ ρ : CFSG.QuasithinUnique.Id2519.HSAut.outerE →* Equiv.Perm (Fin 35), Nat.card ρ.range = 20160 ∧
      ∃ e : Fin classSizes.size ≃ ConjClasses ρ.range,
        (∀ l, Nat.card (e l).carrier = classSizes[l.val]!) ∧
        ∃ l₀ : Fin classSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 :=
  CFSG.KD.LQT.HO.outer_facts

end Certificates

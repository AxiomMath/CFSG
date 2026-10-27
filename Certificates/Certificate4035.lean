module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Aut6Inputs
import Certificates.Kernel.LocalQT.Small.C4035P

public section

namespace Certificates

open CFSG.KD.LQT.C4035 CFSG.QuasithinUnique.A5.Aut6 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Aut6 in
open Equiv in
theorem certificate4035 : (∀ x y : A6, IsCand CFSG.QuasithinUnique.A5.Aut6.word x y → IsInv CFSG.QuasithinUnique.A5.Aut6.word x y →
          ¬ CFSG.QuasithinUnique.A5.Aut6.IsConj CFSG.QuasithinUnique.A5.Aut6.word x y → HasFix CFSG.QuasithinUnique.A5.Aut6.word x y)
    ∧ (∀ g : A6, ev ga gb (CFSG.QuasithinUnique.A5.Aut6.word (g : CFSG.QuasithinUnique.A5.Aut6.P6)) = (g : CFSG.QuasithinUnique.A5.Aut6.P6)) :=
  CFSG.KC.LQT.X6.s4035k wordTab R ha hb hk hp

end Certificates

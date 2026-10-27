module

public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Certificate114

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint.Chevalley

@[expose] def levTab : ℕ :=
  0x41313111331131331131133212331123212223311232222223312222222223122222232222222

@[expose] def lev (k : ℕ) : ℕ := (levTab >>> (4 * k)) % 16

variable (R : Type*) [CommRing R]

@[expose] noncomputable def eLab (k : Fin 78) :
    RootModule Tag.E6 R :=
  Finsupp.single (lab k) 1

@[expose] noncomputable def xOne (v y : RootModule Tag.E6 R) : RootModule Tag.E6 R :=
  y + bracket R v y + form R v y • v

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

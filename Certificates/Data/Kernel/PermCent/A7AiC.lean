module

public import Certificates.Data.Kernel.PermCent.F7Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeA7Inputs

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.A7Ai

@[expose] noncomputable def c1P : CV 7 := cOf c1

@[expose] noncomputable def c2P : CV 7 := cOf c2

@[expose] noncomputable def e9P : List (CV 7) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => c1P ^ i * c2P ^ j

@[expose] noncomputable def e9PP : List (CV 7 × CV 7) := e9P.map fun z => (z, z⁻¹)

@[expose] noncomputable def vP : List (CV 7) := vInv.map cOf

@[expose] noncomputable def cy1P : List (CV 7) := [1, c1P, c1P ^ 2]

@[expose] noncomputable def cy2P : List (CV 7) := [1, c2P, c2P ^ 2]

@[expose] noncomputable def p16P (V : List (CV 7)) : List (CV 7 × CV 7) :=
  (V.flatMap fun t => V.map fun v => (t, v)).filter fun p => powOneC (p.1 * p.2) 16

@[expose] noncomputable def a7aiAB (E : List (CV 7 × CV 7)) (V : List (CV 7)) : Bool :=
  (allPermsP 7 inferInstance).all fun x =>
    !(powOneC x.1 2 && !powOneC x.1 1) || memC x.1.1 V ||
      E.any fun z => !powOneC (x.1 * (z.1 * x.1 * z.2)) 16

@[expose] noncomputable def badGB (E : List (CV 7 × CV 7)) (C1 C2 : List (CV 7)) (c1 c2 g : CV 7) :
    Bool :=
  ((E.any fun e => eq22C g c1 e.1 g) && !C1.any fun e => eq22C g c1 e g) ||
    ((E.any fun e => eq22C g c2 e.1 g) && !C2.any fun e => eq22C g c2 e g)

@[expose] noncomputable def a7aiBB (E : List (CV 7 × CV 7)) (C1 C2 : List (CV 7)) (c1 c2 : CV 7)
    (P : List (CV 7 × CV 7)) : Bool :=
  (allPermsP 7 inferInstance).all fun x =>
    !badGB E C1 C2 c1 c2 x.1 || P.all fun p => !eq22C x.1 p.1 p.2 x.1

@[expose] noncomputable def a7aiAF : Bool :=
  forceQL e9PP fun E => forceCL vP fun V => a7aiAB E V

@[expose] noncomputable def a7aiBF : Bool :=
  forceQL e9PP fun E => forceCL cy1P fun C1 => forceCL cy2P fun C2 => forceC c1P fun c1 =>
    forceC c2P fun c2 => forceCL vP fun V => forceQL (p16P V) fun P => a7aiBB E C1 C2 c1 c2 P

end CFSG.Certificates.Kernel.PkCV

end

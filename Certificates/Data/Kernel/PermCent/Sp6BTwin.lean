module

public import Certificates.Data.Kernel.PermCent.SmallB
public import Certificates.Data.TwinE4Sp62S
public import Certificates.Data.E4Sp6TwinPerf

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6B

open CFSG.EvenSmallLie.Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] noncomputable def sqRootsC (r : CV 36) (E : List (CV 36)) : List (CV 36) :=
  E.filter fun x => decide (x * x = r)

@[expose] noncomputable def sqStepC (S : List (CV 36)) (s : CV 36) : Bool :=
  S.all (fun x => decide (x * s = s * x)) ||
    let X := S.filter fun x => decide (x * s = s * x)
    X.all fun x => X.all fun y => !decide (y * x * y⁻¹ = x⁻¹)

@[expose] noncomputable def sqCheckC (r : CV 36) (E : List (CV 36)) : Bool :=
  let S := sqRootsC r E
  S.isEmpty || E.all fun s => !decide (s * s = 1) || sqStepC S s

@[expose] noncomputable def sq1C : Bool := sqCheckC (cOf sp6Rep1) (elemsC sp6CentQ1)

@[expose] noncomputable def sq2C : Bool := sqCheckC (cOf sp6Rep2) (elemsC sp6CentQ2)

@[expose] noncomputable def sq3C : Bool := sqCheckC (cOf sp6Rep3) (elemsC sp6CentQ3)

@[expose] noncomputable def sq4C : Bool := sqCheckC (cOf sp6Rep4) (elemsC sp6CentQ4)

@[expose] noncomputable def G : List (CV 36) := sp6Gens.map cOf

@[expose] noncomputable def wsC : List (CV 36) := memberWords.map (evCodesB G)

@[expose] noncomputable def L0C : List (CV 36) :=
  let r := cOf sp6Rep2
  let i := cOf (rho ())
  let j := cOf (jay ())
  [1, r, i, i * r, j, j * r, i * j, i * j * r]

@[expose] noncomputable def L1C : List (CV 36) :=
  L0C.map fun y => wsC.getD 11 1 * y * (wsC.getD 11 1)⁻¹

@[expose] noncomputable def commAllC (g : CV 36) (l : List (CV 36)) : Bool :=
  l.all fun x => decide (g * x = x * g)

@[expose] noncomputable def memberElemsC (L : List (CV 36)) (w : CV 36) : List (CV 36) :=
  L.map fun q => w * q * w⁻¹

@[expose] noncomputable def ordThreeC (c : CV 36) : Bool := !decide (c = 1) && decide (c * c * c = 1)

@[expose] noncomputable def layC : List (CV 36) :=
  let L := L0C
  let W := wsC
  let C8 := (elemsC sp6CentQ2).filter fun g => commAllC g L && commAllC g L1C
  C8.filter fun c => !decide (c = 1) &&
    !((List.range W.length).all fun k => k == 0 || k == 11 || !commAllC c (memberElemsC L (W.getD k 1)))

@[expose] noncomputable def twinLayC : Bool :=
  let L := L0C
  let W := wsC
  let lay := layC
  lay.all fun a => lay.all fun b => decide (a = b) ||
    (List.range W.length).any fun k =>
      commAllC a (memberElemsC L (W.getD k 1)) &&
        (memberElemsC L (W.getD k 1)).any fun z => ordThreeC (z * b * z⁻¹ * b⁻¹)

@[expose] noncomputable def twinPerfC : Bool :=
  let L := L0C
  let W := wsC
  let lay := layC
  !lay.isEmpty &&
    lay.all fun c => (List.range W.length).all fun k =>
      !commAllC c (memberElemsC L (W.getD k 1)) ||
        (memberElemsC L (W.getD k 1)).all fun x => perfWords.any fun e =>
          e.getD 0 0 == k && commAllC c (memberElemsC L (W.getD (e.getD 1 0) 1)) &&
            commAllC c (memberElemsC L (W.getD (e.getD 2 0) 1)) &&
            (memberElemsC L (W.getD (e.getD 1 0) 1)).any fun y =>
              (memberElemsC L (W.getD (e.getD 2 0) 1)).any fun z => decide (y * z * y⁻¹ * z⁻¹ = x)

end CFSG.Certificates.Kernel.PkCV.Sp6B

end

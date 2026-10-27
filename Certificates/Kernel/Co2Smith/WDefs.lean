module

public import Certificates.Kernel.Co2Smith.Elems
public import Certificates.Kernel.Co2Smith.CoxData
public import CFSG.Sporadic.Co2Smith.GlWInputs

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def nbK (i : Nat) : Nat := wK LP glNJB[i]!

@[expose] noncomputable def jcK (m : Nat) : Nat :=
  (List.range 10).foldr (fun i acc => if m.testBit i then mulV (nbK i) acc else acc) IDP

@[expose] noncomputable def genK (k : Nat) : Nat := if k == 0 then zK else TP (k - 1)

@[expose] noncomputable def w7K (k : Nat) : Nat := if k == 6 then d1K else genK k

@[expose] noncomputable def whK : Nat := wK genK glWh

@[expose] noncomputable def whiK : Nat := wK genK glWh.reverse

@[expose] noncomputable def whConjK (X : Nat) : Nat := mulV (mulV whiK X) whK

@[expose] noncomputable def tabWK (g : Nat) (tab : List Nat) : Bool :=
  tab.length == 10 && (List.range 10).all fun i =>
    decide (tab[i]! < 1024) && eqK (mulV g (nbK i)) (mulV (jcK tab[i]!) g)

@[expose] noncomputable def wJcK : Bool :=
  glNJB.size == 10 && glNJB.toList.all (fun w => w.all (· < 22)) &&
    (List.range 10).all fun i =>
      eqK (mulV (nbK i) (nbK i)) IDP && commK (nbK i) zK &&
        (List.range 10).all fun j => commK (nbK i) (nbK j)

@[expose] noncomputable def wTabsK : Bool :=
  glWTabs.size == 4 && tabWK d1K glWTabs[0]! && tabWK alK glWTabs[1]! &&
    tabWK gaK glWTabs[2]! && tabWK d0K glWTabs[3]!

@[expose] noncomputable def wE1K : Bool :=
  glWE1c.length == 4 && glWE1ic.length == 4 && glWE1w.size == 4 && glWE1iw.size == 4 &&
    (List.range 4).all fun j =>
      decide (glWE1c[j]! < 1024) && decide (glWE1ic[j]! < 1024) &&
        glWE1w[j]!.all (· < 6) && glWE1iw[j]!.all (· < 6) &&
        eqK (jcK glWE1c[j]!) (wK genK glWE1w[j]!) &&
        eqK (jcK glWE1ic[j]!) (wK genK glWE1iw[j]!) &&
        eqK (mulV d1K (jcK glWE1c[j]!)) (mulV (jcK glWE1ic[j]!) d1K)

@[expose] noncomputable def wD0K : Bool := glWD0.all (· < 6) && eqK (wK genK glWD0) d0K

@[expose] noncomputable def whOKK : Bool :=
  glWh.all (· < 6) && commK whK d1K && commK whK x25K && eqK (mulV whK whiK) IDP

@[expose] noncomputable def wbK : Bool :=
  glWbJ.length == glWbJh.size &&
    (List.range glWbJ.length).all (fun k =>
      decide (glWbJ[k]! < 1024) && tabWK (whConjK (jcK glWbJ[k]!)) glWbJh[k]!) &&
    glWbQ.size == glWbQt.size && glWbQ.size == glWbQh.size &&
    (List.range glWbQ.size).all fun k =>
      glWbQ[k]!.all (· < 9) && commK (wK LP glWbQ[k]!) zK &&
        commK (wK LP glWbQ[k]!) x25K && tabWK (wK LP glWbQ[k]!) glWbQt[k]! &&
        tabWK (whConjK (wK LP glWbQ[k]!)) glWbQh[k]!

@[expose] noncomputable def we2K (j : Nat) : Nat := mulV (mulV whK (jcK glWE1c[j]!)) whiK

@[expose] noncomputable def dcK : List Nat :=
  glWitZ0.flatMap fun e₀ => glWitZ1.flatMap fun e₁ => glWitZ2.map fun e₂ =>
    mulV (mulV (wK LP e₀.2) (wK LP e₁.2)) (wK LP e₂.2)

@[expose] noncomputable def filterK : Bool :=
  dcK.all fun R =>
    !(commK R x25K && (List.range glWbJ.length).all (fun k => commK R (jcK glWbJ[k]!)) &&
        (List.range glWbQ.size).all (fun k => commK R (wK LP glWbQ[k]!))) ||
      (List.range 4).all fun j => commK R (we2K j)

@[expose] noncomputable def wr0K : Bool :=
  glWr0.all (· < 7) && eqK (wK w7K glWr0) (wK LP (glMkRWord 16))

@[expose] noncomputable def wInjK : Bool :=
  glWInj.length == 20 && (List.range 20).all fun i =>
    decide (glWInj[i]! < 36) &&
      commK (wK LP (glMkRWord glWInj[i]!)) (mulV (wK LP (glMkRWord (i + 16))) zK)

@[expose] noncomputable def wRelK : Bool :=
  glWRelsN.all fun w => w.all (· < 7) && eqK (wK w7K w) IDP

end CertificateChecks.KernelCo2Smith

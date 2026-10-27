module

public import Certificates.Kernel.Co2Smith.Elems
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.Sporadic.Co2Smith.GlDataRootInputs

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native
open CFSG.KS.Co2M CertificateChecks.KernelSporSch.Co2M

@[expose] noncomputable def mapsK (A x y : Nat) : Bool :=
  colAct (Array.ofFn (n := 22) fun i => A / 2 ^ (22 * i.val) % 2 ^ 22) (VG (PV 0) x) ==
    VG (PV 0) y

@[expose] noncomputable def rootParK : Bool :=
  (List.range 12).all fun r => [1, 2, 3].all fun t =>
    [1, 2, 3].all (fun s => eqK (mulV (rootK r s) (rootK r t)) (rootK r (s ^^^ t))) &&
    eqK (mulV (mulV (mulV alK alK) (rootK r t)) alK) (rootK r (f4mul glRootChar[r]! t)) &&
    eqK (cjK gaK (rootK r t)) (rootK r (f4mul t t))

@[expose] noncomputable def rootCommK : Bool :=
  (List.range 18).all fun a => (List.range 18).all fun b =>
    a == b || glOpp a b || (glParams a).all fun s => (glParams b).all fun t =>
      eqK (comm4K (rootK a s) (rootK b t)) (prodK (glCommLookup a b s t))

@[expose] noncomputable def chartK : Bool :=
  (List.range 12).all (fun r => (List.range 6).all fun k =>
    decide (glChartCoord r k < 0) || [1, 2, 3].all fun t => commK (rootK r t) (longK k)) &&
  (List.range 6).all fun k => eqK (mulV (frameConjK k) (longK k)) (mulV zK (frameConjK k))

@[expose] noncomputable def uOKK : Bool :=
  [1, 2, 3].all (fun t =>
    eqK (comm4K uK (rootK 2 t)) (rootK 0 (f4mul t t)) &&
    eqK (comm4K uK (rootK 3 t)) (mulV (mulV zK (rootK 0 t)) (rootK 1 (f4mul t t))) &&
    eqK (comm4K uK (rootK 5 t)) (rootK 0 t)) &&
  [0, 1, 4].all (fun r => [1, 2, 3].all fun t => commK uK (rootK r t)) &&
  [12, 13, 14].all (fun r => commK uK (rootK r 1)) &&
  (List.range 18).all fun r => (glParams r).all fun t => mapsK (rootK r t) 80 80

@[expose] noncomputable def frameK : Bool :=
  (List.range 6).all (fun k => eqK (mulV (longK k) (longK k)) IDP) &&
    (List.range 3).all (fun i => eqK (powK (mulV (longK i) (longK (i + 3))) 3) IDP) &&
    (List.range 6).all (fun k => (List.range 6).all fun l =>
      k % 3 == l % 3 || commK (longK k) (longK l)) &&
    eqK (mulV d0K d0K) IDP && eqK (mulV d1K d1K) IDP &&
    eqK (powK (mulV d0K d1K) 3) IDP &&
    commK d0K zK && commK d0K x61K && commK d1K x34K && commK d1K x43K

end CertificateChecks.KernelCo2Smith

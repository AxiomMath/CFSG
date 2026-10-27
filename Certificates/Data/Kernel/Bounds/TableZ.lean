module

public import Certificates.Data.Kernel.Bounds.TableFact
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.Certificates.KB.ZChecks

open CFSG.Certificates.KB.Checks

meta def thm (D : Name) (h : Header) (wf : Array Nat) (nZ LM QM : Nat) (t : Nat) : String × Expr :=
  let c := fun (s : String) => mkConst (D ++ s.toName)
  let eps := h.get "EPS"; let nLab := h.get "nLab"; let nT := h.get "nT"
  let RW := h.get "RW"; let nW := h.get "nWords"; let nR := h.get "R"
  let nF := nT + h.get "nWalk"
  let RM := (1 <<< RW) - 1
  let nTC := (nT + 299) / 300
  let nVC := (nW + 499) / 500
  let nWE := wf.size - 1
  if t < nTC then
    (s!"tree{t}", mkAppN (kb "zTree0") #[c "Lab", lit (300 * t), lit (min 300 (nT - 300 * t))])
  else if t < nTC + nVC then
    let k := t - nTC
    (s!"vals{k}", mkAppN (kb "zVals")
      #[c "Wd", c "Val", lit h.inv, lit eps, lit nZ, lit (500 * k), lit (min 500 (nW - 500 * k))])
  else if t < nTC + nVC + nWE then
    let j := t - nTC - nVC
    let el := c s!"wl{j / perPart}.c{j % perPart}"
    (s!"walk{j}", beqE (mkAppN (kb "zWalkList")
      #[c "Lab", c "Quo", c "Val", c "Wd2", lit RW, lit RM, lit LM, lit QM, el, lit wf[j]!])
      (lit wf[j + 1]!))
  else
    ("piv", mkApp2 (kb "andB") (mkAppN (kb "zPivs")
      #[c "F", c "Lab", c "R", c "Zt", lit RW, lit RM, lit LM, lit QM, lit nLab, lit nR, lit nZ,
        lit nF]) (mkAppN (kb "zInv") #[c "Zt", lit LM, lit QM, lit nZ]))

meta def total (h : Header) (wf : Array Nat) : Nat :=
  (h.get "nT" + 299) / 300 + (h.get "nWords" + 499) / 500 + (wf.size - 1) + 1

end CFSG.Certificates.KB.ZChecks

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.ZChecks in
elab "#kz_checks " p:ident "include_bytes" path:str size:num hash:num nZ:num LM:num QM:num m:num :
    command => do
  let b ← CFSG.Certificates.KB.Load.readPinned path.getString size.getNat hash.getNat
  let h := parseHeader b
  let P := p.getId
  let D := `CFSG.KBData ++ P
  let wf := scan (h.get "nT") (h.fields.getD "walkElems" #[])
  unless wf.back! == h.get "nT" + h.get "nWalk" do
    throwError "header {path.getString}: element sizes do not sum to nWalk"
  let tot := total h wf
  let lo := 2000 * m.getNat
  let hi := min tot (lo + 2000)
  if hi ≤ lo then throwError "module {m.getNat} is past the {tot} label checks of {P}"
  for t in [lo:hi] do
    let (nm, e) := thm D h wf nZ.getNat LM.getNat QM.getNat t
    let name := `CFSG.KZCheck ++ P ++ nm.toName
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)
    CFSG.Certificates.KB.Load.withSync <| CFSG.KC.addThmDecl <|
      { name, levelParams := [], type, value := reflBoolTrue }

end

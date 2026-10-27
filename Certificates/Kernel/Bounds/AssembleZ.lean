module

public import Certificates.Data.Kernel.Bounds.TableZ
public import Certificates.Kernel.Bounds.Assemble
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.Certificates.KB.AssembleZ

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.Cert CFSG.Certificates.KB.Assemble

meta def zokOf (ns T P : Name) (h : Header) (nZ LM QM : Nat) : Expr × Expr :=
  let D := `CFSG.KBData ++ P
  let d := fun (s : String) => mkConst (D ++ s.toName)
  let chk := fun (s : String) => mkConst (`CFSG.KZCheck ++ P ++ s.toName)
  let eps := h.get "EPS"; let nLab := h.get "nLab"; let nT := h.get "nT"
  let RW := h.get "RW"; let nW := h.get "nWords"; let nR := h.get "R"
  let nF := nT + h.get "nWalk"
  let RM := (1 <<< RW) - 1
  let wf := scan nT (h.fields.getD "walkElems" #[])
  let nTC := (nT + 299) / 300
  let nVC := (nW + 499) / 500
  let tree :=
    if nTC = 0 then reflBoolTrue
    else (sliceTree 300 nT (fun k => chk s!"tree{k}")
      (fun k0 a b p1 p2 => mkAppN (mkConst (kbc "zTree0_step")) #[d "Lab", lit k0, lit a, lit b, p1, p2])
      0 nTC).1
  let vals :=
    if nVC = 0 then reflBoolTrue
    else (sliceTree 500 nW (fun k => chk s!"vals{k}")
      (fun k0 a b p1 p2 => mkAppN (mkConst (kbc "zVals_step"))
        #[d "Wd", d "Val", lit h.inv, lit eps, lit nZ, lit k0, lit a, lit b, p1, p2]) 0 nVC).1
  let nWE := wf.size - 1
  let nilE := mkApp (mkConst ``List.nil [Level.zero]) natT
  let (walkL, walk) :=
    if nWE = 0 then (nilE, reflBoolTrue)
    else listTree D "wl" wf (fun j => chk s!"walk{j}")
      (fun l1 l2 x y z p1 p2 => mkAppN (mkConst (kbc "zwalk_step"))
        #[d "Lab", d "Quo", d "Val", d "Wd2", lit RW, lit RM, lit LM, lit QM, l1, l2, lit x, lit y,
          lit z, p1, p2]) 0 nWE
  let args := #[lit h.inv, lit eps, lit nLab, lit nT, lit RW, lit RM, lit nR, lit nW, lit nF,
    lit nZ, lit LM, lit QM, d "F", d "Wd", d "Wd2", d "R", d "Lab", d "Quo", d "Val", d "Zt",
    mkConst (ns ++ `rels)]
  let type := isTrue (mkAppN (kbc "zOk" |> mkConst) (args.push (mkConst (T ++ `walk))))
  let pf := mkAppN (mkConst (kbc "zOk_intro")) (args.push walkL ++
    #[reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, tree, vals, walk, chk "piv"])
  (type, pf)

end CFSG.Certificates.KB.AssembleZ

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.AssembleZ in
elab "#kz_assemble " ns:ident t:ident p:ident "include_bytes" path:str size:num hash:num nZ:num
    LM:num QM:num m:num N:num : command => do
  let b ← CFSG.Certificates.KB.Load.readPinned path.getString size.getNat hash.getNat
  let h := parseHeader b
  let ns := ns.getId
  let T := ns ++ t.getId
  let (type, value) := zokOf ns T p.getId h nZ.getNat LM.getNat QM.getNat
  CFSG.Certificates.KB.Load.withSync do
    CFSG.KC.addThmDecl <| { name := ns ++ `zok, levelParams := [], type, value }
  elabCommand (← `(command| theorem $(mkIdent (ns ++ `zfact)) :
      CFSG.Certificates.KB.TableZFact $(Syntax.mkNumLit (toString m.getNat)) $(mkIdent (ns ++ `rels))
        $(mkIdent (T ++ `words)) $(Syntax.mkNumLit (toString N.getNat))
        $(Syntax.mkNumLit (toString nZ.getNat)) :=
    CFSG.Certificates.KB.TableZFact.intro $(mkIdent (ns ++ `t1)) $(mkIdent (ns ++ `top))
      $(mkIdent (ns ++ `zok))))

end

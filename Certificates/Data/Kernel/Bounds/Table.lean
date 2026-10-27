module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.Certificates.KB

@[expose] noncomputable def lensLt (ws : List (List (Nat × Bool))) (b : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB
      (Nat.blt (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ n => Nat.succ n) w) b) ih) ws

@[expose] noncomputable def tableOk (inv L eps nLab nT N RW RM nR nS nW nF : Nat)
    (F D Wd Wd2 R S : Nat → Nat) (amap : Nat) (rels words : List (List (Nat × Bool)))
    (walk cov : List Nat) : Bool :=
  andB (Nat.ble (Nat.succ L) (nat_lit 128))
  (andB (Nat.ble (nat_lit 1) N)
  (andB (Nat.ble N nLab)
  (andB (Nat.beq nLab (Nat.succ nT))
  (andB (Nat.ble (Nat.succ nLab) bad)
  (andB (Nat.ble (Nat.succ nF) bad)
  (andB (Nat.ble (Nat.succ nR) bad)
  (andB (Nat.ble (Nat.succ nS) bad)
  (andB (lensLt rels (nat_lit 256))
  (andB (lensLt words (nat_lit 256))
  (andB (hdrOk inv L eps amap)
  (andB (relsOk R nR amap rels)
  (andB (subsOk S nS amap words)
  (andB (wordsOkB Wd R S inv eps nR nS nW)
  (andB (words2Ok Wd Wd2 inv nW)
  (andB (treeRange F D L nLab (nat_lit 0) nT)
  (andB (Nat.beq (wWalkList F Wd2 RW RM nLab nW walk nT) nF)
    (Nat.beq (wCovList F RW RM N L nF cov (nat_lit 0)) N)))))))))))))))))

end CFSG.Certificates.KB

namespace CFSG.Certificates.KB.Cert

open CFSG.Certificates.KB.Checks

meta structure Counts where
  inv : Nat
  L : Nat
  eps : Nat
  nLab : Nat
  nT : Nat
  N : Nat
  RW : Nat
  RM : Nat
  nR : Nat
  nS : Nat
  nW : Nat
  nF : Nat
  wf : Array Nat
  cx : Array Nat

meta def counts (h : Header) : Counts :=
  let RW := h.get "RW"
  { inv := h.inv, L := h.get "L", eps := h.get "EPS", nLab := h.get "nLab", nT := h.get "nT",
    N := h.get "N", RW, RM := (1 <<< RW) - 1, nR := h.get "R", nS := h.get "K",
    nW := h.get "nWords", nF := h.get "nT" + h.get "nWalk",
    wf := scan (h.get "nT") (h.fields.getD "walkElems" #[]),
    cx := scan 0 (h.fields.getD "covElems" #[]) }

meta def listNatT (_ : Unit := ()) : Expr := mkApp (mkConst ``List [Level.zero]) natT

meta def elemName (D : Name) (pre : String) (j : Nat) : Name :=
  D ++ s!"{pre}{j / perPart}.c{j % perPart}".toName

meta partial def appendTree (D : Name) (pre : String) (lo hi : Nat) : Expr :=
  if hi ≤ lo then mkApp (mkConst ``List.nil [Level.zero]) natT
  else if hi = lo + 1 then mkConst (elemName D pre lo)
  else
    let mid := lo + (hi - lo) / 2
    mkApp3 (mkConst ``List.append [Level.zero]) natT (appendTree D pre lo mid)
      (appendTree D pre mid hi)

meta def okE (D T R : Name) (c : Counts) : Expr :=
  let d := fun (s : String) => mkConst (D ++ s.toName)
  mkAppN (kb "tableOk")
    #[lit c.inv, lit c.L, lit c.eps, lit c.nLab, lit c.nT, lit c.N, lit c.RW, lit c.RM, lit c.nR,
      lit c.nS, lit c.nW, lit c.nF, d "F", d "D", d "Wd", d "Wd2", d "R", d "S",
      mkConst (T ++ `amap), mkConst R, mkConst (T ++ `words), mkConst (T ++ `walk),
      mkConst (T ++ `cov)]

meta def addTop (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 65534, safety := .safe }

end CFSG.Certificates.KB.Cert

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.Cert in
elab "#kb_cert " ns:ident t:ident p:ident "include_bytes" path:str size:num hash:num rels:ident :
    command => do
  let b ← CFSG.Certificates.KB.Load.readPinned path.getString size.getNat hash.getNat
  let c := counts (parseHeader b)
  let T := ns.getId ++ t.getId
  let D := `CFSG.KBData ++ p.getId
  let R := rels.getId
  unless (← getEnv).contains R do throwError "unknown relator list {R}"
  unless (← getEnv).contains (T ++ `words) do throwError "no #kb_table declarations {T}"
  CFSG.Certificates.KB.Load.withSync do
    addTop (T ++ `walk) listNatT (appendTree D "wl" 0 (c.wf.size - 1))
    addTop (T ++ `cov) listNatT (appendTree D "cv" 0 (c.cx.size - 1))
    addTop (T ++ `ok) (mkConst ``Bool) (okE D T R c)

end

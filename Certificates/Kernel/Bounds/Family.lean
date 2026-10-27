module

public meta import Lean
public import Certificates.Data.Kernel.Bounds.TableFact
public import CFSG.Certificates.Kernel.Bounds.Checks
public import Certificates.Kernel.Bounds.Assemble
public import CFSG.Certificates.Kernel.Bounds.Load
public import CFSG.Certificates.Kernel.Bounds.LoadGz
public import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.Certificates.Kernel.Bounds.Load
meta import all CFSG.Certificates.Kernel.Common.Repo
meta import all CFSG.Certificates.Kernel.Common.Harness
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
public import Lean.Parser.Term

open Lean Elab Command

elab "kb_beta% " t:term : term => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  return (← instantiateMVars e).headBeta

namespace CFSG.Certificates.KB.Family

set_option hygiene false

meta def readManifest (rel : String) (size hash : Nat) : CommandElabM Json := do
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "cannot compute the directory of {← getFileName}"
  let z ← IO.FS.readBinFile (dir / rel)
  let b ← if !rel.endsWith ".gz" then pure z else match CFSG.KC.Gz.gunzip z with
    | .ok b => pure b
    | .error e => throwError "manifest {rel}: {e}"
  unless b.size == size && b.hash.toNat == hash do
    throwError "manifest {rel}: decompressed size {b.size} hash {b.hash.toNat}, pinned size {size} hash {hash}"
  let some s := String.fromUTF8? b | throwError "manifest {rel} is not UTF-8"
  match Json.parse s with
  | .ok j => pure j
  | .error e => throwError "manifest {rel}: {e}"

meta def field (j : Json) (k : String) : CommandElabM Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throwError "manifest: no field {k} in {j.compress}"

meta def str (j : Json) (k : String) : CommandElabM String := do
  match (← field j k).getStr? with
  | .ok s => pure s
  | .error _ => throwError "manifest: field {k} is not a string"

meta def nat (j : Json) : CommandElabM Nat :=
  match j.getNat? with
  | .ok n => pure n
  | .error _ => throwError "manifest: {j.compress} is not a natural number"

meta def natF (j : Json) (k : String) : CommandElabM Nat := do nat (← field j k)

meta def arr (j : Json) : CommandElabM (Array Json) :=
  match j.getArr? with
  | .ok a => pure a
  | .error _ => throwError "manifest: {j.compress} is not an array"

meta def num (n : Nat) : TSyntax `num := Syntax.mkNumLit (toString n)

meta structure Ctx where
  tables : Array Json
  route : Name
  fact : Name
  dir : String
  hdrDir : String
  repo : Bool

meta def ctx (path : String) (size hash : Nat) : CommandElabM Ctx := do
  let j ← readManifest path size hash
  let parent := (System.FilePath.mk path).parent.map (·.toString) |>.getD ""
  return { tables := ← arr (← field j "tables"), route := (← str j "route").toName,
           fact := (← str j "fact").toName,
           dir := (← str j "dir").replace "CertificateProofs/" "Certificates/",
           hdrDir := if parent.isEmpty then "" else parent ++ "/",
           repo := (j.getObjVal? "root").toOption != some (.str "data") }

meta def hdr (c : Ctx) (t : Json) : CommandElabM (Name × String × Nat × Nat) := do
  let dp ← str t "data"
  let #[s, h] ← arr (← field t "meta") | throwError "manifest: meta is not [size, hash]"
  return (dp.toName, c.hdrDir ++ dp ++ ".meta", ← nat s, ← nat h)

meta def relsTerm (t : Json) (srcs : Array (Name × Term)) : CommandElabM Term := do
  if let .ok ws := t.getObjVal? "words" then
    let ws ← (← arr ws).mapM fun w => do
      let ls ← (← arr w).mapM fun x => do
        let .ok (i : Int) := x.getInt? | throwError "manifest: letter {x.compress}"
        if i == 0 then throwError "manifest: letter 0"
        let g := num (i.natAbs - 1)
        if 0 < i then `(($g, true)) else `(($g, false))
      `([$ls,*])
    return ← `([$ws,*])
  let k := (← str t "src").toName
  let some (_, s) := srcs.find? (·.1 == k) | throwError "#kb_family: no source {k}"
  let args ← (← arr (← field t "args")).mapM fun a : Json => do
    match a with
    | .bool true => `(true)
    | .bool false => `(false)
    | _ => pure (num (← nat a) : Term)
  let x ← if s.raw.isOfKind ``Lean.Parser.Term.fun then `(kb_beta% ($s $args*))
    else if args.isEmpty then pure s else `($s $args*)
  `(($x).map fun w => w.map fun l => (l.1.val, l.2))

meta def checkCmds (c : Ctx) (t : Json) (slices : Array Nat) : CommandElabM Unit := do
  let (dp, hp, hs, hh) ← hdr c t
  for i in slices do
    elabCommand (← `(command| #kb_checks $(mkIdent dp) include_bytes $(quote hp) $(num hs)
      $(num hh) $(num i)))

meta def certCmds (c : Ctx) (t : Json) : CommandElabM Unit := do
  let P := (← str t "P").toName
  let (dp, hp, hs, hh) ← hdr c t
  let ns := c.route ++ P
  elabCommand (← `(command| #kb_cert $(mkIdent ns) T1 $(mkIdent dp) include_bytes $(quote hp)
    $(num hs) $(num hh) $(mkIdent (ns ++ `rels))))
  elabCommand (← `(command| theorem $(mkIdent (ns ++ `t1)) : $(mkIdent (ns ++ `T1.ok)) = true := by
    kb_assemble $(mkIdent dp)))
  elabCommand (← `(command| theorem $(mkIdent (c.fact ++ P)) :
      CFSG.Certificates.KB.TableFact $(num (← natF t "m")) $(mkIdent (ns ++ `rels))
        $(mkIdent (ns ++ `T1.words)) $(num (← natF t "N")) :=
    CFSG.Certificates.KB.TableFact.intro $(mkIdent (ns ++ `t1)) $(mkIdent (ns ++ `top))))

meta def flag (t : Json) (k : String) : Bool :=
  match t.getObjVal? k with
  | .ok (.bool b) => b
  | _ => false

meta def readFiles (c : Ctx) (files : Array (String × Nat × Nat)) (size hash : Nat) :
    CommandElabM ByteArray := do
  let root ← if c.repo then CFSG.KC.Repo.pkgRoot else (CFSG.KC.Load.dataRoot : CommandElabM _)
  let mut b := ByteArray.empty
  for (f, s, h) in files do
    let x ← IO.FS.readBinFile (root / f)
    unless x.size == s && x.hash.toNat == h do
      throwError "loader file {f}: size {x.size} hash {x.hash.toNat}, pinned size {s} hash {h}"
    b := b ++ x
  unless b.size == size && b.hash.toNat == hash do
    throwError "loader files {files.map (·.1)}: size {b.size} hash {b.hash.toNat}, pinned size \
      {size} hash {hash}"
  return b

open CFSG.Certificates.KB.Load in
meta def plainLoad (k : String) (F : Name) (as : Array Nat) (b : ByteArray) :
    CommandElabM Unit := do
  match k, as with
  | "blocked", #[lr, ls, mask] =>
    let leafBytes := (1 <<< (lr + ls)) / 8
    let nLeaves := (b.size + leafBytes - 1) / leafBytes
    withSync do
      for j in [0:nLeaves] do
        let lo := j * leafBytes
        let hi := min b.size (lo + leafBytes)
        addDef (F ++ Name.mkSimple s!"b{j}") natT (lit (natLE b lo hi))
      let leaf (j : Nat) : Expr :=
        let blk := if j < nLeaves then mkConst (F ++ Name.mkSimple s!"b{j}") else lit 0
        let i := mkBVar 0
        let off := mkApp2 (mkConst ``Nat.shiftLeft)
          (mkApp2 (mkConst ``Nat.land) i (lit ((1 <<< lr) - 1))) (lit ls)
        mkLambda `i .default natT
          (mkApp2 (mkConst ``Nat.land) (mkApp2 (mkConst ``Nat.shiftRight) blk off) (lit mask))
      addDef F fnT (CFSG.KC.Tab.table leaf (nextPow2 (max nLeaves 1)) lr)
  | "items", #[] =>
    let its := items b
    withSync do
      for j in [0:its.size] do
        let (lo, hi) := its[j]!
        addDef (F ++ Name.mkSimple s!"b{j}") natT (lit (natLE b lo hi))
      let leaf (j : Nat) : Expr :=
        mkApp (mkConst `CFSG.Certificates.KB.constN)
          (if j < its.size then mkConst (F ++ Name.mkSimple s!"b{j}") else lit 0)
      addDef F fnT (CFSG.KC.Tab.table leaf (nextPow2 (max its.size 1)) 0)
  | "list", #[per] =>
    let its := items b
    let listT := mkApp (mkConst ``List [Level.zero]) natT
    withSync do
      let nk := (its.size + per - 1) / per
      for k in [0:nk] do
        let mut e := mkApp (mkConst ``List.nil [Level.zero]) natT
        let top := min its.size ((k + 1) * per)
        for jj in [0:top - k * per] do
          let j := top - 1 - jj
          let (lo, hi) := its[j]!
          e := mkApp3 (mkConst ``List.cons [Level.zero]) natT (lit (natLE b lo hi)) e
        addDef (F ++ Name.mkSimple s!"c{k}") listT e
  | _, _ => throwError "manifest: loader kind {k} with {as.size} arguments"

meta def loadCmds (c : Ctx) (t : Json) (part : Option Nat) : CommandElabM Unit := do
  let (dp, _) ← hdr c t
  let .ok ls := t.getObjVal? "load" | return
  for l in ← arr ls do
    let a ← arr l
    let p? ← if h : 6 < a.size then some <$> nat a[6] else pure none
    unless a.size == 6 || a.size == 7 do throwError "manifest: loader {l.compress}"
    unless p? == part do continue
    let .ok k := a[0]!.getStr? | throwError "manifest: loader {l.compress}"
    let .ok nm := a[1]!.getStr? | throwError "manifest: loader {l.compress}"
    let F := `CFSG.KBData ++ dp ++ nm.toName
    let id := mkIdent F
    let as ← (← arr a[3]!).mapM nat
    let (sz, hs) := (← nat a[4]!, ← nat a[5]!)
    let (s, h) := (num sz, num hs)
    let gz := match a[2]!.getStr? with
      | .ok f => if f.endsWith ".gz" then some f else none
      | .error _ => none
    let some f := gz | do
      let files ← match a[2]! with
        | .str f => pure #[(f, sz, hs)]
        | .arr ps => ps.mapM fun q => do
          let #[f, qs, qh] ← arr q | throwError "manifest: part {q.compress}"
          let .ok f := f.getStr? | throwError "manifest: part {q.compress}"
          pure (f, ← nat qs, ← nat qh)
        | _ => throwError "manifest: loader {l.compress}"
      plainLoad k F as (← readFiles c (files.map fun (f, x, y) => (c.dir ++ "/" ++ f, x, y)) sz hs)
      continue
    let p := quote (c.dir ++ "/" ++ f)
    let cmd ← match k, as with
      | "blocked", #[x, y, m] => `(command| #kc_blocked_gz $id $p $(num x) $(num y) $(num m) $s $h)
      | "items", #[] => `(command| #kc_items_gz $id $p $s $h)
      | "list", #[per] => `(command| #kc_list_gz $id $p $(num per) $s $h)
      | _, _ => throwError "manifest: loader {l.compress}"
    elabCommand (← if c.repo then `(command| #kc_repo $cmd) else pure cmd)

meta def mainCmds (c : Ctx) (srcs : Array (Name × Term)) (t : Json) : CommandElabM Unit := do
  let P := (← str t "P").toName
  let ns := c.route ++ P
  let (dp, hp, hs, hh) ← hdr c t
  elabCommand (← `(command| @[expose] def $(mkIdent (ns ++ `rels)) : List (List (Nat × Bool)) :=
    $(← relsTerm t srcs)))
  loadCmds c t none
  elabCommand (← `(command| #kb_table $(mkIdent ns) T1 $(mkIdent dp) include_bytes $(quote hp)
    $(num hs) $(num hh) $(num (← natF t "amap")) $(mkIdent (ns ++ `rels))
    $(quote (← str t "subs"))))
  let m := num (← natF t "m")
  elabCommand (← `(command| theorem $(mkIdent (ns ++ `top)) :
      CFSG.Certificates.KB.topOk $(mkIdent (ns ++ `T1.amap)) (nat_lit $m) = true := by
    quickRfl))
  if (t.getObjVal? "parts").toOption.isNone then
    if let .ok n := t.getObjVal? "slices" then
      checkCmds c t (Array.range (← nat n))
  unless flag t "close" do certCmds c t

end CFSG.Certificates.KB.Family

open CFSG.Certificates.KB.Family in
elab "#kb_family " path:str size:num hash:num srcs:("(" ident " := " term ")")* : command => do
  let c ← ctx path.getString size.getNat hash.getNat
  let srcs := srcs.map fun s => ((⟨s.raw[1]⟩ : Ident).getId, (⟨s.raw[3]⟩ : Term))
  for t in c.tables do mainCmds c srcs t

open CFSG.Certificates.KB.Family in
elab "#kb_family_part " path:str size:num hash:num i:num : command => do
  let c ← ctx path.getString size.getNat hash.getNat
  for t in c.tables do
    if let .ok ps := t.getObjVal? "parts" then
      let ps ← arr ps
      if h : i.getNat < ps.size then
        loadCmds c t (some i.getNat)
        checkCmds c t (← (← arr ps[i.getNat]).mapM nat)

open CFSG.Certificates.KB.Family in
elab "#kb_family_close " path:str size:num hash:num : command => do
  let c ← ctx path.getString size.getNat hash.getNat
  for t in c.tables do
    if let .ok cs := t.getObjVal? "closeSlices" then
      checkCmds c t (← (← arr cs).mapM nat)
    if flag t "close" then certCmds c t

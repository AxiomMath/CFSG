module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Verify

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def findK (P : Pt) : Option Vec :=
  let p := P.p
  let rec fzt_powGo (b e acc fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
        if e = 0 then acc
        else if e % 2 = 1 then fzt_powGo (b * b % p) (e / 2) (acc * b % p) fuel
        else fzt_powGo (b * b % p) (e / 2) acc fuel
  let fzt_powMod (b e : Nat) : Nat := fzt_powGo (b % p) e (1 % p) e
  let fzt_inv (a : Nat) : Nat := fzt_powMod a (p - 2)
  let fzt_rowSub (coef : Nat) (r b : Vec) : Vec :=
    (List.range P.D).map fun i => (P.ent r i + p - (coef * P.ent b i) % p) % p
  let rec fzt_reduceRow (r : Vec) (bs : List (Nat × Vec)) : Vec :=
    match bs with
    | [] => r
    | (piv, b) :: bs' => fzt_reduceRow (fzt_rowSub (P.ent r piv) r b) bs'
  let fzt_insert (r : Vec) (basis : List (Nat × Vec)) : List (Nat × Vec) :=
    let r := fzt_reduceRow r basis
    match (List.range P.D).find? (fun j => P.ent r j != 0) with
    | none => basis
    | some j =>
        let iv := fzt_inv (P.ent r j)
        let rn := r.map (fun x => (x % p * iv) % p)
        let basis' := basis.map fun (piv, b) =>
          if P.ent b j == 0 then (piv, b)
          else (piv, fzt_rowSub (P.ent b j) b rn)
        (j, rn) :: basis'
  let fzt_pivs (basis : List (Nat × Vec)) : List Nat := basis.map (·.1)
  let fzt_freeCols (basis : List (Nat × Vec)) : List Nat :=
    (List.range P.D).filter fun j => (fzt_pivs basis).contains j == false
  let fzt_kernelVec (basis : List (Nat × Vec)) (j : Nat) : Vec :=
    (List.range P.D).map fun i =>
      if i = j then 1
      else match basis.find? (fun pr => pr.1 == i) with
        | some pr => (p - P.ent pr.2 j) % p
        | none => 0
  let rec fzt_firstK (basis : List (Nat × Vec)) (js : List Nat) : Option Vec :=
    match js with
    | [] => none
    | j :: js' =>
        let w := fzt_kernelVec basis j
        if verifyK P w then some w else fzt_firstK basis js'
  let rows := (P.gens.take P.nFrame).map (·.f)
  let basis := rows.foldl (fun bs r => fzt_insert r bs) []
  fzt_firstK basis (fzt_freeCols basis)

@[expose] def findT (P : Pt) : Option TWit :=
  let p := P.p
  let rec fzt_powGo (b e acc fuel : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
        if e = 0 then acc
        else if e % 2 = 1 then fzt_powGo (b * b % p) (e / 2) (acc * b % p) fuel
        else fzt_powGo (b * b % p) (e / 2) acc fuel
  let fzt_powMod (b e : Nat) : Nat := fzt_powGo (b % p) e (1 % p) e
  let fzt_inv (a : Nat) : Nat := fzt_powMod a (p - 2)
  let fzt_key (r : Vec × Vec × Word) : Nat × Nat := (P.code r.1, P.code r.2.1)
  let fzt_normalize (r : Vec × Vec × Word) : Vec × Vec × Word :=
    match (List.range P.D).find? (fun i => P.ent r.1 i != 0) with
    | none => r
    | some i =>
        let v := P.ent r.1 i
        let iv := fzt_inv v
        (r.1.map (fun x => (x % p * iv) % p), r.2.1.map (fun x => (x % p * v) % p), r.2.2)
  let fzt_conj (s t : Vec × Vec × Word) : Vec × Vec × Word :=
    let a := P.dotv s.2.1 t.1
    let b := P.dotv t.2.1 s.1
    ((List.range P.D).map (fun i => (P.ent t.1 i + p - (a * P.ent s.1 i) % p) % p),
     (List.range P.D).map (fun i => (P.ent t.2.1 i + p - (b * P.ent s.2.1 i) % p) % p),
     s.2.2 ++ t.2.2 ++ s.2.2.reverse)
  let fzt_par (u v : Vec) : Bool :=
    (List.range P.D).all fun i => (List.range P.D).all fun j =>
      (P.ent u i * P.ent v j) % p == (P.ent u j * P.ent v i) % p
  let fzt_buildWit (w : Word) : Option TWit :=
    let diffs := (List.range P.D).map fun i =>
      (List.range P.D).map fun j =>
        (P.ent (P.applyWord w (P.unit i)) j + p - (if i = j then 1 else 0)) % p
    match diffs.find? (fun col => P.vecNZ col) with
    | none => none
    | some u =>
        match (List.range P.D).find? (fun r => P.ent u r != 0) with
        | none => none
        | some r =>
            let iv := fzt_inv (P.ent u r)
            let φ := diffs.map (fun col => (P.ent col r * iv) % p)
            let wit : TWit := { word := w, u := u, φ := φ }
            if verifyT P wit then some wit else none
  let rec fzt_tryWords (ws : List Word) : Option TWit :=
    match ws with
    | [] => none
    | w :: ws' =>
        match fzt_buildWit w with
        | some wit => some wit
        | none => fzt_tryWords ws'
  let fzt_testOne (s t : Vec × Vec × Word) : Option TWit :=
    let a := P.dotv s.2.1 t.1
    let b := P.dotv t.2.1 s.1
    if ((a == 0) != (b == 0)) ||
        (((a * b) % p) == (4 % p) && (fzt_par s.1 t.1 || fzt_par s.2.1 t.2.1)) then
      fzt_tryWords [s.2.2 ++ t.2.2, t.2.2 ++ s.2.2,
        s.2.2 ++ t.2.2 ++ s.2.2 ++ t.2.2, t.2.2 ++ s.2.2 ++ t.2.2 ++ s.2.2]
    else none
  let rec fzt_test (order : List (Vec × Vec × Word)) (t : Vec × Vec × Word) : Option TWit :=
    match order with
    | [] => none
    | s :: rest =>
        match fzt_testOne s t with
        | some wit => some wit
        | none => fzt_test rest t
  let rec fzt_genGens (gs : List (Vec × Vec × Word)) (tt : Vec × Vec × Word)
      (acc : List (Vec × Vec × Word) × List (Nat × Nat) × List (Vec × Vec × Word)) :
      Option (List (Vec × Vec × Word) × List (Nat × Nat) × List (Vec × Vec × Word)) × Option TWit :=
    match gs with
    | [] => (some acc, none)
    | g :: gs' =>
        let cc := fzt_normalize (fzt_conj g tt)
        let k := fzt_key cc
        if acc.2.1.contains k then fzt_genGens gs' tt acc
        else
          match fzt_test acc.2.2 cc with
          | some wit => (none, some wit)
          | none =>
              let acc' := (cc :: acc.1, k :: acc.2.1, acc.2.2 ++ [cc])
              if acc'.2.2.length > 400 then (none, none)
              else fzt_genGens gs' tt acc'
  let rec fzt_level (gens : List (Vec × Vec × Word)) (fuel : Nat)
      (fr : List (Vec × Vec × Word)) (nf : List (Vec × Vec × Word))
      (seen : List (Nat × Nat)) (order : List (Vec × Vec × Word)) : Option TWit :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match fr with
        | [] =>
            match nf with
            | [] => none
            | _ =>
                if order.length > 400 then none
                else fzt_level gens fuel nf.reverse [] seen order
        | tt :: rest =>
            match fzt_genGens gens tt (nf, seen, order) with
            | (some acc, none) => fzt_level gens fuel rest acc.1 acc.2.1 acc.2.2
            | (none, some wit) => some wit
            | _ => none
  let rec fzt_addGens (gs : List (Vec × Vec × Word)) (seen : List (Nat × Nat))
      (order : List (Vec × Vec × Word)) :
      Option TWit × List (Vec × Vec × Word) × List (Nat × Nat) × List (Vec × Vec × Word) :=
    match gs with
    | [] => (none, [], seen, order)
    | g :: gs' =>
        let k := fzt_key g
        if seen.contains k then fzt_addGens gs' seen order
        else
          match fzt_test order g with
          | some wit => (some wit, [], k :: seen, order ++ [g])
          | none =>
              match fzt_addGens gs' (k :: seen) (order ++ [g]) with
              | (found, fr, seen', order') => (found, g :: fr, seen', order')
  let gens : List (Vec × Vec × Word) :=
    (P.gens.zipIdx).map fun (r, k) => fzt_normalize ((r.h, r.f, [k]) : Vec × Vec × Word)
  match fzt_addGens gens [] [] with
  | (some wit, _, _, _) => some wit
  | (none, fr, seen, order) => fzt_level gens 100000 fr [] seen order

end CFSG.TwoNodeSmall

module

public import CFSG.Quasithin.H13.L32NMatNInputs
public import Certificates.Data.Kernel.Mat8P

public section

namespace CFSG.KC.Mat12P

open CFSG.KC.Mat8P

@[expose] def termQ (X Y i s : ℕ) : ℕ :=
  Nat.mul (Nat.land (Nat.shiftRight Y i) (nat_lit 5445847423328601499764522166702896582657))
    (Nat.land (Nat.shiftRight X s) (nat_lit 4095))

@[expose] def mulQ (X Y : ℕ) : ℕ :=
  Nat.xor (termQ X Y 0 0) (Nat.xor (termQ X Y 1 12) (Nat.xor (termQ X Y 2 24)
    (Nat.xor (termQ X Y 3 36) (Nat.xor (termQ X Y 4 48) (Nat.xor (termQ X Y 5 60)
    (Nat.xor (termQ X Y 6 72) (Nat.xor (termQ X Y 7 84) (Nat.xor (termQ X Y 8 96)
    (Nat.xor (termQ X Y 9 108) (Nat.xor (termQ X Y 10 120) (termQ X Y 11 132)))))))))))

@[expose] def colQ (X s : ℕ) : ℕ := Nat.land (Nat.shiftRight X s) (nat_lit 4095)

@[expose] def unpackQ (X : ℕ) : List ℕ :=
  [colQ X 0, colQ X 12, colQ X 24, colQ X 36, colQ X 48, colQ X 60, colQ X 72, colQ X 84,
    colQ X 96, colQ X 108, colQ X 120, colQ X 132]

@[expose] def codeQ (x : List ℕ) : ℕ :=
  x.foldr (fun c acc => Nat.add c (Nat.mul (nat_lit 4096) acc)) (nat_lit 0)

@[expose] def oneQ : ℕ := nat_lit 11151733894906779683522195341810241573494785

@[expose] def mvT (X v j s : ℕ) : ℕ := Nat.mul (colQ X s) (Nat.land (Nat.shiftRight v j) 1)

@[expose] def mvQ (X v : ℕ) : ℕ :=
  Nat.xor (mvT X v 0 0) (Nat.xor (mvT X v 1 12) (Nat.xor (mvT X v 2 24)
    (Nat.xor (mvT X v 3 36) (Nat.xor (mvT X v 4 48) (Nat.xor (mvT X v 5 60)
    (Nat.xor (mvT X v 6 72) (Nat.xor (mvT X v 7 84) (Nat.xor (mvT X v 8 96)
    (Nat.xor (mvT X v 9 108) (Nat.xor (mvT X v 10 120) (mvT X v 11 132)))))))))))

@[expose] def bfsQ (gens : List ℕ) (cap : ℕ) : ℕ → NT ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      if cap ≤ acc.length then acc else
      let st := fr.foldl (fun (st : NT ℕ × List ℕ × List ℕ) x =>
          (List.range gens.length).foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
            let y := mulQ (gens.getD i oneQ) x
            if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st)
        (seen, acc, [])
      bfsQ gens cap fuel st.1 st.2.1 st.2.2

@[expose] def elemsQ (gens : List ℕ) (cap : ℕ := 100000) : List ℕ :=
  bfsQ gens cap 400 (insP (.tip []) oneQ) [oneQ] [oneQ]

@[expose] def mvNR : List ℕ → ℕ → ℕ
  | [], _ => nat_lit 0
  | c :: A, v => Nat.xor (Nat.mul c (Nat.land v (nat_lit 1))) (mvNR A (Nat.shiftRight v (nat_lit 1)))

@[expose] def validQ (x : List ℕ) : Bool :=
  Nat.beq x.length (nat_lit 12) && x.all fun c => Nat.blt c (nat_lit 4096)

@[expose] def mulNF (A B : List ℕ) : List ℕ :=
  if validQ A && validQ B then unpackQ (mulQ (codeQ A) (codeQ B)) else B.map (mvNR A)

@[expose] def elemsQF (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  if gens.all validQ then (elemsQ (gens.map codeQ) cap).map unpackQ
  else CFSG.Quasithin.H13.MatNCert.elemsOf 12 gens cap

@[expose] def powNF (x : List ℕ) : ℕ → List ℕ
  | 0 => CFSG.Quasithin.H13.MatNCert.oneN 12
  | k + 1 => mulNF x (powNF x k)

@[expose] def sqNF (x : List ℕ) : ℕ → List ℕ
  | 0 => x
  | k + 1 => mulNF (sqNF x k) (sqNF x k)

end CFSG.KC.Mat12P

end

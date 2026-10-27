module

public import Certificates.Data.Kernel.Fi23Q.Defs

public section

namespace CFSG.KC.Fi23Q

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Pc3

@[expose] noncomputable def f16 (T k : Nat) : Nat :=
  fld(T, Nat.shiftLeft k (nat_lit 4), nat_lit 65535)

@[expose] noncomputable def f64 (T k : Nat) : Nat :=
  fld(T, Nat.shiftLeft k (nat_lit 6), nat_lit 18446744073709551615)

@[expose] noncomputable def b3v (m s t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih x => Nat.add (Nat.mod x (nat_lit 3)) (Nat.shiftLeft (ih (Nat.div x (nat_lit 3))) s))
    m t

@[expose] noncomputable def d3 (b k : Nat) : Nat :=
  Nat.mod (Nat.div b (Nat.pow (nat_lit 3) k)) (nat_lit 3)

@[expose] noncomputable def aOK (u : Nat) : Bool :=
  bAnd(vecOK (nat_lit 13) u, Nat.beq (lowV u (nat_lit 8)) (nat_lit 0))

@[expose] noncomputable def nibA (u : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun _ ih x => Nat.add (Nat.land x (nat_lit 3)) (Nat.shiftLeft (ih (Nat.shiftRight x (nat_lit 2))) (nat_lit 4)))
    (nat_lit 5) (Nat.shiftRight u (nat_lit 16))

@[expose] noncomputable def nAdd (x y : Nat) : Nat :=
  strictN (Nat.add x y) fun s => Nat.sub s (Nat.mul (nat_lit 3)
    (Nat.land (Nat.lor (Nat.shiftRight s (nat_lit 2)) (Nat.land s (Nat.shiftRight s (nat_lit 1))))
      (nat_lit 69905)))

@[expose] noncomputable def nSc (e x : Nat) : Nat :=
  nIf(Nat.beq e (nat_lit 0), nat_lit 0, nIf(Nat.beq e (nat_lit 1), x, nAdd x x))

@[expose] noncomputable def mulM (MV b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc fun s => nAdd s (nSc (d3 b k) (nibA (f32 MV k)))) (nat_lit 5)

@[expose] noncomputable def cosChk (H : Nat → Nat) (RV nR i D : Nat) : Bool :=
  allN (nat_lit 64) fun l => strictB (Nat.add (Nat.shiftLeft i (nat_lit 6)) l) fun t =>
    bIf(Nat.blt t (nat_lit 6561),
      strictB (f64 D l) fun e => strictB (fld(e, nat_lit 0, nat_lit 67108863)) fun b =>
        strictB (fld(e, nat_lit 26, nat_lit 67108863)) fun α =>
        strictB (Nat.shiftRight e (nat_lit 52)) fun ρ =>
        bAnd(Nat.blt ρ nR, bAnd(aOK α, bAnd(vecOK (nat_lit 13) b,
          eqH H (List.append (nwR (nat_lit 13) (b3v (nat_lit 8) (nat_lit 2) t)) (nwR (nat_lit 13) b))
            (List.append (nwR (nat_lit 13) b)
              (List.append (nwR (nat_lit 13) (f16 RV ρ)) (nwR (nat_lit 13) α)))))),
      true)

@[expose] noncomputable def clsChk (H : Nat → Nat) (CR nQ r c e : Nat) : Bool :=
  (fun X => bIf(eqH H (List.append X (List.append X X)) List.nil,
    bIf(eqH H X List.nil, true,
      strictB (fld(e, nat_lit 0, nat_lit 67108863)) fun w => strictB (Nat.shiftRight e (nat_lit 26)) fun q =>
        bAnd(Nat.blt q nQ, bAnd(vecOK (nat_lit 13) w,
          eqH H (List.append X (nwR (nat_lit 13) w))
            (List.append (nwR (nat_lit 13) w) (nwR (nat_lit 13) (f32 CR q)))))),
    true)) (List.append (nwR (nat_lit 13) r) (nwR (nat_lit 13) c))

@[expose] noncomputable def repChk (H : Nat → Nat) (RV CR nQ ρ MV ncl CV WD XD : Nat) : Bool :=
  strictB (f16 RV ρ) fun r => bAnd(vecOK (nat_lit 13) r,
    bAnd(allN (nat_lit 5) fun k => strictB (f32 MV k) fun m => bAnd(aOK m,
        eqH H (List.cons (Nat.add (nat_lit 8) k) (nwR (nat_lit 13) r))
          (List.append (nwR (nat_lit 13) r) (nwR (nat_lit 13) m))),
      bAnd(allN (nat_lit 243) fun a => strictB (f16 WD a) fun e =>
          strictB (Nat.land e (nat_lit 255)) fun b => strictB (Nat.shiftRight e (nat_lit 8)) fun j =>
          bAnd(Nat.blt b (nat_lit 243), bAnd(Nat.blt j ncl,
            Nat.beq (nAdd (nAdd (b3v (nat_lit 5) (nat_lit 4) a) (b3v (nat_lit 5) (nat_lit 4) b))
                (nSc (nat_lit 2) (mulM MV b)))
              (nibA (f32 CV j)))),
        allN ncl fun j => strictB (f32 CV j) fun c => bAnd(aOK c,
          clsChk H CR nQ r c (f64 XD j)))))

end CFSG.KC.Fi23Q

end

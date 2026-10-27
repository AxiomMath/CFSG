module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithLab
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Quasithin.Stroth.G5.K

@[expose] noncomputable def dSK (s2 s1 m : ℕ) : ℕ :=
  Bool.rec (Bool.rec 0 1 (Nat.ble m s1)) 2 (Nat.ble m s2)

@[expose] noncomputable def dLK (l1 m : ℕ) : ℕ := Bool.rec 0 1 (Nat.ble m l1)

@[expose] noncomputable def pk (key : ℕ) : ℕ := Nat.shiftLeft 1 (Nat.mul 8 key)

@[expose] noncomputable def redK (J1 r e t' s : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (Nat.add (Nat.mul 4 t') (Nat.mul 2 s))
    (fun r₀ _ =>
      let x := Nat.add t' (Nat.mul J1 r₀)
      Nat.add (Nat.mul 4 (Nat.mod x (Nat.succ r₀)))
        (Nat.mul 2 (Nat.mod (Nat.add s (Nat.mul e (Nat.mod (Nat.add (Nat.div x (Nat.succ r₀)) J1) 2))) 2)))
    r

@[expose] noncomputable def psiStep (J1 r e s2 s1 m lo s : ℕ) : ℕ :=
  Bool.rec 0
    (let d := dSK s2 s1 m
     let b := redK J1 r e (Nat.div lo 2) s
     Bool.rec (Bool.rec 0 (pk (Nat.add b 1)) (Nat.beq d 1))
       (Nat.add (pk b) (pk (Nat.add b 1))) (Nat.beq d 2))
    (Nat.beq (Nat.mod lo 2) 0)

@[expose] noncomputable def chiStep (J1 r e l1 m lo s : ℕ) : ℕ :=
  Bool.rec (Bool.rec 0 (pk (redK J1 r e (Nat.div lo 2) s)) (Nat.beq (dLK l1 m) 1)) 0
    (Nat.beq (Nat.mod lo 2) 0)

@[expose] noncomputable def linStep (J1 r ε δ s2 s1 l1 m lo s : ℕ) : ℕ :=
  let x := Nat.add (Nat.div lo 2) (Nat.mul J1 (Nat.sub r 1))
  Bool.rec
    (Bool.rec 0
      (pk (Nat.add (Nat.add (Nat.mul 4 (Nat.mod (Nat.add x (Nat.div (Nat.succ r) 2)) r))
        (Nat.mul 2 (Nat.mod (Nat.add s ε) 2))) δ)) (Nat.beq (dLK l1 m) 1))
    (let d := dSK s2 s1 m
     let b := Nat.add (Nat.mul 4 (Nat.mod x r)) (Nat.mul 2 s)
     Bool.rec (Bool.rec 0 (pk (Nat.add b 1)) (Nat.beq d 1))
       (Nat.add (pk b) (pk (Nat.add b 1))) (Nat.beq d 2))
    (Nat.beq (Nat.mod lo 2) 0)

@[expose] noncomputable def winOK (f : ℕ → ℕ → ℕ → ℕ) (J O i d : ℕ) : Bool :=
  Nat.beq
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => Nat.add acc
        (f (Nat.add (Nat.succ d) k) (Nat.add (Nat.add (Nat.add i d) (Nat.succ k)) O) 0))
      (Nat.sub J d))
    (Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => Nat.add acc (f (Nat.add (Nat.succ d) k) (Nat.sub (Nat.add i O) (Nat.succ k)) 1))
      (Nat.sub J d))

@[expose] noncomputable def allWin (f : ℕ → ℕ → ℕ → ℕ) (J : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun d acc => Bool.rec false (Bool.rec false (winOK f J (Nat.mul 2 (Nat.succ J)) 1 d)
      (winOK f J (Nat.mul 2 (Nat.succ J)) 0 d)) acc) (Nat.succ J)

@[expose] noncomputable def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => Bool.rec false (f k) acc) n

@[expose] noncomputable def linNone (J s2 s1 l1 : ℕ) : Bool :=
  allBelow (Nat.add J 3) fun k => allBelow 4 fun c =>
    Bool.not (allWin (linStep (Nat.succ J) (Nat.succ (Nat.mul 2 k)) (Nat.div c 2) (Nat.mod c 2)
      s2 s1 l1) J)

@[expose] noncomputable def memP (r r' : ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ acc => Bool.rec acc true (Bool.rec false (Nat.beq x.2 r') (Nat.beq x.1 r))) pairs30

@[expose] noncomputable def isP (p : Pattern) (a b c : ℕ) : Bool :=
  Bool.rec false (Bool.rec false (Nat.beq p.l1 c) (Nat.beq p.s1 b)) (Nat.beq p.s2 a)

@[expose] noncomputable def okK (p : Pattern) (r e r' e' : ℕ) : Bool :=
  let i44 := Bool.rec true (isP p 7 7 7) (Bool.rec false (Nat.beq r' 4) (Nat.beq r 4))
  let i33 := Bool.rec true (isP p 5 5 5) (Bool.rec false (Nat.beq r' 3) (Nat.beq r 3))
  let i22 := Bool.rec true
      (Bool.rec (Bool.rec (isP p 3 11 3) true (isP p 3 3 11)) true (isP p 3 3 3))
      (Bool.rec false (Bool.rec (Nat.beq r' 6) true (Nat.beq r' 2)) (Nat.beq r 2))
  Bool.rec false (Bool.rec false (Bool.rec false
    (Bool.rec false (Bool.rec false i44 i33) i22) (memP r r')) (Nat.beq e' 1)) (Nat.beq e 1)

@[expose] noncomputable def nbits (r : ℕ) : ℕ := Bool.rec 2 1 (Nat.beq r 0)

@[expose] noncomputable def chkG (ok : ℕ → ℕ → ℕ → ℕ → Bool) (p : Pattern) : Bool :=
  Bool.rec false
    (allBelow (Nat.add p.J 3) fun r => allBelow (nbits r) fun e =>
      Bool.rec true
        (allBelow (Nat.add p.J 3) fun r' => allBelow (nbits r') fun e' =>
          Bool.rec true (ok r e r' e') (allWin (chiStep (Nat.succ p.J) r' e' p.l1) p.J))
        (allWin (psiStep (Nat.succ p.J) r e p.s2 p.s1) p.J))
    (linNone p.J p.s2 p.s1 p.l1)

@[expose] noncomputable def chkK (p : Pattern) : Bool := chkG (okK p) p

@[expose] noncomputable def admK (s2 s1 l1 : ℕ) : Bool :=
  Bool.rec false
    (Nat.rec (motive := fun _ => ℕ × ℕ × Bool) (0, 0, true)
      (fun m acc =>
        let a := Bool.rec
          (Nat.add acc.1 (Bool.rec (dSK s2 s1 m) (dLK l1 m) (Nat.beq (Nat.mod m 2) 1))) acc.1
          (Nat.beq m 0)
        let b := Bool.rec
          (Nat.add acc.2.1 (Bool.rec (dLK l1 m) (dSK s2 s1 m) (Nat.beq (Nat.mod m 2) 1))) acc.2.1
          (Nat.beq m 0)
        (a, b, Bool.rec false
          (Bool.rec false
            (Bool.rec true (Nat.beq b (Nat.succ a)) (Nat.beq (Nat.mod m 2) 1))
            (Nat.ble b 11)) (Bool.rec false (Nat.ble a 10) acc.2.2)))
      (Nat.add (Nat.max s1 l1) 2)).2.2
    (Bool.rec false (Bool.rec false (Nat.ble 1 l1) (Nat.ble s2 s1)) (Nat.ble 1 s2))

@[expose] noncomputable def fullK : Bool :=
  allBelow 25 fun s1 => allBelow (Nat.succ s1) fun s2 => allBelow 25 fun l1 =>
    Bool.rec true (chkK ⟨s2, s1, l1⟩) (admK s2 s1 l1)

end CFSG.Quasithin.Stroth.G5.K

end

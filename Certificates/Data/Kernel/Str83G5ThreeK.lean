module

public import Certificates.Data.Kernel.Str83G5TypeK

public section

namespace CFSG.Quasithin.Stroth.G5.K

@[expose] noncomputable def sg1K (m v : ℕ) : ℕ :=
  Nat.add (Nat.mul 7 (Nat.mod (Nat.sub 7 (Nat.div v 7)) 7))
    (Nat.mod (Nat.add (Nat.mod v 7) (Nat.mul 12 (Nat.mul m (Nat.div v 7)))) 7)

@[expose] noncomputable def sg2K (k v : ℕ) : ℕ :=
  Nat.add (Nat.mul 7 (Nat.mod (Nat.add (Nat.div v 7) (Nat.mul 12 (Nat.mul k (Nat.mod v 7)))) 7))
    (Nat.mod (Nat.sub 7 (Nat.mod v 7)) 7)

@[expose] noncomputable def pwK (k m J1 t' v : ℕ) : ℕ :=
  Bool.rec (Nat.rec (motive := fun _ => ℕ) v (fun _ w => sg1K m (sg2K k w)) (Nat.sub J1 t'))
    (Nat.rec (motive := fun _ => ℕ) v (fun _ w => sg2K k (sg1K m w)) (Nat.sub t' J1))
    (Nat.ble J1 t')

@[expose] noncomputable def smK (c v : ℕ) : ℕ :=
  Nat.add (Nat.mul 7 (Nat.mod (Nat.mul c (Nat.div v 7)) 7)) (Nat.mod (Nat.mul c (Nat.mod v 7)) 7)

@[expose] noncomputable def minK (a b : ℕ) : ℕ := Bool.rec b a (Nat.ble a b)

@[expose] noncomputable def clsK (v : ℕ) : ℕ := minK v (minK (smK 2 v) (smK 4 v))

@[expose] noncomputable def step3K (k m J1 s2 s1 l1 mm lo s : ℕ) : ℕ :=
  let sc := Bool.rec 1 6 (Nat.beq s 1)
  Bool.rec
    (Bool.rec 0 (pk (clsK (smK sc (pwK k m J1 (Nat.div lo 2) (Nat.add (Nat.mul 7 k) 1)))))
      (Nat.beq (dLK l1 mm) 1))
    (let w := pwK k m J1 (Nat.div lo 2) (Nat.add 7 m)
     let d := dSK s2 s1 mm
     Bool.rec (Bool.rec 0 (pk (clsK (smK (Nat.mul 5 sc) w))) (Nat.beq d 1))
       (Nat.add (pk (clsK (smK sc w))) (pk (clsK (smK (Nat.mul 5 sc) w)))) (Nat.beq d 2))
    (Nat.beq (Nat.mod lo 2) 0)

@[expose] noncomputable def okThreeK (p : Pattern) (k m : ℕ) : Bool :=
  let T := Nat.mod (Nat.add (Nat.mul 4 (Nat.mul k m)) 5) 7
  Bool.rec
    (Bool.rec (Bool.rec false (Nat.beq T 1) (isP p 5 5 5)) true
      (Bool.rec false (Nat.beq T 0)
        (Bool.rec (Bool.rec (Bool.rec (isP p 7 7 3) true (isP p 3 11 3)) true (isP p 3 3 11)) true
          (isP p 3 3 3))))
    true (isP p 7 7 7)

@[expose] noncomputable def chk3K (p : Pattern) : Bool :=
  allBelow 6 fun k => allBelow 6 fun m =>
    Bool.rec true (okThreeK p (Nat.succ k) (Nat.succ m))
      (allWin (step3K (Nat.succ k) (Nat.succ m) (Nat.succ p.J) p.s2 p.s1 p.l1) p.J)

@[expose] noncomputable def threeK : Bool :=
  allBelow 25 fun s1 => allBelow (Nat.succ s1) fun s2 => allBelow 25 fun l1 =>
    Bool.rec true (chk3K ⟨s2, s1, l1⟩) (admK s2 s1 l1)

end CFSG.Quasithin.Stroth.G5.K

end

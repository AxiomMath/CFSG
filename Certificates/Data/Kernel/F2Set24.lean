module

public section

namespace CFSG.KC.F2Set24

universe u

@[expose] noncomputable def strict {α : Sort u} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def W : Nat := 16777216

@[expose] noncomputable def par (d : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih x => Bool.xor (Nat.beq (Nat.mod x 2) 1) (ih (Nat.div x 2))) d

@[expose] noncomputable def opApp (o : Nat × Nat) (v : Nat) : Nat :=
  Bool.rec v (Nat.xor v (Nat.shiftLeft 1 o.1)) (par 24 (Nat.land o.2 v))

@[expose] noncomputable def opsApp (ops : List (Nat × Nat)) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun o _ ih v => strict (ih v) (opApp o)) ops v

@[expose] noncomputable def opsWF (ops : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun o _ ih => Nat.blt o.1 24 && Nat.blt o.2 W &&
      Nat.beq (Nat.mod (Nat.shiftRight o.2 o.1) 2) 0 && ih) ops

@[expose] noncomputable def colsOK (ops : List (Nat × Nat)) (c : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih j => Nat.beq (opsApp ops (Nat.shiftLeft 1 j)) x && ih (Nat.succ j)) c

@[expose] noncomputable def opsOK (c : List Nat) (ops : List (Nat × Nat)) : Bool :=
  Nat.beq c.length 24 && opsWF ops && colsOK ops c 0

@[expose] noncomputable def dbl (c : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih w x => strict (Nat.lor x (Nat.shiftLeft x w)) (ih (Nat.mul 2 w))) c

@[expose] noncomputable def pmask (k : Nat) : Nat :=
  dbl (Nat.sub 23 k) (2 ^ (k + 1)) (Nat.shiftLeft (2 ^ 2 ^ k - 1) (2 ^ k))

@[expose] def ks24 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

@[expose] noncomputable def mapRevK {α : Sort u} (f : Nat → Nat) (xs : List Nat) :
    List Nat → (List Nat → α) → α :=
  List.rec (motive := fun _ => List Nat → (List Nat → α) → α) (fun acc k => k acc)
    (fun x _ ih acc k => strict (f x) fun y => ih (y :: acc) k) xs

@[expose] noncomputable def withPms {α : Sort u} (k : List Nat → α) : α :=
  mapRevK pmask ks24.reverse [] k

@[expose] noncomputable def xorSel (pms : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun P _ ih a acc => ih (Nat.div a 2)
      (Bool.rec acc (Nat.xor acc P) (Nat.beq (Nat.mod a 2) 1))) pms

@[expose] noncomputable def opMask (pms : List Nat) (o : Nat × Nat) : Nat :=
  strict (xorSel pms o.2 0) fun X => Nat.xor X (Nat.land X (pms.getD o.1 0))

@[expose] noncomputable def prepK {α : Sort u} (pms : List Nat) (ops : List (Nat × Nat)) :
    List (Nat × Nat) → (List (Nat × Nat) → α) → α :=
  List.rec (motive := fun _ => List (Nat × Nat) → (List (Nat × Nat) → α) → α)
    (fun acc k => k acc)
    (fun o _ ih acc k => strict (opMask pms o) fun m =>
      strict (Nat.shiftLeft 1 o.1) fun s => ih ((s, m) :: acc) k) ops

@[expose] noncomputable def withPrep {α : Sort u} (pms : List Nat) (ops : List (Nat × Nat))
    (k : List (Nat × Nat) → α) : α :=
  prepK pms ops.reverse [] k

@[expose] noncomputable def swp (s m S : Nat) : Nat :=
  (fun t => Nat.xor S (Nat.xor t (Nat.shiftLeft t s)))
    (Nat.land (Nat.xor S (Nat.shiftRight S s)) m)

@[expose] noncomputable def img (P : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun st _ ih S => ih (swp st.1 st.2 S)) P

@[expose] noncomputable def round (P Q : List (Nat × Nat)) (S : Nat) : Nat :=
  Nat.lor S (Nat.lor (img P S) (img Q S))

@[expose] noncomputable def iterK {α : Sort u} (P Q : List (Nat × Nat)) (r : Nat) :
    Nat → (Nat → α) → α :=
  Nat.rec (motive := fun _ => Nat → (Nat → α) → α) (fun S k => k S)
    (fun _ ih S k => strict (round P Q S) fun S' => ih S' k) r

@[expose] noncomputable def popAux (pms : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun P _ ih w c => strict (Nat.xor (2 ^ W - 1) P) fun Q =>
      strict (Nat.add (Nat.land c Q) (Nat.land (Nat.shiftRight c w) Q)) (ih (Nat.mul 2 w))) pms

@[expose] noncomputable def popc (pms : List Nat) (S : Nat) : Nat := popAux pms 1 S

@[expose] noncomputable def finOK (pms : List Nat) (P Q : List (Nat × Nat)) (root n S : Nat) :
    Bool :=
  Nat.beq (round P Q S) S && Nat.beq (Nat.land S (2 ^ root - 1)) 0 && Nat.beq (popc pms S) n

@[expose] noncomputable def orbOK (cP cQ : List Nat) (opsP opsQ : List (Nat × Nat))
    (root n steps : Nat) : Bool :=
  opsOK cP opsP && opsOK cQ opsQ && Nat.blt root W &&
    withPms fun pms => withPrep pms opsP fun P => withPrep pms opsQ fun Q =>
      iterK P Q steps (Nat.shiftLeft 1 root) (finOK pms P Q root n)

end CFSG.KC.F2Set24

end

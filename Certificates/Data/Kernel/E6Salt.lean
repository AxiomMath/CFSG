module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.E6Salt

open CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits CFSG.KC.Loop

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => Bool.rec false ih (f i)) n

@[expose] noncomputable def allL {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => Bool.rec false ih (f x)) l

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] def dataS (A : ℕ) : ℕ :=
  A / 2 ^ 192 % 2 ^ 6084

@[expose] noncomputable def saltOf (r : ℕ) : ℕ :=
  Nat.add (Nat.shiftLeft r 192) (Nat.mod r (Nat.sub (Nat.pow 2 191) 1))

@[expose] noncomputable def maskOfS (s : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.pow 2 192) s) (Nat.sub (Nat.pow 2 64) 1)

@[expose] noncomputable def maskS : ℕ :=
  maskOfS (slots 78)

@[expose] noncomputable def mulSAux (A B : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun q ih =>
    Nat.xor (Nat.mul (Nat.mod (Nat.shiftRight A (Nat.add 192 (Nat.mul 78 q)))
      302231454903657293676544) (Nat.land (Nat.shiftRight B q) maskS)) ih) n

@[expose] noncomputable def mulS (A B : ℕ) : ℕ :=
  strictN (Nat.shiftRight (mulSAux A B 78) 192) saltOf

@[expose] noncomputable def eqS (A B : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.shiftRight A 192) (Nat.pow 2 6084))
    (Nat.mod (Nat.shiftRight B 192) (Nat.pow 2 6084))

@[expose] noncomputable def oneS : ℕ :=
  saltOf oneBits

@[expose] def letterOfCode (c : ℕ) : Letter :=
  if h : c < 6 then .x ⟨c, h⟩ else .n ⟨(c - 6) % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def letS (c : ℕ) : ℕ :=
  saltOf (letterOfCode c).bits

@[expose] noncomputable def letT (LP c : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight LP (Nat.mul 6400 c)) (Nat.pow 2 6400)

@[expose] noncomputable def letOK (LP : ℕ) : Bool :=
  allN 16 fun c => Nat.beq (letT LP c) (letS c)

@[expose] noncomputable def digit (b W m : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight W (Nat.mul b m)) (Nat.pow 2 b)

@[expose] def decW (b W : ℕ) : ℕ → List ℕ
  | 0 => []
  | L + 1 => decW b W L ++ [W / 2 ^ (b * L) % 2 ^ b]

@[expose] noncomputable def wordSAux (LP b W : ℕ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun m ih acc => strictN (mulS (letT LP (digit b W m)) acc) ih) m

@[expose] noncomputable def wordS (LP b W L : ℕ) : ℕ :=
  wordSAux LP b W L oneS

@[expose] noncomputable def powS (A : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) oneS (fun _ acc => mulS acc A) n

end CFSG.KC.E6Salt

end

module

public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.Kernel.Multipliers.Mono
public import CFSG.Certificates.PresentationLetters
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop CFSG.LieType.Multipliers.L34 CFSG.Fischer CFSG.Certificates.CosetEnumeration

@[expose] noncomputable def VT : Nat :=
  nat_lit 2080673533433038323057810417276803754120405937413561865197199386077063984353125965143023977788406335528219923481752356050935519535747045667883707570289087687448438556236736930903149642150984282272045116198589776742810979835300053239184687587636305463318316391189931336389910522088436943829236835745935259584061796672819385318218100186412954318018668276719498564277840882577039222652602831193143579591464246733141165132857437812123690223724441940250661749239316480

@[expose] noncomputable def vtOf (V v c : Nat) : Nat :=
  Nat.land (Nat.shiftRight V (Nat.mul (Nat.add (Nat.mul v (nat_lit 4)) c) (nat_lit 6))) (nat_lit 63)

@[expose] noncomputable def rwalk (V : Nat) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s) (fun c _ ih s => strictN (vtOf V s c) ih) w v

@[expose] noncomputable def rowsOK (V : Nat) (w : List Nat) (s : Nat) : Bool :=
  andB (Nat.beq (rwalk V w (nat_lit 1)) s)
    (andB (Nat.beq (rwalk V w (nat_lit 4)) (Nat.mul (nat_lit 4) s))
      (Nat.beq (rwalk V w (nat_lit 16)) (Nat.mul (nat_lit 16) s)))

@[expose] noncomputable def lamR (r : Nat) : Nat :=
  nIf(Nat.beq r (nat_lit 0), nat_lit 1, nIf(Nat.beq r (nat_lit 1), nat_lit 2, nat_lit 3))

@[expose] noncomputable def lamC (c₃ : Nat) : Nat := lamR (Nat.mod c₃ (nat_lit 3))

@[expose] noncomputable def cvIdOK (V : Nat) (TA TB : Nat → Nat) (w : List Nat) (c₁ c₂ c₃ : Nat) :
    Bool :=
  andB (rowsOK V w (lamC c₃))
    (andB (Nat.beq (Mono.walk TA (nat_lit 4) (nat_lit 4) w (nat_lit 0))
        (Nat.shiftLeft (Nat.mod (Nat.add (Nat.mul (nat_lit 3) c₁) (Nat.mul (nat_lit 2) c₂)) (nat_lit 4))
          (nat_lit 16)))
      (Nat.beq (Mono.walk TB (nat_lit 4) (nat_lit 4) w (nat_lit 0))
        (Nat.shiftLeft (Nat.mod c₂ (nat_lit 4)) (nat_lit 16))))

@[expose] def encV (x : F4 × F4 × F4) : Nat :=
  x.1.code.val + 4 * x.2.1.code.val + 16 * x.2.2.code.val

@[expose] def vecMulM (x : F4 × F4 × F4) (M : Mat3) : F4 × F4 × F4 :=
  (x.1 * M.e00 + x.2.1 * M.e10 + x.2.2 * M.e20, x.1 * M.e01 + x.2.1 * M.e11 + x.2.2 * M.e21,
    x.1 * M.e02 + x.2.1 * M.e12 + x.2.2 * M.e22)

@[expose] def decV (v : Nat) : F4 × F4 × F4 :=
  (⟨⟨v % 4, Nat.mod_lt _ (by decide)⟩⟩, ⟨⟨v / 4 % 4, Nat.mod_lt _ (by decide)⟩⟩,
    ⟨⟨v / 16 % 4, Nat.mod_lt _ (by decide)⟩⟩)

@[expose] def codeMat (c : Nat) : Mat3 :=
  if c = 0 then aMat else if c = 1 then aInvMat else if c = 2 then bMat else bInvMat

@[expose] noncomputable def vtOK (V : Nat) : Bool :=
  Mono.allR (nat_lit 0) (nat_lit 64) fun v => Mono.allR (nat_lit 0) (nat_lit 4) fun c =>
    Nat.beq (vtOf V v c) (encV (vecMulM (decV v) (codeMat c)))

end CFSG.KC.L34Cov

end

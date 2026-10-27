module

public import Certificates.Data.Kernel.G2Three.Rows

public section

namespace CFSG.KD.G2Three

@[expose] noncomputable def s7Gen (GA : Nat → Nat) (k : Nat) : Nat := cond (Nat.blt k 4) (GA k) ONE

@[expose] noncomputable def s7Word (GA : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc k => MUL acc (s7Gen GA k)) ONE

@[expose] noncomputable def s7WordInv (GA : Nat → Nat) (w : List Nat) : Nat :=
  w.reverse.foldl (fun acc k => MUL acc (MUL (s7Gen GA k) (s7Gen GA k))) ONE

@[expose] noncomputable def spanK (I J : Nat) : List Nat :=
  [ONE, MUL I I, I, MUL (MUL I I) I, J, MUL (MUL J J) J, MUL I J, MUL J I]

@[expose] def memK (X : Nat) (L : List Nat) : Bool := L.any fun Y => Nat.beq Y X

@[expose] noncomputable def conjInK (SP : List Nat) (G X : Nat) : Bool :=
  SP.any fun Q => Nat.beq (MUL G X) (MUL Q G)

@[expose] noncomputable def normK (I J G : Nat) : Bool :=
  conjInK (spanK I J) G I && conjInK (spanK I J) G J

@[expose] noncomputable def ord4K (U : Nat) : Bool :=
  Nat.beq (MUL (MUL U U) (MUL U U)) ONE && !(Nat.beq (MUL U U) ONE)

@[expose] noncomputable def normVK (Z W A : Nat) : Bool :=
  conjInK [ONE, Z, W, MUL Z W] A Z && conjInK [ONE, Z, W, MUL Z W] A W

@[expose] noncomputable def classStepK (I J U X XI : Nat) : Bool :=
  let Z := MUL I I
  let W := MUL U U
  let I' := MUL (MUL X I) XI
  let J' := MUL (MUL X J) XI
  Nat.beq (MUL X XI) ONE && Nat.beq (MUL X Z) (MUL W X) &&
    (!(memK U (spanK I' J') && !(memK I' (spanK I J) && memK J' (spanK I J)) &&
        !(normK I J I' && normK I J J')) ||
      (spanK I J).any fun A => (spanK I' J').any fun B =>
        normVK Z W A && normVK Z W B && conjInK (spanK I' J') (MUL A B) I &&
          conjInK (spanK I' J') (MUL A B) J)

@[expose] noncomputable def classCheckK (I J : Nat) (S : List Nat) (XW : List (Nat × Nat)) : Bool :=
  S.all fun U => !ord4K U || XW.any fun p => classStepK I J U p.1 p.2

@[expose] noncomputable def q8InK (L : List Nat) (I₁ J₁ I₂ J₂ : Nat) : Bool :=
  ((L.filter ord4K).map fun a => (a, MUL a a)).all fun a =>
    ((L.filter ord4K).map fun a => (a, MUL a a)).all fun b =>
      !(Nat.beq a.2 b.2 && Nat.beq (MUL (MUL a.1 b.1) a.1) b.1) ||
        (memK a.1 (spanK I₁ J₁) && memK b.1 (spanK I₁ J₁)) ||
        (memK a.1 (spanK I₂ J₂) && memK b.1 (spanK I₂ J₂))

@[expose] noncomputable def s7BasicK (T I₁ J₁ I₂ J₂ : Nat) : Bool :=
  q8K I₁ J₁ && q8K I₂ J₂ && Nat.beq (MUL I₁ I₁) T && Nat.beq (MUL I₂ I₂) T &&
    !memK I₂ (spanK I₁ J₁)

@[expose] noncomputable def s7NormK (I₁ J₁ I₂ J₂ : Nat) (S X : List Nat) : Bool :=
  X.all (normK I₁ J₁) && X.all (normK I₂ J₂) && S.all (normK I₁ J₁) && S.all (normK I₂ J₂)

@[expose] noncomputable def s7K (T I₁ J₁ I₂ J₂ : Nat) (CW : List (Nat × Nat)) (S X : List Nat) :
    Bool :=
  s7BasicK T I₁ J₁ I₂ J₂ && classCheckK I₁ J₁ S CW && classCheckK I₂ J₂ S CW &&
    s7NormK I₁ J₁ I₂ J₂ S X && q8InK S I₁ J₁ I₂ J₂

end CFSG.KD.G2Three

end

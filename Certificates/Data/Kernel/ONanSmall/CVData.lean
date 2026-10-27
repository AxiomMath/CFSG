module

public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Data.Kernel.ONanSmall.PickRun
public import Certificates.Data.Kernel.ONanSmall.EdgeK

public section

namespace CFSG.KC.ONanSmall

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkEnum CFSG.Certificates

instance small11 : Small 11 := ⟨by decide⟩

instance small24 : Small 24 := ⟨by decide⟩

variable {n : ℕ} [Small n]

@[expose] noncomputable def TsC (Q : RawSchreierDatum n) : List (List (CV n)) :=
  (List.finRange Q.baseCount).map fun i => (transV (levelV (strongV Q) Q.base i)).map toCV

@[expose] noncomputable def invC (t : CV n) : Bool := powOneC t 2 && !decide (t = 1)

@[expose] noncomputable def conjC (g t r : CV n) : Bool := eq22C g t r g

@[expose] noncomputable def centC (L : List (CV n)) (t : CV n) : List (CV n) :=
  L.filter fun c => eq22C c t t c

@[expose] noncomputable def pairsVKF (B : ℕ) (LN K : List (CV n)) (e3b : Bool) (t : CV n)
    (C : List (CV n)) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => CFSG.ClassicalInvolution.Q3.TA3.Check.memB
          (CFSG.ClassicalInvolution.Q3.TA3.Check.q8B t a b) (c * a * c⁻¹) &&
        CFSG.ClassicalInvolution.Q3.TA3.Check.memB
          (CFSG.ClassicalInvolution.Q3.TA3.Check.q8B t a b) (c * b * c⁻¹)) ||
      (CFSG.ClassicalInvolution.Q3.TA3.Check.memB LN a &&
        CFSG.ClassicalInvolution.Q3.TA3.Check.memB LN b) ||
      (C.any fun x => powOneC x 3 && !(eq22C x a a x && eq22C x b b x) &&
        C.all fun y => !(eq22C y a a y && eq22C y b b y) || eq22C x y y x) ||
      (edgeK K t a b && (e3b || CFSG.ClassicalInvolution.Q3.TA3.Check.noActs3B B C a b))

@[expose] noncomputable def genC (Q : RawSchreierDatum n) (d : List ℕ) :
    Option (CV n) := genP (TsC Q) d

@[expose] noncomputable def genA (Q : RawSchreierDatum n) (σ : CV n) :
    List ℕ → Option (CV n)
  | 0 :: d => genP (TsC Q) d
  | 1 :: d => (genP (TsC Q) d).map (σ * ·)
  | _ => none

end CFSG.KC.ONanSmall

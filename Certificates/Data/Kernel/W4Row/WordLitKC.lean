module

public import Certificates.Data.Kernel.W4Row.WordLitK
public import CFSG.Certificates.Kernel.Enum.DefsC
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def wordTcC (n w idn : Nat) (G GI : List Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun z _ ih => strictN ih (fun q => pcompC n w (mask w) (letG idn G GI z) q)) wd

theorem wordTc_eq_C (n w idn : Nat) (G GI : List Nat) :
    ∀ wd : List Int, wordTc n w idn G GI wd = wordTcC n w idn G GI wd
  | [] => rfl
  | z :: wd => by
    have e1 : wordTc n w idn G GI (z :: wd) =
        strictN (wordTc n w idn G GI wd) (fun q => pcomp n w (mask w) (letG idn G GI z) q) := rfl
    have e2 : wordTcC n w idn G GI (z :: wd) =
        strictN (wordTcC n w idn G GI wd) (fun q => pcompC n w (mask w) (letG idn G GI z) q) := rfl
    rw [e1, e2, wordTc_eq_C n w idn G GI wd]
    simp only [CFSG.KS.PK.pcompC_eq]

@[expose] noncomputable def wordLitKC (n w : Nat) (G GI : List Nat) (wd : List Int) (Y YI : Nat) :
    Bool :=
  bAnd(Nat.beq (wordTcC n w (pidn n w) G GI wd) Y, permOK n w (mask w) (n * w) Y YI)

theorem wordLitK_eq_C (n w : Nat) (G GI : List Nat) (wd : List Int) (Y YI : Nat) :
    wordLitK n w G GI wd Y YI = wordLitKC n w G GI wd Y YI := by
  unfold wordLitK wordLitKC
  rw [wordTc_eq_C]

end CFSG.KC.W4E

end

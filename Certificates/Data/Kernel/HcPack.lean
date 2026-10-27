module

public import Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23

@[expose] def pk (l : List ℕ) : ℕ := l.foldr (fun a acc => a + 32 * acc) 0

@[expose] def lane (x j : ℕ) : ℕ := x / 32 ^ j % 32

@[expose] noncomputable def mulGo (x : ℕ) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ ih g => lane x (g % 32) + 32 * ih (g / 32)) n

@[expose] noncomputable def mulP (x g : ℕ) : ℕ := mulGo x 32 g

@[expose] def idP : ℕ := pk (List.range 32)

@[expose] noncomputable def bfsP (gs : List ℕ) : List ℕ := bfsAux 576 mulP gs 600 [idP] [idP]

end CFSG.KC.HcPack

end

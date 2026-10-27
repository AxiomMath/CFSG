module

public import Certificates.Data.Kernel.G2Three.Defs
public import Certificates.Data.G23RecogTriNativeInputs
public import Certificates.Data.Th687.SplitTNative

public section

namespace CFSG.KD.G2Three

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.P7 CFSG.Sporadic.Th.Recog

@[expose] noncomputable def wordF (F : Fin 6 × Bool → Nat) (w : List (Fin 6 × Bool)) : Nat :=
  w.foldl (fun c a => MUL c (F a)) ONE

@[expose] noncomputable def recTriK (F : Fin 6 × Bool → Nat) : Bool :=
  triWords.all (fun r => Nat.beq (wordF F (substTri r)) ONE) &&
    (List.finRange 6).all fun i => Nat.beq (wordF F (substTri (triEWord i))) (F (i, true))

@[expose] noncomputable def recThK (F : Fin 6 × Bool → Nat) : Bool :=
  Nat.beq (wordF F (z0Word ++ z0Word)) ONE &&
    !Nat.beq (wordF F z0Word) ONE &&
    (List.finRange 5).all (fun i => Nat.beq (wordF F (z0Word ++ [(Fin.castSucc i, true)]))
      (wordF F ((Fin.castSucc i, true) :: z0Word))) &&
    g23PD.all (fun r => Nat.beq (wordF F (substWord (dEmbed r))) ONE) &&
    !Nat.beq (wordF F (substWord d2mWord)) ONE &&
    Nat.beq (wordF F (substWord (List.flatten (List.replicate 7 d2mWord)))) ONE

end CFSG.KD.G2Three

end

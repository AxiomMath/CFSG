module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Th.F2Spec

@[expose] public section

namespace CFSG.Quasithin.A312He

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.Quasithin.A312Words

def heLetters (j : ℕ) : List (Array ℕ) :=
  heQp.map (fun p => heSLP[p.1]!) ++ (heMwLit[j]!).map (wordTabA #[heTa, heTb] 8330)

def heHat3Xs : List QuotGen := [
  ⟨[4, 0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3, 3, 4, 0, 3, 2, 1, 4], 1, 5⟩,
  ⟨[1, 1, 3, 2, 0, 3, 4, 0, 1, 2, 0, 2, 4, 3, 4, 1, 2, 2, 4, 3, 4, 3, 4, 0], 2, 3⟩,
  ⟨[1, 3, 3, 1, 2, 4, 2, 0, 3, 4, 0, 1, 4, 3, 2, 3, 0, 3, 0, 2, 4, 4, 4, 3, 1, 1, 4, 1], 1, 15⟩,
  ⟨[3, 4, 0, 1, 1, 4, 4, 1, 0, 4, 2, 0, 0, 0, 0, 3, 0, 2, 1, 2, 0, 4, 1, 2], 1, 15⟩]

def heHat3T : QuotGen := ⟨[4, 0, 1, 1, 4, 4, 1, 0, 4, 2, 0, 0, 0, 0, 3, 0], 3, 2⟩

def heHat3Ws : List (List ℕ) :=
  [[6, 1, 7, 1, 2], [1, 0, 8, 0, 8, 3], [0, 1, 6, 0, 8, 2], [3, 8, 7, 7, 2, 8, 0],
    [1, 7, 1, 7, 7, 1]]

def heHat3Pts : List ℕ := [2543, 7220, 4564, 5493, 7637, 6003]

def heHat3W1 : List ℕ := [8, 3]

def heHat3W2 : List ℕ := [8]

def heHat3V : List (List ℕ) :=
  [[3, 1, 2, 1, 3, 6], [2, 3, 1, 3, 1, 6], [7, 5, 3, 6, 7, 2, 0], [3, 5, 0, 5, 0, 7],
    [3, 1, 3, 0, 5, 0], [7, 5, 6, 3, 1, 2]]

def heHat4Xs : List QuotGen := [
  ⟨[4, 0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3, 3, 4, 0, 3, 2, 1, 4], 2, 3⟩,
  ⟨[2, 0, 0, 0, 4, 0, 3, 1, 3, 0, 4, 1, 3, 3, 4, 1], 1, 15⟩]

def heHat4T : QuotGen := ⟨[3, 4, 0, 3, 2, 1, 4, 0, 2, 0, 0, 0, 4, 0, 3, 1], 3, 2⟩

def heHat4Ws : List (List ℕ) :=
  [[1, 2, 4, 3, 2, 3, 3, 3, 3, 0], [3, 4, 2, 3, 2, 3, 4, 2, 1, 0], [0, 3, 3, 4, 0, 1, 0, 3, 3],
    [2, 3, 4, 3, 4, 1, 4, 1, 0], [1, 1, 4, 2, 4, 1, 1, 1, 1, 0]]

def heHat4Pts : List ℕ := [5493, 2859, 4174, 6003, 1323, 1252]

def heHat4W1 : List ℕ := [4, 0]

def heHat4W2 : List ℕ := [1, 1, 4, 0]

def heHat4V : List (List ℕ) :=
  [[1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3], [0, 3, 3, 3, 2, 3, 3, 3, 2, 3, 3, 3, 0],
    [1, 1, 0, 3, 3, 3, 3, 3, 2, 1, 1, 1], [1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 0],
    [1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 0, 1], [1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 0, 1, 0]]

def heExt7Xs : List QuotGen := [
  ⟨[1, 1, 3, 2, 0, 3, 4, 0, 1, 2, 0, 2, 4, 3, 4, 1, 2, 2, 4, 3, 4, 3, 4, 0], 2, 3⟩,
  ⟨[1, 3, 3, 1, 2, 4, 2, 0, 3, 4, 0, 1, 4, 3, 2, 3, 0, 3, 0, 2, 4, 4, 4, 3, 1, 1, 4, 1], 2, 3⟩,
  ⟨[1, 4, 4, 1, 3, 4, 2, 4, 2, 3, 2, 4, 4, 0, 3, 4], 2, 3⟩]

def heExt7T : QuotGen := ⟨[], 1, 2⟩

def heExt7Ws : List (List ℕ) :=
  [[4, 2, 4, 2, 4, 2, 0, 1], [2, 0, 4, 2, 4, 5, 0, 4], [0, 4, 2, 3, 1, 3],
    [0, 1, 5, 3, 4, 0, 4, 2, 0], [3, 1, 0, 2, 0, 5, 3]]

def heExt7W : List (List ℕ) :=
  [[3], [0, 0], [2, 1, 0], [0, 2, 1], [1, 3, 1], [2, 3, 1, 0], [1, 2, 1, 2]]

def heExt7Z : List ℕ := [0, 0]

def HeCertOK : Prop :=
  HatOK 8330 heB (heLetters 3) heHat3Xs heHat3T heHat3Ws heHat3Pts heHat3W1 heHat3W2 heHat3V
      200 64 ∧
    HatOK 8330 heB (heLetters 4) heHat4Xs heHat4T heHat4Ws heHat4Pts heHat4W1 heHat4W2 heHat4V
      200 64 ∧
    ExtraGenOK 8330 heB (heLetters 7) heExt7Xs heExt7T heExt7Ws heExt7W heExt7Z 400 128

instance : Decidable HeCertOK := by unfold HeCertOK; infer_instance

end CFSG.Quasithin.A312He

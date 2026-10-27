module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Defs
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting

@[expose] public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312Words
open CFSG.Quasithin.H.MathieuLat

def m23MwLit : Array (List (List ℕ)) :=
  #[[], [[0]], [[0, 1, 1, 0]], [[1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]],
    [[0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0]], [[0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1]],
    [[0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0]],
    [[1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1]],
    [[1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1]],
    [[0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0]],
    [[1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1]],
    [[0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]],
    [[1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]],
    [[1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1]],
    [[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]],
    [[1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0]]]

def m23Letters (j : ℕ) : List (Array ℕ) :=
  m23STabs ++ (m23MwLit[j]!).map (wordTabA #[m23ta.toArray, m23tb.toArray] 23)

def m23B : List ℕ := List.range 23

def m23Y2Xs : List QuotGen := [
  ⟨[0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3], 1, 5⟩,
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 1, 3⟩,
  ⟨[3, 2, 0, 3, 0, 1, 2, 0, 2, 3, 1, 2], 1, 3⟩]

def m23Y2T : QuotGen := ⟨[1, 0, 0, 3, 1, 1, 0, 0, 3, 1, 0, 2, 3, 0, 3, 0, 2, 2], 7, 2⟩

def m23Y2Ws : List (List ℕ) :=
  [[2, 1, 5, 1, 2], [3, 6, 4, 2, 0, 2], [0, 4, 0, 6, 0, 1], [0, 5, 3, 1, 5, 0, 0]]

def m23Y2Wu : List ℕ := [3, 5, 4, 5, 4, 5, 1, 0]

def m23Y2Wui : List ℕ := [3, 5, 4, 5, 4, 5, 1, 0]

def m23Y2Wv : List ℕ := [4, 5, 1, 2, 3, 1, 2]

def m23Y2Wvi : List ℕ := [0, 0, 4, 5, 0, 0, 1]

def m23Y2Wxs : List (List ℕ) :=
  [[0, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1], [1, 0, 3, 3, 0, 3, 0, 1, 0, 3, 3, 0, 3, 0, 3],
   [3, 0, 1, 0, 1, 0, 3, 3, 0, 3, 0, 3], [3, 0, 3, 0, 1, 1, 0, 1, 0, 3, 0],
   [1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 1, 0, 3], [1, 0, 1, 0, 1, 1, 0, 3, 0, 3, 0, 1]]

def m23Y2Wcj : List (List ℕ) :=
  [[4, 5, 1, 2, 1, 3, 2], [5, 0, 1, 2, 0], [4, 0, 0, 4, 5, 0, 0], [5, 0, 4, 5, 4, 2, 1],
   [3, 5, 4, 3, 2], [5, 1, 2, 3, 1, 2, 1]]

def m23Y3Xs : List QuotGen := [
  ⟨[0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3], 1, 3⟩,
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 1, 5⟩,
  ⟨[3, 2, 0, 3, 0, 1, 2, 0, 2, 3, 1, 2], 1, 5⟩]

def m23Y3T : QuotGen := ⟨[], 1, 2⟩

def m23Y3Ws : List (List ℕ) :=
  [[1, 2, 1, 5, 4, 0, 2], [0, 1, 1, 3, 2, 3], [3, 2, 4, 0, 1, 0], [1, 3, 2, 2, 4, 3]]

def m23Y3Blks : List (List ℕ) :=
  [[0], [5], [9], [15], [16], [18]]

def m23Y3V : List (List ℕ) :=
  [[4, 2, 3, 2, 3, 1], [2, 2, 1, 2, 1, 5], [2, 3, 2, 3], [5, 1, 0, 5, 1, 0]]

def m23Y4Xs : List QuotGen := [
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 1, 7⟩,
  ⟨[3, 3, 0, 3, 1, 3, 3, 1, 2, 2, 0, 3, 0, 1, 3, 2], 1, 7⟩]

def m23Y4T : QuotGen := ⟨[], 1, 2⟩

def m23Y4Ws : List (List ℕ) :=
  [[3, 3, 2, 3, 0, 1, 1, 0], [2, 2, 2, 1, 1, 2, 1], [0, 0, 3, 3, 3, 2, 1, 0],
   [1, 1, 2, 3, 3, 2, 1, 0]]

def m23Y4Blks : List (List ℕ) :=
  [[0], [4], [5], [9], [15], [16], [18]]

def m23Y4V : List (List ℕ) :=
  [[1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 0, 0, 3, 0], [1, 2, 1, 1, 2, 1], [1, 2, 1, 1, 1, 2, 1, 0]]

def m23Y5Xs : List QuotGen := [
  ⟨[0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3], 1, 7⟩,
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 1, 7⟩]

def m23Y5T : QuotGen := ⟨[], 1, 2⟩

def m23Y5Ws : List (List ℕ) :=
  [[1, 2, 3, 0, 1, 1, 1, 0, 1, 0], [3, 0, 0, 3, 3, 2, 3, 2, 2, 1], [3, 0, 3, 3, 0, 0, 0],
   [2, 1, 1, 1, 0, 1, 2, 3, 0, 1]]

def m23Y5Blks : List (List ℕ) :=
  [[0], [4], [5], [9], [15], [16], [18]]

def m23Y5V : List (List ℕ) :=
  [[1, 2, 1, 0, 0, 0, 3, 0, 0, 1, 0, 0], [1, 2, 1, 0, 1, 0, 1, 0, 0, 3],
   [3, 0, 0, 1, 0, 1, 0, 1, 2, 1], [0, 1, 0, 1, 0, 1]]

def m23Y6Xs : List QuotGen := [
  ⟨[0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3], 2, 3⟩,
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 2, 7⟩]

def m23Y6T : QuotGen := ⟨[1, 0, 0, 2, 3, 1, 0, 2, 1, 0, 0, 1, 2, 3, 0, 3, 0, 1], 7, 2⟩

def m23Y6Ws : List (List ℕ) :=
  [[0, 3, 3, 2, 1, 2, 1], [1, 0, 4, 1, 0, 1, 0], [3, 0, 1, 1, 2, 3, 0], [0, 3, 3, 3, 2, 1, 1]]

def m23Y6Blks : List (List ℕ) :=
  [[0], [4], [5], [9], [15], [16], [18]]

def m23Y6V : List (List ℕ) :=
  [[1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 1], [1, 1, 1, 0, 1, 1, 0, 3]]

def m23Y6Wcj : List (List ℕ) :=
  [[0, 1, 0, 1, 1, 0, 1], [1], [3, 2, 3, 0, 1, 0, 1], [3]]

def m23Y6Wit : List ℕ := [1, 2, 3, 8, 10, 13, 21, 22]

def m23Y7Xs : List QuotGen := [
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 1, 3⟩,
  ⟨[3, 2, 0, 3, 0, 1, 2, 0, 2, 3, 1, 2], 1, 3⟩,
  ⟨[3, 3, 0, 3, 1, 3, 3, 1, 2, 2, 0, 3, 0, 1, 3, 2], 1, 5⟩]

def m23Y7T : QuotGen := ⟨[3, 0, 1, 0, 1, 0, 3, 2, 1, 1], 3, 2⟩

def m23Y7Ws : List (List ℕ) :=
  [[6, 4, 6, 4], [4, 5, 6, 2, 2], [1, 5, 1, 6, 2], [0, 5, 0]]

def m23Y7Blks : List (List ℕ) :=
  [[0, 5, 9, 16], [1, 8, 10, 22], [2, 3, 13, 21], [6, 7, 12, 20], [11, 14, 17, 19]]

def m23Y7V : List (List ℕ) :=
  [[1, 5, 0, 5, 5, 0], [2, 4, 3, 2, 2, 3], [5, 5, 0, 1, 5, 0], [2, 2, 1, 2, 2, 1]]

def m23Y7Wcj : List (List ℕ) :=
  [[3, 2, 2, 0, 5], [2, 3, 4, 5], [0, 5, 0, 2], [2, 2, 0, 5, 0], [2, 1, 0, 5], [5, 0, 5, 0]]

def m23Y7Wit : List ℕ := [15]

def m23Y9Xs : List QuotGen := [
  ⟨[0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3], 1, 5⟩,
  ⟨[0, 3, 2, 1, 0, 2, 0, 0, 0, 0, 3, 1, 3, 0, 1, 3, 3, 1, 2, 1], 1, 5⟩,
  ⟨[3, 3, 0, 3, 1, 3, 3, 1, 2, 2, 0, 3, 0, 1, 3, 2], 1, 3⟩]

def m23Y9T : QuotGen := ⟨[1, 0, 3, 1, 3, 2], 3, 2⟩

def m23Y9Ws : List (List ℕ) :=
  [[5, 1, 0, 2], [6, 1, 2, 4], [0, 6, 3], [6, 0, 6, 4]]

def m23Y9Blks : List (List ℕ) :=
  [[0], [4], [5], [9], [16]]

def m23Y9V : List (List ℕ) :=
  [[2, 0, 4, 0, 2], [3, 5, 0, 4, 0, 0], [2, 3, 1, 3], [1, 0, 2, 4, 0, 0]]

def m23Y9Wcj : List (List ℕ) :=
  [[3, 5, 3, 1, 0], [3, 3, 2, 1, 2], [1, 0, 5], [5, 3, 1, 0, 0], [5, 4, 5, 0, 0], [2, 1, 0]]

def m23Y9Wit : List ℕ := [15]

def m23Y1Blks : List (List ℕ) :=
  [[0], [1], [2], [5], [8], [11], [22], [19], [20], [3], [12], [14], [21], [17], [6], [18], [13],
   [10], [9], [16], [7], [15]]

def m23Y1WA : List ℕ := [1, 3, 2, 0, 2, 1, 1, 3, 2, 1, 0, 2]

def m23Y1WB : List ℕ := [1, 3, 2, 3, 1, 3, 0, 1, 1, 1, 3, 2]

def m23Y8Blks : List (List ℕ) :=
  [[4], [15], [18]]

def m23Y8X : QuotGen := ⟨[1, 3, 0, 1, 0, 1, 3, 2, 1, 3], 1, 15⟩

def m22TabA : Array ℕ :=
  #[12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

def m22TabB : Array ℕ :=
  #[21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

def m23Rels : List (List (ℕ × Bool)) :=
  CFSG.LieType.Multipliers.L34.rels.map (List.map fun l => (l.1.val, l.2))

def M23CertOK : Prop :=
  m23Lat.mw = m23MwLit ∧
    M22OK 23 (m23Letters 1) m23Y1Blks m23Y1WA m23Y1WB m22TabA m22TabB ∧
    L34OK 23 (m23Letters 2) m23Y2Xs m23Y2T m23Y2Ws m23Y2Wcj m23Rels m23Y2Wu m23Y2Wui m23Y2Wv
      m23Y2Wvi m23Y2Wxs ∧
    E2PermOK 23 m23B (m23Letters 3) m23Y3Xs m23Y3T m23Y3Ws m23Y3Blks m23Y3V 100 16 5000 360
      5760 ∧
    (E2PermOK 23 m23B (m23Letters 4) m23Y4Xs m23Y4T m23Y4Ws m23Y4Blks m23Y4V 100 16 5000 168
      2688 ∧ ImgTransOK 23 (m23Letters 4) m23Y4Xs m23Y4Blks 5000) ∧
    E2PermOK 23 m23B (m23Letters 5) m23Y5Xs m23Y5T m23Y5Ws m23Y5Blks m23Y5V 100 16 20000 2520
      40320 ∧
    (E2AltOK 23 m23B (m23Letters 6) m23Y6Xs m23Y6T m23Y6Ws m23Y6Wcj m23Y6Wit m23Y6Blks m23Y6V
      100 8 5000 168 2688 ∧ ImgTransOK 23 (m23Letters 6) m23Y6Xs m23Y6Blks 5000) ∧
    E2AltOK 23 m23B (m23Letters 7) m23Y7Xs m23Y7T m23Y7Ws m23Y7Wcj m23Y7Wit m23Y7Blks m23Y7V
      100 16 5000 60 1920 ∧
    E2AltOK 23 m23B (m23Letters 9) m23Y9Xs m23Y9T m23Y9Ws m23Y9Wcj m23Y9Wit m23Y9Blks m23Y9V
      100 16 5000 60 1920 ∧
    TriOK 23 (m23Letters 8) m23Y8Blks m23Y8X

instance : Decidable M23CertOK := by unfold M23CertOK; infer_instance

end CFSG.Quasithin.A312M23

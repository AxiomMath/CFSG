module

public import Certificates.Data.Kernel.ONanCMK
public import Certificates.Data.ONanB2Tabs

public section

namespace CFSG.OddStandard.ONanRec.B2K

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK

@[expose] def b2Base : List Nat := [0, 56, 2]

@[expose] noncomputable def eqB (u v : List Nat) : Bool :=
  b2Base.all fun b => ptK u b == ptK v b

@[expose] noncomputable def allNeB : List (List Nat) → Bool
  | [] => true
  | u :: us => us.all (fun v => !eqB u v) && allNeB us

@[expose] def incK : List Nat → Bool
  | a :: b :: l => Nat.blt a b && incK (b :: l)
  | _ => true

@[expose] noncomputable def orbKey (rs : List (List Nat)) (ps : List (Nat × Nat))
    (w : List Nat) : Nat :=
  ps.foldl (fun acc cp => acc * 480 + ptK (w ++ rs.getD cp.1 [] ++ invWord w) cp.2) 0

@[expose] noncomputable def orbK (rs : List (List Nat)) (ps : List (Nat × Nat)) (n : Nat)
    (ws : List (List Nat)) : Bool :=
  ws.length == n && ws.all (fun w => w.all fun c => Nat.blt c 12) && incK (ws.map (orbKey rs ps))

@[expose] def ptsR : List (Nat × Nat) := [(0, 0), (0, 2), (0, 4)]

@[expose] def ptsS : List (Nat × Nat) := [(1, 0), (1, 2), (0, 0), (1, 4)]

@[expose] noncomputable def fzK : Bool :=
  ((List.range 6).all fun i => eqB ([2 * i] ++ fW) (fW ++ [2 * i])) && eqB (zW ++ zW) fW &&
    ((List.range 6).all fun i => eqB ([2 * i] ++ zW ++ [2 * i + 1]) zW ||
      eqB ([2 * i] ++ zW ++ [2 * i + 1]) (invWord zW))

@[expose] noncomputable def rK : Bool :=
  eqB (wpow r1W 3) [] && eqB (wpow r2W 3) [] && eqB (r1W ++ r2W) (r2W ++ r1W) && allNeB rWords &&
    eqB (yW ++ r1W ++ invWord yW) (rW 0 2) && eqB (yW ++ r2W ++ invWord yW) (rW 1 0)

@[expose] noncomputable def irredK : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j => (i == 0 && j == 0) ||
    (!eqB (yW ++ rW i j ++ invWord yW) [] && !eqB (yW ++ rW i j ++ invWord yW) (rW i j) &&
      !eqB (yW ++ rW i j ++ invWord yW) (rW i j ++ rW i j))

@[expose] noncomputable def sK : Bool :=
  eqB (zW ++ r1W) (r1W ++ zW) && eqB (zW ++ r2W) (r2W ++ zW) && eqB (dW ++ r1W) (r1W ++ dW) &&
    eqB (dW ++ r2W) (r2W ++ dW) && eqB (wpow zW 4) [] && !eqB (zW ++ zW) [] &&
    eqB (dW ++ dW) [] && eqB (dW ++ zW ++ dW) (invWord zW) &&
    !((List.range 4).any fun k => eqB dW (wpow zW k))

@[expose] noncomputable def tK : Bool :=
  allNeB (tIdx.map tWord) &&
    (tIdx.all fun l => tGens.all fun s => tIdx.any fun l' => eqB (tWord l ++ s) (tWord l')) &&
    (tGens.all fun s => [r1W, r2W].all fun r =>
      rWords.any (eqB (s ++ r ++ invWord s)) && rWords.any (eqB (invWord s ++ r ++ s)))

@[expose] noncomputable def tCentK : Bool :=
  (tIdx.all fun l =>
    !(eqB (tWord l ++ zW) (zW ++ tWord l) && eqB (tWord l ++ dW) (dW ++ tWord l)) ||
      qWords.any (eqB (tWord l))) &&
  ([yW, yW ++ fW].all fun w => tIdx.all fun l =>
    !((wPowWords w).any (eqB (tWord l ++ tWord l))) || (swWords w).any (eqB (tWord l)))

@[expose] noncomputable def yK : Bool :=
  eqB (wpow yW 4) [] && !eqB (yW ++ yW) [] && eqB (yW ++ zW) (zW ++ yW) &&
    eqB (yW ++ dW) (dW ++ yW)

@[expose] def csWords : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    (List.range 4).flatMap fun k => (List.range 2).map fun l => rW i j ++ wpow yW k ++ wpow fW l

@[expose] noncomputable def centK : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j => (List.range 4).all fun k =>
    (List.range 2).all fun l => (i == 0 && j == 0 && l == 0 && (k == 0 || k == 2)) ||
      (List.range 6).any fun a => !eqB (rW i j ++ sW k l ++ [2 * a]) ([2 * a] ++ (rW i j ++ sW k l))

@[expose] def cW (i j k l : Nat) : List Nat := rW i j ++ wpow yW k ++ wpow fW l

@[expose] noncomputable def ordK : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j => [0, 2].all fun k =>
    (List.range 2).all fun l => !eqB (wpow (cW i j k l) 4) [] || eqB (cW i j k l ++ cW i j k l) []

end CFSG.OddStandard.ONanRec.B2K

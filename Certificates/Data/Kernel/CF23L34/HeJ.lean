module

public import Certificates.Data.Kernel.CF23L34.Slp
public import Certificates.Data.GrSLitL34FactsCF23HeCheck

public section

namespace CFSG.KC.CF23L34

open CFSG.KC.Enum CFSG.KS CFSG.ComponentClassification.GSThmB.CF23L34
open CFSG.LieType.Multipliers.L34 CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def hjKeep : List ℕ :=
  [32, 86, 103, 173, 216, 217, 226, 227, 250, 277, 278, 279, 280, 281, 282]

@[expose] def hjInvJ : List ℕ := [0, 1, 2, 3, 4, 5, 7, 9, 10, 11]


@[expose] def hjPos (a : ℕ) : ℕ := if a = 1 then 0 else if a = 2 then 2 else 4 + 2 * hjKeep.idxOf a

@[expose] def hjIdx (z : ℤ) : ℕ := hjPos z.natAbs + if z < 0 then 1 else 0

@[expose] def hjCl (l : Fin 2 × Bool) : ℤ :=
  if l.1.val = 0 then (if l.2 then 250 else -250) else (if l.2 then 277 else -277)

@[expose] def hjCw (w : List (Fin 2 × Bool)) : List ℤ := w.map hjCl

@[expose] def hjX (r : ℤ) : List ℤ := frz (slpX hjProg hjKeep 400 r)

@[expose] def hjD (r : ℕ) : List ℤ := slpR hjProg hjKeep 400 r

@[expose] noncomputable def hjTr (T : Nat → Nat) (L : List ℤ) (x : Nat) : Nat := tzK 14 T hjIdx L x

@[expose] noncomputable def hjEqB (T : Nat → Nat) (L₁ L₂ : List ℤ) : Bool :=
  allN 5 (fun b => Nat.beq (hjTr T L₁ b) (hjTr T L₂ b))

@[expose] noncomputable def hjNeAt (T : Nat → Nat) (L₁ L₂ : List ℤ) (x : Nat) : Bool :=
  bIf(Nat.beq (hjTr T L₁ x) (hjTr T L₂ x), false, true)

@[expose] noncomputable def hjTabOK (T : Nat → Nat) (j : Nat) : Bool :=
  Nat.beq (wzK 8330 14 T hjIdx (hjD (hjKeep.getD j 0))) (T (Nat.add 4 (Nat.mul 2 j)))

@[expose] noncomputable def hjInvOK (T : Nat → Nat) (j : Nat) : Bool :=
  bAnd(permOK 8330 14 (mask 14) (8330 * 14) (T (Nat.mul 2 j)) (T (Nat.add (Nat.mul 2 j) 1)),
    permOK 8330 14 (mask 14) (8330 * 14) (T (Nat.add (Nat.mul 2 j) 1)) (T (Nat.mul 2 j)))

@[expose] def hjLabW (l : ℕ × ℕ × ℕ × ℤ) : List ℤ × List ℤ :=
  (hjX l.2.2.2 ++ [1], 1 :: (hjCw (tw l.1) ++ (if l.2.1 = 1 then hjCw zOne else []) ++
    (if l.2.2.1 = 1 then [1] else []) ++ hjX l.2.2.2))

@[expose] noncomputable def hjLabK (T : Nat → Nat) (l : ℕ × ℕ × ℕ × ℤ) : Bool :=
  hjEqB T (hjLabW l).1 (hjLabW l).2

@[expose] def hjRelW : List (List (Fin 2 × Bool)) := coverWs ++ [zThree]

end CFSG.KC.CF23L34

end

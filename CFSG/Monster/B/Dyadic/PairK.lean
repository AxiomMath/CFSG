module

public import CFSG.Monster.B.Dyadic.FactsA0
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerData
public import Certificates.Data.Kernel.BabyMonster.Pair24
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
public import CFSG.Certificates.Kernel.BabyMonster.SoundDefs
public import CFSG.Monster.B.Pinned.GeneratorDeterminantsBase

public section

namespace CFSG.Monster.B.Dyadic

@[expose] noncomputable def QnK (j : ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  if h : j < 26 then Qmat ⟨j, h⟩ else 1

@[expose] noncomputable def BWK : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  (CFSG.Monster.B.Bin.conjWord24.map fun j => QnK (j - 1)).prod

@[expose] noncomputable def F0K : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Matrix.of F0row

@[expose] noncomputable def FK : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  CFSG.KC.BM.stripMat CFSG.KC.BM.NativePair24.F

@[expose] noncomputable def TK : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  CFSG.KC.BM.stripMat CFSG.KC.BM.NativePair24.T

@[expose] noncomputable def probeProdK {M : Type*} [Monoid M] (a b : M) : M :=
  (CFSG.Monster.B.Bin.probeWord.map fun l => if l then a else b).prod

@[expose] noncomputable def rowsK (R : List (List ℕ)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) :=
  Matrix.of fun j t => if (CFSG.KC.BM.Lat.recOf R j).testBit t then 1 else 0

@[expose] def FactPair : Prop :=
  (BWK * FK = F0K * BWK ∧
    F0K * F0K = 1 ∧ F0K ≠ 1 ∧ (F0K - 1).rank = 2158 ∧
    FK * TK = TK * genA₁ ∧ Qmat 25 * TK = TK * genA₂ ∧
    FK * FK = 1 ∧ Qmat 25 ^ 3 = 1 ∧ Qmat 25 ≠ 1 ∧
    (FK * Qmat 25) ^ 55 = 1 ∧ (FK * Qmat 25) ^ 5 ≠ 1 ∧ (FK * Qmat 25) ^ 11 ≠ 1 ∧
    probeProdK FK (Qmat 25) ≠ 1 ∧ probeProdK FK (Qmat 25) ^ 23 = 1) ∧
  FK = rowsK CFSG.KC.BM.NativePair24.F.rows ∧ TK = rowsK CFSG.KC.BM.NativePair24.T.rows

end CFSG.Monster.B.Dyadic

end

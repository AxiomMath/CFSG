module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

@[expose] def oPhiMatZ : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of ![![1, 0, 0, 0], ![0, -1, 1, -1], ![0, 1, -1, -1], ![0, 1, 1, 0]]

@[expose] def oPhiOrbitGens : List (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  [diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1, oPhiMatZ]

@[expose] def oPhiQ (v : Fin 4 → ZMod 3) : ZMod 3 :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 - v 3 ^ 2

@[expose] def oPhiNormNegOne : Finset (Fin 4 → ZMod 3) :=
  Finset.univ.filter (fun v => oPhiQ v = -1)

@[expose] def oPhiOrbitStep (s : Finset (Fin 4 → ZMod 3)) : Finset (Fin 4 → ZMod 3) :=
  s ∪ s.biUnion (fun v => (oPhiOrbitGens.map (fun M => M.mulVec v)).toFinset)

@[expose] def oPhiOrbitLevels : ℕ → Finset (Fin 4 → ZMod 3)
  | 0 => {![0, 0, 0, 1]}
  | n + 1 => oPhiOrbitLevels n ∪ oPhiOrbitStep (oPhiOrbitLevels n)

theorem oPhiOrbitLevels_ten : oPhiOrbitLevels 10 = oPhiNormNegOne := by
  decide +kernel

theorem oPhiNormOneVectors :
    ∀ x : Fin 4 → ZMod 3, x 3 = 0 → x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 →
      ∃ i : Fin 4, x = Pi.single i 1 ∨ x = -Pi.single i 1 := by
  decide +kernel

@[expose] def oPhiStabGens : List (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  [diagSignMat 0, pijMat 0 1 1, pijMat 1 2 1]

@[expose] def oPhiSignedPermMat (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ZMod 3) :
    Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  fun i j => if σ j = i then ε j else 0

@[expose] def oPhiSignedPerms : Finset (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  (Finset.univ.filter (fun p : Equiv.Perm (Fin 4) × (Fin 4 → ZMod 3) =>
    p.1 3 = 3 ∧ p.2 3 = 1 ∧ ∀ i, p.2 i = 1 ∨ p.2 i = -1)).image
    (fun p => oPhiSignedPermMat p.1 p.2)

@[expose] def oPhiStabStep (s : Finset (Matrix (Fin 4) (Fin 4) (ZMod 3))) :
    Finset (Matrix (Fin 4) (Fin 4) (ZMod 3)) :=
  s ∪ s.biUnion (fun M => (oPhiStabGens.map (fun N => M * N)).toFinset)

@[expose] def oPhiStabLevels : ℕ → Finset (Matrix (Fin 4) (Fin 4) (ZMod 3))
  | 0 => {1}
  | n + 1 => oPhiStabLevels n ∪ oPhiStabStep (oPhiStabLevels n)

@[expose] def oPhiColsMat (k : Fin 3 → Fin 4) (s : Fin 3 → Bool) :
    Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  fun i j => Fin.lastCases ((Pi.single 3 (1 : ZMod 3) : Fin 4 → ZMod 3) i)
    (fun j' => ((if s j' then (-1 : ZMod 3) else 1)) *
      ((Pi.single (k j') (1 : ZMod 3) : Fin 4 → ZMod 3) i)) j

theorem oPhiColsMat_mem_signedPerms :
    ∀ (k : Fin 3 → Fin 4), (∀ j, k j ≠ 3) → Function.Injective k →
      ∀ s : Fin 3 → Bool, oPhiColsMat k s ∈ oPhiSignedPerms := by
  decide +kernel

theorem oPhiSignedPerms_subset :
    oPhiSignedPerms ⊆ oPhiStabLevels 10 := by
  decide +kernel

end CFSG.StandardType.ZS

end

module

public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Monster.B.Dyadic.Max2K
public import CFSG.Monster.B.Intertwiner.RankSpec
public import Certificates.Certificate3045

public section

namespace CFSG.Monster.B

open Bin Matrix

@[expose] noncomputable def Qn (j : ℕ) : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Dyadic.QnK j

theorem Qn_eq (g : Fin 26) : Qn g = Dyadic.Qmat g := by
  rw [Qn, Dyadic.QnK, dite_eq_left g.2]

@[expose] noncomputable def F0mat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Dyadic.F0K

@[expose] noncomputable def Fmat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Dyadic.FK

@[expose] noncomputable def BWmat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Dyadic.BWK

theorem BWmat_eq : BWmat = (conjWord24.map fun j => Qn (j - 1)).prod := rfl

theorem Tmat_eq : Tmat = Dyadic.TK := rfl

@[expose] noncomputable def probeProd {M : Type*} [Monoid M] (a b : M) : M :=
  (probeWord.map fun l => if l then a else b).prod

theorem sub_one_eq_add_one {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) : M - 1 = M + 1 := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply]
  generalize M i j = a
  generalize (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i j = b
  revert a b
  decide

theorem pair_matrix_facts :
    BWmat * Fmat = F0mat * BWmat ∧
    F0mat * F0mat = 1 ∧ F0mat ≠ 1 ∧ (F0mat - 1).rank = 2158 ∧
    Fmat * Tmat = Tmat * genA₁ ∧ Dyadic.Qmat 25 * Tmat = Tmat * genA₂ ∧
    Fmat * Fmat = 1 ∧ Dyadic.Qmat 25 ^ 3 = 1 ∧ Dyadic.Qmat 25 ≠ 1 ∧
    (Fmat * Dyadic.Qmat 25) ^ 55 = 1 ∧ (Fmat * Dyadic.Qmat 25) ^ 5 ≠ 1 ∧
    (Fmat * Dyadic.Qmat 25) ^ 11 ≠ 1 ∧
    probeProd Fmat (Dyadic.Qmat 25) ≠ 1 ∧ probeProd Fmat (Dyadic.Qmat 25) ^ 23 = 1 :=
  Certificates.certificate3045.1

theorem pair_file_facts :
    Fmat = Dyadic.rowsK KC.BM.NativePair24.F.rows ∧ Tmat = Dyadic.rowsK KC.BM.NativePair24.T.rows :=
  Certificates.certificate3045.2

end CFSG.Monster.B

end

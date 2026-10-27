module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddLevi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Gl2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
include hF hp2

@[expose] noncomputable def blkHom :
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) →*
      Matrix (Fin 2) (Fin 2) F where
  toFun x := !![mat3 x.1 0 0, mat3 x.1 0 2; mat3 x.1 2 0, mat3 x.1 2 2]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat3]
  map_mul' := fun x y => by
    have hx := offblock_of_commute_zSU hF hp2 (Subgroup.mem_centralizer_singleton_iff.1 x.2)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Subgroup.coe_mul, mat3_mul, Matrix.mul_apply, Fin.sum_univ_three, hx.1, hx.2.2.2]

theorem false_of_commute_zSU (h7 : (7 : F) ≠ 0) {a y : SU (unitaryInvolution F p f) 3}
    (ha : a * zSU hF = zSU hF * a) (hy : y * zSU hF = zSU hF * y) (ha7 : a ^ 7 = 1)
    (ha1 : a ≠ 1) (hya : y * a * y⁻¹ = a ^ 2) : False := by
  let A : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) :=
    ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha⟩
  let Y : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) :=
    ⟨y, Subgroup.mem_centralizer_singleton_iff.2 hy⟩
  refine CFSG.LocalAnalysis.RankThreeUC.S15.F1Proof.false_of_conj_pow_two h7
    (x := (blkHom hF hp2).toHomUnits A) (y := (blkHom hF hp2).toHomUnits Y) ?_ ?_ ?_
  · rw [← map_pow]
    have : A ^ 7 = 1 := Subtype.ext (by simpa [A] using ha7)
    rw [this, map_one]
  · intro h
    have h' := congrArg Units.val h
    rw [MonoidHom.coe_toHomUnits, Units.val_one] at h'
    have hx := offblock_of_commute_zSU hF hp2 ha
    have e00 := congrFun (congrFun h' 0) 0
    have e02 := congrFun (congrFun h' 0) 1
    have e20 := congrFun (congrFun h' 1) 0
    have e22 := congrFun (congrFun h' 1) 1
    simp [blkHom, A] at e00 e02 e20 e22
    have hdet : (mat3 a).det = 1 := a.2.1
    simp [Matrix.det_fin_three, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, e00, e02, e20, e22] at hdet
    apply ha1
    apply mat3_injective
    rw [show mat3 (1 : SU (unitaryInvolution F p f) 3) = 1 from rfl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, e00, e02, e20, e22, hdet]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    congr 1
    exact Subtype.ext hya

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

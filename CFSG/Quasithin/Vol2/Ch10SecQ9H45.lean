module

public import CFSG.Quasithin.Vol2.Ch10SecKRSa
public import CFSG.Quasithin.Vol2.Ch10SecQ9H30

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

abbrev blk23 (g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  topB (m := 2) (k := 1) (botB (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)))

theorem P2_le_stabStd23 : KRS.P2 ≤ stabStd 2 3 := fun g hg i j => by
  show (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (Fin.natAdd 2 i) (Fin.castAdd 3 j) = 0
  exact hg (by fin_cases i <;> fin_cases j <;> decide)

theorem botB_presStd_of_P2 {g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)} (hg : g ∈ KRS.P2) :
    PresStd (m := 2) (k := 1) (botB (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) :=
  fun i j => by
    show (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) (Fin.natAdd 2 (Fin.natAdd 2 i))
      (Fin.natAdd 2 (Fin.castAdd 1 j)) = 0
    exact hg (by fin_cases i; fin_cases j <;> decide)

theorem blk23_mul {g h : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)} (hg : g ∈ KRS.P2)
    (hh : h ∈ KRS.P2) : blk23 (g * h) = blk23 g * blk23 h := by
  simp only [blk23]
  rw [Matrix.SpecialLinearGroup.coe_mul, botB_mul (P2_le_stabStd23 hg),
    topB_mul (botB_presStd_of_P2 hh)]

theorem blk23_one : blk23 1 = 1 := by
  simp only [blk23]
  rw [Matrix.SpecialLinearGroup.coe_one, botB_one, topB_one]

@[expose] def radP2 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) where
  carrier := {g | g ∈ KRS.P2 ∧ blk23 g = 1}
  one_mem' := ⟨KRS.P2.one_mem, blk23_one⟩
  mul_mem' := fun ha hb => ⟨KRS.P2.mul_mem ha.1 hb.1, by
    rw [blk23_mul ha.1 hb.1, ha.2, hb.2, Matrix.mul_one]⟩
  inv_mem' := fun {g} ha => ⟨KRS.P2.inv_mem ha.1, by
    have := blk23_mul ha.1 (KRS.P2.inv_mem ha.1)
    rw [mul_inv_cancel, blk23_one, ha.2, Matrix.one_mul] at this
    exact this.symm⟩

theorem conj_mem_radP2 {p r : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)} (hp : p ∈ KRS.P2)
    (hr : r ∈ radP2) : p * r * p⁻¹ ∈ radP2 := by
  have hpi := KRS.P2.inv_mem hp
  refine ⟨KRS.P2.mul_mem (KRS.P2.mul_mem hp hr.1) hpi, ?_⟩
  rw [blk23_mul (KRS.P2.mul_mem hp hr.1) hpi, blk23_mul hp hr.1, hr.2, Matrix.mul_one,
    ← blk23_mul hp hpi, mul_inv_cancel, blk23_one]

theorem radP2_le_uniSL : radP2 ≤ uniSL 5 := by
  intro g hg
  have h4 : g ∈ stabStd 4 1 := fun i j => hg.1 (by fin_cases i; fin_cases j <;> decide)
  have h44 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 4 = 1 :=
    congrFun (congrFun (botB_eq_one_of_one ⟨g, h4⟩) 0) 0
  obtain ⟨h00, h11⟩ := KRS.P2_diag hg.1
  have hb : blk23 g = 1 := hg.2
  have h22 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 2 = 1 := congrFun (congrFun hb 0) 0
  have h33 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 3 = 1 := congrFun (congrFun hb 1) 1
  have h32 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 2 = 0 := congrFun (congrFun hb 1) 0
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hij' (by decide)
        | exact h32
        | exact hg.1 (by decide)
  · fin_cases i
    · exact h00
    · exact h11
    · exact h22
    · exact h33
    · exact h44

abbrev tP2 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  trvE 2 3 (by decide) * trvE 3 2 (by decide)

abbrev wP2 : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  trvE 0 2 (by decide) * (tP2 * tP2) * trvE 0 2 (by decide)

theorem trvE03_eq : (trvE (0 : Fin 5) 3 (by decide) : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) =
    tP2 * wP2 := by
  decide

theorem tP2_mem : tP2 ∈ KRS.P2 := by
  show ∀ i j : Fin 5, (![0, 1, 2, 2, 3] : Fin 5 → ℕ) j < ![0, 1, 2, 2, 3] i →
    (tP2 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0
  decide

theorem wP2_mem : wP2 ∈ KRS.P2 := by
  show ∀ i j : Fin 5, (![0, 1, 2, 2, 3] : Fin 5 → ℕ) j < ![0, 1, 2, 2, 3] i →
    (wP2 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = 0
  decide

theorem trvE03_mem_radP2 : trvE (0 : Fin 5) 3 (by decide) ∈ radP2 := by
  refine ⟨?_, by decide⟩
  rw [trvE03_eq]
  exact KRS.P2.mul_mem tP2_mem wP2_mem

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

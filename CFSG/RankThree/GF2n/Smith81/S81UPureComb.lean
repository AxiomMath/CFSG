module

public import CFSG.RankThree.GF2n.Smith81.S81NBasis

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube exteriorPower

variable {F : Type} [Field F] [CharP F 2]

private theorem pc_ι3_e_eq_ub {a b c : Fin 6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i j k : Fin 6) (hij : i < j) (hjk : j < k)
    (hI : ({i, j, k} : Finset (Fin 6)) = {a, b, c}) :
    ιMulti F 3 ![e F a, e F b, e F c] = ub F i j k hij hjk :=
  ι3_e_eq_cubeBasis hab hac hbc (tripleSet i j k hij.ne (hij.trans hjk).ne hjk.ne) hI

private theorem pc_ι_024 : ιMulti F 3 ![e F 0, e F 2, e F 4] = ub F 0 2 4 :=
  pc_ι3_e_eq_ub (by decide) (by decide) (by decide) 0 2 4 (by decide) (by decide) (by decide)

private theorem pc_ι_025 : ιMulti F 3 ![e F 0, e F 2, e F 5] = ub F 0 2 5 :=
  pc_ι3_e_eq_ub (by decide) (by decide) (by decide) 0 2 5 (by decide) (by decide) (by decide)

theorem isPure_comb_024_025 (c1 c2 : F) : IsPure F (c1 • ub F 0 2 4 + c2 • ub F 0 2 5) := by
  refine ⟨![e F 0, e F 2, c1 • e F 4 + c2 • e F 5], ?_⟩
  rw [ι3_add_thd, ι3_smul_thd, ι3_smul_thd, pc_ι_024, pc_ι_025]

end CFSG.RankThree.GF2n.Smith81.U6Cube

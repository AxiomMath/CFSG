module

public import CFSG.Blueprint.NativeSporadic
import CFSG.Quasithin.Background.SmithB45MatM22Cls
import CFSG.Quasithin.Vol2.Ch10SecKGA7a
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem orderOf_ne_fifteen_a7 (x : alternatingGroup (Fin 7)) : orderOf x ≠ 15 := by
  rw [← Subgroup.orderOf_coe]
  exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.perm_seven_orderOf_ne_fifteen x

theorem orderOf_ne_fifteen_m22
    (x : Blueprint.NativeSporadic.M22) : orderOf x ≠ 15 := by
  intro h
  have hmem := CFSG.Quasithin.B45Mat.M22.orderOf_mem_of_isPRegular x (by
    change Nat.Coprime (orderOf x) 2
    rw [h]
    norm_num)
  rw [h] at hmem
  simp at hmem

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

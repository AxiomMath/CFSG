module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4RankData

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)
open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem transvRank_dec_Ua : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 pa pb pc pd t ≠ 1 →
    (tup4 pa pb pc pd t * cc = cc * tup4 pa pb pc pd t ∨
      (∃ s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        tup4 pa pb pc pd s * cc⁻¹ * (tup4 pa pb pc pd s)⁻¹ * cc⁻¹⁻¹ = tup4 pa pb pc pd t) ∨
      (∃ g ∈ rankG, Equiv.Perm.sign g = 1 ∧ g * rep4 * g⁻¹ = tup4 pa pb pc pd t)) := by
  decide +kernel

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem transvRank_dec_Ub : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tup4 qa qb qc qd t ≠ 1 →
    (tup4 qa qb qc qd t * cc = cc * tup4 qa qb qc qd t ∨
      (∃ s : Fin 2 × Fin 2 × Fin 2 × Fin 2,
        tup4 qa qb qc qd s * cc⁻¹ * (tup4 qa qb qc qd s)⁻¹ * cc⁻¹⁻¹ = tup4 qa qb qc qd t) ∨
      (∃ g ∈ rankG, Equiv.Perm.sign g = 1 ∧ g * rep4 * g⁻¹ = tup4 qa qb qc qd t)) := by
  decide +kernel


end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end

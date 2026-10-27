module

public import CFSG.RankThree.Co2.CrBridge

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Co2Inv


namespace CM

theorem rep_mul_self (h : ClassFacts) {i : ℕ} (hi : i < 10) : rep i * rep i = 1 :=
  crMat_injective (by rw [map_mul, crMat_rep hi, map_one]; exact h.sq i hi)

theorem rep_ne_one (h : ClassFacts) {i : ℕ} (hi : i < 10) : rep i ≠ 1 := fun e =>
  h.ne_one i hi (by rw [← crMat_rep hi, e, map_one])

theorem card_centralizer_eq {i : ℕ} (hi : i < 10) :
    Nat.card (Subgroup.centralizer ({rep i} : Set Cr)) =
      Nat.card {g : Matrix (Fin 22) (Fin 22) (ZMod 2) // g ∈ Cm ∧ g * repMat i = repMat i * g} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨crMat (x : Cr), crMat_mem_Cm _, ?_⟩) ⟨?_, ?_⟩)
  · rw [← crMat_rep hi, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 x.2]
  · intro x y e
    exact Subtype.ext (crMat_injective (congrArg Subtype.val e))
  · rintro ⟨g, hg, e⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_mrange.1 (Cm_le_mrange hg)
    refine ⟨⟨x, Subgroup.mem_centralizer_singleton_iff.2 (crMat_injective ?_)⟩, rfl⟩
    rw [map_mul, map_mul, crMat_rep hi]
    exact e

theorem card_centralizer_rep (h : ClassFacts) {i : ℕ} (hi : i < 10) :
    Nat.card (Subgroup.centralizer ({rep i} : Set Cr)) * classSizes[i]! = 743178240 := by
  rw [card_centralizer_eq hi]
  exact h.cent i hi

end CM

theorem rep_mul_self {i : ℕ} (hi : i < 10) : rep i * rep i = 1 :=
  CM.rep_mul_self classFacts_cert hi

theorem rep_ne_one {i : ℕ} (hi : i < 10) : rep i ≠ 1 :=
  CM.rep_ne_one classFacts_cert hi

theorem card_centralizer_rep {i : ℕ}
    (hi : i < 10) :
    Nat.card (Subgroup.centralizer ({rep i} : Set Cr)) * classSizes[i]! = 743178240 :=
  CM.card_centralizer_rep classFacts_cert hi

end CFSG.RankThree.Co2

end

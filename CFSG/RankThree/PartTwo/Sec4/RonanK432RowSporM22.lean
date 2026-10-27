module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeM22
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
  (wordM22 m22x m22y m22_pair_facts m22_pair_inj)

@[expose] def m22f (p : Fin 3 × Fin 3) : NativeSporadic.M22 :=
  m22x ^ (p.1 : ℕ) * m22y ^ (p.2 : ℕ)

@[expose] def m22w (p : Fin 3 × Fin 3) : NativeSporadic.M22 :=
  if (p.1 = 1 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 1) ∨ (p.1 = 2 ∧ p.2 = 2)
  then wordM22 [2, 1, -2, 1, 2, 1, -2, 1, 2, 2] else wordM22 [-2, 1, 2, 1, 2]

theorem m22f_mul_x : ∀ p : Fin 3 × Fin 3, m22f p * m22x = m22f (p.1 + 1, p.2) := by
  decide +kernel

theorem m22f_mul_y : ∀ p : Fin 3 × Fin 3, m22f p * m22y = m22f (p.1, p.2 + 1) := by
  decide +kernel

theorem m22f_pow_three : ∀ p : Fin 3 × Fin 3, m22f p ^ 3 = 1 := by
  decide +kernel

theorem m22w_spec : ∀ p : Fin 3 × Fin 3, m22f p ≠ 1 →
    (m22w p * m22f p * (m22w p)⁻¹) * m22f p = m22f p * (m22w p * m22f p * (m22w p)⁻¹) ∧
      m22w p * m22f p * (m22w p)⁻¹ ≠ m22f p ∧ m22w p * m22f p * (m22w p)⁻¹ ≠ (m22f p)⁻¹ ∧
      m22w p * m22f p * (m22w p)⁻¹ ≠ 1 := by
  decide +kernel

theorem m22f_mem (p : Fin 3 × Fin 3) :
    m22f p ∈ Subgroup.closure ({m22x, m22y} : Set NativeSporadic.M22) :=
  Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem listRow_m22 : ListRow NativeSporadic.M22 := by
  haveI : Finite NativeSporadic.M22 := Nat.finite_of_card_ne_zero (by rw [m22_card]; norm_num)
  obtain ⟨-, h2, h3, -, -⟩ := m22_pair_facts
  exact listRow_of_gen (x := m22x) (y := m22y) m22f (fun p => (p.1 + 1, p.2))
    (fun p => (p.1, p.2 + 1)) m22_pair_inj m22f_mem ⟨(0, 0), by simp [m22f]⟩
    m22f_mul_x m22f_mul_y h2 h3 m22f_pow_three 2 (by simp)
    (by rw [m22_card]; norm_num) m22w m22w_spec

theorem outerRow_m22 :
    OuterRow NativeSporadic.M22 := by
  apply outerRow_of_not_three_dvd_outer
  exact CFSG.Quasithin.A318P.not_dvd_outer_M22 (S := NativeSporadic.M22) (MulEquiv.refl _)
    Nat.prime_three (by norm_num)

theorem row_carrier_m22 :
    RowOf (NativeSporadic.Carrier .M22) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.M22) e.symm ⟨listRow_m22, outerRow_m22⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

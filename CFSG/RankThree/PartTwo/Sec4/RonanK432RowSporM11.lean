module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeM11
public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
  (wordM11 m11x m11y m11_pair_facts m11_pair_inj)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def m11f (p : Fin 3 × Fin 3) : NativeSporadic.M11 :=
  m11x ^ (p.1 : ℕ) * m11y ^ (p.2 : ℕ)

@[expose] def m11w (p : Fin 3 × Fin 3) : NativeSporadic.M11 :=
  if (p.1 = 1 ∧ p.2 = 0) ∨ (p.1 = 1 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 0) ∨ (p.1 = 2 ∧ p.2 = 1)
  then wordM11 [-2, 1, 2] else wordM11 [2, 1, 2, 1, -2]

theorem m11_gen_facts :
    (∀ p : Fin 3 × Fin 3, m11f p * m11x = m11f (p.1 + 1, p.2)) ∧
    (∀ p : Fin 3 × Fin 3, m11f p * m11y = m11f (p.1, p.2 + 1)) ∧
    (∀ p : Fin 3 × Fin 3, m11f p ^ 3 = 1) ∧
    (∀ p : Fin 3 × Fin 3, m11f p ≠ 1 →
      (m11w p * m11f p * (m11w p)⁻¹) * m11f p = m11f p * (m11w p * m11f p * (m11w p)⁻¹) ∧
      m11w p * m11f p * (m11w p)⁻¹ ≠ m11f p ∧ m11w p * m11f p * (m11w p)⁻¹ ≠ (m11f p)⁻¹ ∧
      m11w p * m11f p * (m11w p)⁻¹ ≠ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem listRow_m11 : ListRow NativeSporadic.M11 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := m11_pair_facts
  obtain ⟨hσx, hσy, hP3, hw⟩ := m11_gen_facts
  have hmem : ∀ p : Fin 3 × Fin 3, m11f p ∈ Subgroup.closure ({m11x, m11y} : Set NativeSporadic.M11) :=
    fun p => Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  exact listRow_of_gen (x := m11x) (y := m11y) m11f (fun p => (p.1 + 1, p.2))
    (fun p => (p.1, p.2 + 1)) m11_pair_inj hmem ⟨(0, 0), by simp [m11f]⟩ hσx hσy h2 h3 hP3 2
    (by simp) (by rw [m11_card]; norm_num) m11w hw

theorem outerRow_m11 :
    OuterRow NativeSporadic.M11 := by
  apply outerRow_of_not_three_dvd_outer
  have h2 : Nat.card (Outer NativeSporadic.M11) ≤ 2 := CFSG.Sporadic.Schreier.at_m11_schreier.1
  haveI : Finite (NativeSporadic.Carrier .M11) := inferInstanceAs (Finite NativeSporadic.M11)
  exact CFSG.Quasithin.A318P.not_dvd_outer_of_carrier (S := NativeSporadic.M11) (s := .M11)
    (MulEquiv.refl _) h2 Nat.prime_three (by norm_num)

theorem row_carrier_m11 :
    RowOf (NativeSporadic.Carrier .M11) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.M11) e.symm ⟨listRow_m11, outerRow_m11⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeM12
public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.Schreier
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (wordM12 m12σx m12σy)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def m12Sx : NativeSporadic.M12 := wordM12 [2, 1, -2, 1, 2, 1, 2, 1, -2]

@[expose] def m12Sy : NativeSporadic.M12 := wordM12 [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1]

@[expose] def m12Sz : NativeSporadic.M12 := m12Sx * m12Sy * m12Sx⁻¹ * m12Sy⁻¹

@[expose] def m12Sf (p : Fin 3 × Fin 3 × Fin 3) : NativeSporadic.M12 :=
  m12Sx ^ (p.1 : ℕ) * m12Sy ^ (p.2.1 : ℕ) * m12Sz ^ (p.2.2 : ℕ)

@[expose] def m12Sws : List (List ℤ) :=
  [[], [-2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2], [-2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2],
    [2, 1, -2, 1, 2, 1, 2, 1, -2], [2, 1, -2, 1, 2, 1, 2, 1, -2], [2, 1, 2, 1, 2, 1, -2, 1, -2],
    [2, 1, -2, 1, 2, 1, 2, 1, -2], [2, 1, 2, 1, 2, 1, -2, 1, -2], [2, 1, -2, 1, 2, 1, 2, 1, -2],
    [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1], [1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1],
    [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1], [1], [2, 1, -2, 1, 2, 1, 2, 1, -2], [1],
    [2, 1, -2, 1, 2, 1, 2, 1, -2], [-2, 1, 2], [2, 1, -2, 1, 2, 1, 2, 1, -2],
    [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1], [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1],
    [1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1], [-2, 1, 2], [2, 1, -2, 1, 2, 1, 2, 1, -2],
    [2, 1, -2, 1, 2, 1, 2, 1, -2], [1], [2, 1, -2, 1, 2, 1, 2, 1, -2], [1]]

@[expose] def m12Sw (p : Fin 3 × Fin 3 × Fin 3) : NativeSporadic.M12 :=
  wordM12 (m12Sws.getD (9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)) [])

theorem m12S_gen : m12Sx ^ 3 = 1 ∧ m12Sy ^ 3 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem m12Sf_inj : Function.Injective m12Sf := by
  intro p q h
  revert p q
  decide +kernel

theorem m12Sf_σx : ∀ p, m12Sf p * m12Sx = m12Sf (m12σx p) := by
  decide +kernel

theorem m12Sf_σy : ∀ p, m12Sf p * m12Sy = m12Sf (m12σy p) := by
  decide +kernel

theorem m12Sf_one : ∃ p, m12Sf p = 1 := ⟨(0, 0, 0), by simp [m12Sf]⟩

theorem m12Sf_mem : ∀ p, m12Sf p ∈ Subgroup.closure ({m12Sx, m12Sy} : Set NativeSporadic.M12) := by
  intro p
  have hx : m12Sx ∈ Subgroup.closure ({m12Sx, m12Sy} : Set NativeSporadic.M12) :=
    Subgroup.subset_closure (by simp)
  have hy : m12Sy ∈ Subgroup.closure ({m12Sx, m12Sy} : Set NativeSporadic.M12) :=
    Subgroup.subset_closure (by simp)
  have hz : m12Sz ∈ Subgroup.closure ({m12Sx, m12Sy} : Set NativeSporadic.M12) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hx _)
    (Subgroup.pow_mem _ hy _)) (Subgroup.pow_mem _ hz _)

theorem m12Sf_exp3 : ∀ p, m12Sf p ^ 3 = 1 := by
  decide +kernel

theorem m12Sf_wit : ∀ p, m12Sf p ≠ 1 →
    (m12Sw p * m12Sf p * (m12Sw p)⁻¹) * m12Sf p = m12Sf p * (m12Sw p * m12Sf p * (m12Sw p)⁻¹) ∧
      m12Sw p * m12Sf p * (m12Sw p)⁻¹ ≠ m12Sf p ∧ m12Sw p * m12Sf p * (m12Sw p)⁻¹ ≠ (m12Sf p)⁻¹ ∧
      m12Sw p * m12Sf p * (m12Sw p)⁻¹ ≠ 1 := by
  decide +kernel

theorem listRow_m12 : ListRow NativeSporadic.M12 :=
  listRow_of_gen (x := m12Sx) (y := m12Sy) m12Sf m12σx m12σy m12Sf_inj m12Sf_mem m12Sf_one
    m12Sf_σx m12Sf_σy m12S_gen.1 m12S_gen.2 m12Sf_exp3 3 (by simp)
    (by rw [CFSG.Sporadic.Schreier.m12_card]; norm_num) m12Sw m12Sf_wit

theorem outerRow_m12 :
    OuterRow NativeSporadic.M12 := by
  apply outerRow_of_not_three_dvd_outer
  have h2 : Nat.card (Outer NativeSporadic.M12) ≤ 2 :=
    (CFSG.ComponentClassification.M12Cover.card_outer).le
  haveI : Finite (NativeSporadic.Carrier .M12) := inferInstanceAs (Finite NativeSporadic.M12)
  exact CFSG.Quasithin.A318P.not_dvd_outer_of_carrier (S := NativeSporadic.M12) (s := .M12)
    (MulEquiv.refl _) h2 Nat.prime_three (by norm_num)

theorem row_carrier_m12 :
    RowOf (NativeSporadic.Carrier .M12) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.M12) e.symm ⟨listRow_m12, outerRow_m12⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

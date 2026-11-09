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

section M12Codes

open CFSG.Permutation.FinPack
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (m12WordK m12WordK_enc)

@[expose] noncomputable def m12SfK (p : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  mulK 12 (mulK 12
      (powK 12 (enc (1 : Equiv.Perm (Fin 12))) (m12WordK [2, 1, -2, 1, 2, 1, 2, 1, -2])
        (p.1 : ℕ))
      (powK 12 (enc (1 : Equiv.Perm (Fin 12)))
        (m12WordK [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1]) (p.2.1 : ℕ)))
    (powK 12 (enc (1 : Equiv.Perm (Fin 12)))
      (mulK 12 (mulK 12 (mulK 12
        (m12WordK [2, 1, -2, 1, 2, 1, 2, 1, -2])
        (m12WordK [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1]))
        (invCK 12 (m12WordK [2, 1, -2, 1, 2, 1, 2, 1, -2])))
        (invCK 12 (m12WordK [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1]))) (p.2.2 : ℕ))

theorem m12SfK_enc (p : Fin 3 × Fin 3 × Fin 3) :
    enc ((m12Sf p : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12SfK p := by
  have hn : 12 ≤ 16 := by norm_num
  simp only [m12Sf, m12Sz, Subgroup.coe_mul, SubmonoidClass.coe_pow, InvMemClass.coe_inv,
    enc_mul hn, ← powK_enc hn, enc_inv_invCK hn, m12Sx, m12Sy, m12WordK_enc, m12SfK]

@[expose] noncomputable def m12SwK (p : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  m12WordK (m12Sws.getD (9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)) [])

theorem m12Sf_wit_codes : ∀ p : Fin 3 × Fin 3 × Fin 3,
    Nat.beq (m12SfK p) (enc (1 : Equiv.Perm (Fin 12))) = true ∨
    (Nat.beq (mulK 12 (mulK 12 (mulK 12 (m12SwK p) (m12SfK p)) (invCK 12 (m12SwK p))) (m12SfK p))
        (mulK 12 (m12SfK p) (mulK 12 (mulK 12 (m12SwK p) (m12SfK p)) (invCK 12 (m12SwK p)))) =
        true ∧
      Nat.beq (mulK 12 (mulK 12 (m12SwK p) (m12SfK p)) (invCK 12 (m12SwK p))) (m12SfK p) = false ∧
      Nat.beq (mulK 12 (mulK 12 (m12SwK p) (m12SfK p)) (invCK 12 (m12SwK p)))
        (invCK 12 (m12SfK p)) = false ∧
      Nat.beq (mulK 12 (mulK 12 (m12SwK p) (m12SfK p)) (invCK 12 (m12SwK p)))
        (enc (1 : Equiv.Perm (Fin 12))) = false) := by
  decide +kernel

theorem m12Sf_wit : ∀ p, m12Sf p ≠ 1 →
    (m12Sw p * m12Sf p * (m12Sw p)⁻¹) * m12Sf p = m12Sf p * (m12Sw p * m12Sf p * (m12Sw p)⁻¹) ∧
      m12Sw p * m12Sf p * (m12Sw p)⁻¹ ≠ m12Sf p ∧ m12Sw p * m12Sf p * (m12Sw p)⁻¹ ≠ (m12Sf p)⁻¹ ∧
      m12Sw p * m12Sf p * (m12Sw p)⁻¹ ≠ 1 := by
  have hn : 12 ≤ 16 := by norm_num
  have key : ∀ g h : NativeSporadic.M12, g = h ↔
      Nat.beq (enc (g : Equiv.Perm (Fin 12))) (enc (h : Equiv.Perm (Fin 12))) = true :=
    fun g h => Subtype.ext_iff.trans (beq_enc_iff hn).symm
  have hW : ∀ p, enc ((m12Sw p : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12SwK p :=
    fun p => m12WordK_enc _
  intro p hp
  rw [ne_eq, key] at hp
  simp only [ne_eq, key, Subgroup.coe_mul, InvMemClass.coe_inv, OneMemClass.coe_one, enc_mul hn,
    enc_inv_invCK hn, m12SfK_enc, hW, Bool.not_eq_true] at hp ⊢
  rcases m12Sf_wit_codes p with h | ⟨h2, h3, h4, h5⟩
  · simp [h] at hp
  · exact ⟨h2, h3, h4, h5⟩

end M12Codes

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

module

public import CFSG.Quasithin.Background.F918Z8Op0
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Quasithin.Background.F918Z4bAut

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem opx_card_mulAut_psl2 {K : Type} [Field K] [Finite K] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hK : Nat.card K = q) :
    Nat.card (MulAut (PSL2 K)) = 2 * Nat.card (PSL2 K) := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨q, 1, hq, hq.odd_of_ne_two hq2, le_rfl, by rw [hK, pow_one]⟩
  have hsub : Subsingleton (RingAut K) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hq K
      (n := 1) (by rw [hK, pow_one])).1
    exact (Nat.card_eq_one_iff_unique.mp h).1
  have hbij : Function.Bijective (pglAction K) :=
    ⟨pglAction_injective_of_finite K, fun α =>
      mem_range_pglAction_of_autFieldPart_eq_one (Subsingleton.elim _ _)⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), pgl2_card_formula,
    psl2_card_formula K hodd, hK]
  have hqodd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  have h1 : q ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hqodd]
  have h2 : 2 ∣ q * (q ^ 2 - 1) := Dvd.dvd.mul_left (by omega) q
  exact (Nat.mul_div_cancel' h2).symm

theorem opx_card_aut_le {X : Type} [Group X] [Finite X] {p : ℕ} (h : ExcPair X p) :
    Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  obtain ⟨q, hq, hq3, -, -, -, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  let e' := e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
  exact (opx_card_mulAut_psl2 hq (by omega) hK).le

end CFSG.Quasithin

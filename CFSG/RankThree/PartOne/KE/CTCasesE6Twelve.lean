module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.Lattice.SteinbergBIE6CoxTwelve
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem e6Cx_annihilators {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {x : ℤ}
    (hg : ¬ (p : ℤ) ∣ x ^ 2 + x + 1) (α : Fin Tag.E6.rank → ℤ) (hα : IsRoot .E6 α) :
    ∃ A : ℤ[X], (∀ β, (aeval e6CxW A) *ᵥ β ∈ orbitLattice e6CxW α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  obtain ⟨-, -, -, -, hcase, -⟩ := e6Cx_case
  rcases hcase α hα with ⟨-, hidx⟩ | ⟨-, hs, h, -, h5⟩
  · refine exists_annihilator_of_index e6CxW _ x ?_
    rw [hidx]
    exact CTE6.not_dvd_natCast_of_lt one_pos (by omega)
  · refine exists_annihilator_of_quotient e6CxW _ h (X ^ 2 + X + 1) (by rw [h5]; simp) x ?_
    rw [hs]
    simpa using CTE6.not_dvd_natCast_mul hp (c := 1) one_pos (by omega) hg

theorem E6_twelve_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 12 ∧
      CyclicSylowConclusion .E6 K p
        ((Nat.card K ^ 4 - Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 + Nat.card K + 1)) 3 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 2 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Twelve_data hp hp3 hpf'
  obtain ⟨hg, h1, hR⟩ := CTE6.e6Twelve_factors hp hord
  refine ⟨hp7, hord, ?_⟩
  obtain ⟨-, hchar, ⟨v, -, hv1, hv2⟩, -⟩ := e6Cx_case
  have h24 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h12 : 1 ≤ Nat.card K ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hn₀ : (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 + Nat.card K + 1) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (by omega)
  have hev : e6CxW.charpoly.eval (Nat.card K : ℤ) =
      (((Nat.card K ^ 4 - Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 + Nat.card K + 1) : ℕ) : ℤ) := by
    rw [hchar]
    push_cast [Nat.cast_sub h24]
    simp
  have hfac : ((Nat.card K ^ 12 - 1 : ℕ) : ℤ) =
      (((Nat.card K ^ 4 - Nat.card K ^ 2 + 1) * (Nat.card K ^ 2 + Nat.card K + 1) : ℕ) : ℤ) *
        (((Nat.card K : ℤ) - 1) * ((Nat.card K : ℤ) ^ 3 + 1) * ((Nat.card K : ℤ) ^ 2 + 1)) := by
    push_cast [Nat.cast_sub h12, Nat.cast_sub h24]
    ring
  have hW : IsWeylMatrix .E6 e6CxW := IsWeylMatrix.of_word .E6 [0, 1, 2, 3, 4, 5]
  refine cyclic_sylow_of_inputs hmain (Or.inl ⟨rfl, rfl⟩)
    hW hv1 hv2 ?_ K hp hp7 hpq hn₀ hev
    (fun α hα => e6Cx_annihilators hp hp7 hg α hα)
    (ordProj_card_adjointGroup_E6 hp hp3 hpq hord (d₀ := 12) (by decide) (by decide) hn₀ hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E6_twelve_n0_odd (q : ℕ) : Odd ((q ^ 4 - q ^ 2 + 1) * (q ^ 2 + q + 1)) := by
  have hle : q ^ 2 ≤ q ^ 4 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · exact Nat.pow_le_pow_right hq (by norm_num)
  have h1 : Odd (q ^ 4 - q ^ 2 + 1) := by
    refine Even.add_one ?_
    rw [Nat.even_sub hle, Nat.even_pow, Nat.even_pow]
    simp
  have h2 : Odd (q ^ 2 + q + 1) := by
    have : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
    rw [this]
    exact (Nat.even_mul_succ_self q).add_one
  exact h1.mul h2

end CFSG.RankThree.PartOne.KE

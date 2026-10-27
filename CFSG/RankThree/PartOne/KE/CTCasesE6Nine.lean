module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.Lattice.SteinbergBIE6NineQuot
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem e6N9_annihilators {p : ℕ} (hp7 : 7 < p) (x : ℤ) (α : Fin Tag.E6.rank → ℤ)
    (hα : IsRoot .E6 α) :
    ∃ A : ℤ[X], (∀ β, (aeval e6N9W A) *ᵥ β ∈ orbitLattice e6N9W α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  obtain ⟨-, -, -, -, hfull, -⟩ := e6N9_case
  obtain ⟨-, hidx⟩ := hfull α hα
  refine exists_annihilator_of_index e6N9W _ x ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hidx
  rcases hidx with h | h <;> rw [h] <;> exact CTE6.not_dvd_natCast_of_lt (by norm_num) (by omega)

theorem E6_nine_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 9 ∧
      CyclicSylowConclusion .E6 K p (Nat.card K ^ 6 + Nat.card K ^ 3 + 1) 3 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 6 + (Nat.card K : ℤ) ^ 3 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Nine_data hp hp3 hpf'
  have hR := CTE6.e6Nine_factors hord
  refine ⟨hp7, hord, ?_⟩
  obtain ⟨-, hchar, ⟨v, -, hv1, hv2⟩, -⟩ := e6N9_case
  have h3 : 1 ≤ Nat.card K ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h9 : 1 ≤ Nat.card K ^ 9 := Nat.one_le_pow _ _ (by omega)
  have hn₀ : Nat.card K ^ 6 + Nat.card K ^ 3 + 1 ≠ 0 := by omega
  have hev : e6N9W.charpoly.eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 6 + Nat.card K ^ 3 + 1 : ℕ) : ℤ) := by
    rw [hchar]
    push_cast
    simp
  have hfac : ((Nat.card K ^ 9 - 1 : ℕ) : ℤ) =
      ((Nat.card K ^ 6 + Nat.card K ^ 3 + 1 : ℕ) : ℤ) * ((Nat.card K : ℤ) ^ 3 - 1) := by
    push_cast [Nat.cast_sub h9]
    ring
  have hW : IsWeylMatrix .E6 e6N9W := IsWeylMatrix.of_word .E6 [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]
  refine cyclic_sylow_of_inputs hmain (Or.inl ⟨rfl, rfl⟩)
    hW hv1 hv2 ?_ K hp hp7 hpq hn₀ hev
    (fun α hα => e6N9_annihilators hp7 _ α hα)
    (ordProj_card_adjointGroup_E6 hp hp3 hpq hord (d₀ := 9) (by decide) (by decide) hn₀ hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E6_nine_n0_odd (q : ℕ) : Odd (q ^ 6 + q ^ 3 + 1) := by
  have : q ^ 6 + q ^ 3 + 1 = q ^ 3 * (q ^ 3 + 1) + 1 := by ring
  rw [this]
  exact (Nat.even_mul_succ_self (q ^ 3)).add_one

end CFSG.RankThree.PartOne.KE

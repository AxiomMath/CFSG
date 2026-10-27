module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.Lattice.SteinbergBIE7CoxNine
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem e7Cx2_annihilators {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {x : ℤ}
    (hg : ¬ (p : ℤ) ∣ x - 1) (α : Fin Tag.E7.rank → ℤ) (hα : IsRoot .E7 α) :
    ∃ A : ℤ[X], (∀ β, (aeval (e7CxW ^ 2) A) *ᵥ β ∈ orbitLattice (e7CxW ^ 2) α) ∧
      ¬ (p : ℤ) ∣ A.eval x := by
  obtain ⟨-, -, -, -, hcase, -⟩ := e7Cx2_case
  rcases hcase α hα with ⟨-, hidx⟩ | ⟨-, hs, h, -, h5⟩
  · refine exists_annihilator_of_index (e7CxW ^ 2) _ x ?_
    rw [hidx]
    exact CTE6.not_dvd_natCast_of_lt one_pos (by omega)
  · refine exists_annihilator_of_quotient (e7CxW ^ 2) _ h (X - 1) (by rw [h5]; simp) x ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs <;> rw [hs]
    · simpa using CTE6.not_dvd_natCast_mul hp (c := 1) one_pos (by omega) hg
    · simpa using CTE6.not_dvd_natCast_mul hp (c := 3) (by norm_num) (by omega) hg

theorem E7_nine_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 9).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 9 ∧
      CyclicSylowConclusion .E7 K p
        ((Nat.card K ^ 6 + Nat.card K ^ 3 + 1) * (Nat.card K - 1)) 2 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 6 + (Nat.card K : ℤ) ^ 3 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Nine_data hp hp3 hpf'
  obtain ⟨hg, hR⟩ := CTE6.e7Nine_factors hp hp3 hord
  refine ⟨hp7, hord, ?_⟩
  obtain ⟨-, hchar, ⟨v, -, hv1, hv2⟩, -⟩ := e7Cx2_case
  have h18 : 1 ≤ Nat.card K ^ 18 := Nat.one_le_pow _ _ (by omega)
  have hn₀ : (Nat.card K ^ 6 + Nat.card K ^ 3 + 1) * (Nat.card K - 1) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (by omega)
  have hev : (e7CxW ^ 2).charpoly.eval (Nat.card K : ℤ) =
      (((Nat.card K ^ 6 + Nat.card K ^ 3 + 1) * (Nat.card K - 1) : ℕ) : ℤ) := by
    rw [hchar]
    push_cast [Nat.cast_sub (show 1 ≤ Nat.card K by omega)]
    simp
  have hfac : ((Nat.card K ^ 18 - 1 : ℕ) : ℤ) =
      (((Nat.card K ^ 6 + Nat.card K ^ 3 + 1) * (Nat.card K - 1) : ℕ) : ℤ) *
        (((Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) * ((Nat.card K : ℤ) ^ 9 + 1)) := by
    push_cast [Nat.cast_sub h18, Nat.cast_sub (show 1 ≤ Nat.card K by omega)]
    ring
  have hW : IsWeylMatrix .E7 (e7CxW ^ 2) :=
    (IsWeylMatrix.of_word .E7 [0, 1, 2, 3, 4, 5, 6]).pow 2
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inl ⟨rfl, rfl⟩))
    hW hv1 hv2 ?_ K hp hp7 hpq hn₀ hev
    (fun α hα => e7Cx2_annihilators hp hp7 hg α hα)
    (ordProj_card_adjointGroup_E7 hp hp3 hpq hord (d₀ := 18) (by decide) (by decide) hn₀ hfac hR)
  right
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

end CFSG.RankThree.PartOne.KE

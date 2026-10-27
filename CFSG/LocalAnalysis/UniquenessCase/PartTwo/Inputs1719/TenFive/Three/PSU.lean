module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.SuGood
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.PSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open
open CFSG.Blueprint (LieModel)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_eichler_inv_hypPSU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) {α : MulAut (hypPSU h r ε)} (hα : orderOf α = 2) :
    ∃ (v w : HypIndex r ε → K) (γ : K) (hd : IsEichlerDatum h v w γ),
      α (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq)) =
        (hypProj h r ε (eichlerSU h hd.isotropic hd.orthogonal hd.trace_eq))⁻¹ := by
  obtain ⟨A, σ, hx, hA, rfl, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp2 hr hε hn).2.2.2 α hα
  obtain ⟨v, w, γ, hd, hAE⟩ : ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map σ =
        hypEichler h v (-w) (h.bar γ) * A := by
    rcases hσ with rfl | hσ
    · obtain ⟨l, hl0, hAA, hN, hAs⟩ := inner_involution_lift h hp2 hr hA (hrefl rfl)
      obtain ⟨v, w, γ, hd, hE⟩ : ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * hypEichler h v w γ =
            hypEichler h v (-w) (h.bar γ) * A := by
        rcases hN with hN | hN
        · exact exists_eichler_inv_split h hp2 hn hA hl0 hAA hN hAs
        · exact exists_eichler_inv_paired h hp2 hA hAA hN hAs
      exact ⟨v, w, γ, hd, hE⟩
    · obtain ⟨c, -, hc⟩ := hbar hσ
      have hmap (M : Matrix (HypIndex r ε) (HypIndex r ε) K) : M.map σ = M.map h.bar :=
        Matrix.ext fun _ _ => hσ _
      obtain ⟨v, w, γ, hd, hE⟩ : ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
          (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map h.bar =
            hypEichler h v (-w) (h.bar γ) * A := by
        rcases bar_scalar_eq_one_or_neg_one h hr hA hc with rfl | rfl
        · exact exists_eichler_inv_barOne h hp2 hn hA (by rw [hc, one_smul])
        · exact exists_eichler_inv_barNeg h hp2 hn hA (by rw [hc, neg_one_smul])
      exact ⟨v, w, γ, hd, by rw [hmap]; exact hE⟩
  exact ⟨v, w, γ, hd, semilinearAutHom_eichler_inv h hr hε hx hd.isotropic hd.orthogonal
    hd.trace_eq hAE⟩

theorem involGood_hypPSU_three (h : UnitaryFieldData 3 1 K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 4 ≤ 2 * r + ε) : InvolGood (hypPSU h r ε) := by
  intro α hα
  obtain ⟨v, w, γ, hd, hinv⟩ := exists_eichler_inv_hypPSU h (by norm_num) hr hε (by omega) hα
  obtain ⟨hord, hgood⟩ := isExtraGood_eichlerSU_three h hn hd
  exact Or.inl ⟨_, hord, hinv, hgood⟩

theorem involAt_PSU : InvolAt .PSU := by
  intro S _ _ n hU _ hS
  obtain ⟨⟨hp, he1, hn3, -⟩, K, hKf, -, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  have h : UnitaryFieldData 3 1 K := ⟨hp, he1, by rw [hKcard, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hn4 : 4 ≤ 2 * r + ε := by
    have h3 : 2 * r + ε ≠ 3 := fun h3 => hU ⟨rfl, h3⟩
    omega
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  exact InvolGood.of_mulEquiv ((hypPSUEquivStatedProj h hR (by omega)).trans φ.symm)
    (involGood_hypPSU_three h (by omega) hε hn4)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

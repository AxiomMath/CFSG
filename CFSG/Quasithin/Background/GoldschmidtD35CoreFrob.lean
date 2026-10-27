module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreOdd
public import CFSG.Quasithin.Background.GoldschmidtD35CoreSwap
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {L : Subgroup (V ≃ₗ[F] V)} {pt : Fin 6 → ℙ F V}

theorem IsSixOrbit.exists_swap [Finite F] [FiniteDimensional F V] (hF : Nat.card F = 4)
    (hV : Module.finrank F V = 3) (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ n : gammaL F V, ∀ i, pointAct n (pt i) = pt (swap 4 5 i) := by
  have := charP_two_of_card_four hF
  set σ : F ≃+* F := frobeniusEquiv F 2 with hσdef
  have hσ : ∀ x, σ x = x ^ 2 := fun x => by rw [hσdef, frobeniusEquiv_apply, frobenius_def]
  have h3 : ∀ {i j k : Fin 6}, i ≠ j → i ≠ k → j ≠ k →
      LinearIndependent F ![(pt i).rep, (pt j).rep, (pt k).rep] :=
    fun hij hik hjk => hO.linearIndependent_three hV hirr hij hik hjk
  have hli : LinearIndependent F ![(pt 0).rep, (pt 1).rep, (pt 2).rep] :=
    h3 (by decide) (by decide) (by decide)
  let bas₀ := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hV])
  have hbas₀ : ⇑bas₀ = ![(pt 0).rep, (pt 1).rep, (pt 2).rep] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have e0 : bas₀ 0 = (pt 0).rep := by rw [hbas₀]; rfl
  have e1 : bas₀ 1 = (pt 1).rep := by rw [hbas₀]; rfl
  have e2 : bas₀ 2 = (pt 2).rep := by rw [hbas₀]; rfl
  obtain ⟨x0, x1, x2, hx0, hx1, hx2, hrr⟩ : ∃ x0 x1 x2 : F, x0 ≠ 0 ∧ x1 ≠ 0 ∧ x2 ≠ 0 ∧
      (pt 3).rep = x0 • (pt 0).rep + x1 • (pt 1).rep + x2 • (pt 2).rep := by
    obtain ⟨h0, h1, h2⟩ := coord_ne_zero bas₀ (w := (pt 3).rep)
      (by rw [e0, e1]; exact h3 (by decide) (by decide) (by decide))
      (by rw [e0, e2]; exact h3 (by decide) (by decide) (by decide))
      (by rw [e1, e2]; exact h3 (by decide) (by decide) (by decide))
    refine ⟨_, _, _, h0, h1, h2, ?_⟩
    have := repr_expansion bas₀ (pt 3).rep
    rwa [e0, e1, e2] at this
  have hlis : LinearIndependent F ![x0 • (pt 0).rep, x1 • (pt 1).rep, x2 • (pt 2).rep] :=
    hO.indep_smul hV hirr (by decide) (by decide) (by decide) hx0 hx1 hx2
  let b := basisOfLinearIndependentOfCardEqFinrank hlis (by simp [hV])
  have hb : ⇑b = ![x0 • (pt 0).rep, x1 • (pt 1).rep, x2 • (pt 2).rep] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hb0 : b 0 = x0 • (pt 0).rep := by rw [hb]; rfl
  have hb1 : b 1 = x1 • (pt 1).rep := by rw [hb]; rfl
  have hb2 : b 2 = x2 • (pt 2).rep := by rw [hb]; rfl
  have hsum : b 0 + b 1 + b 2 = (pt 3).rep := by rw [hb0, hb1, hb2, hrr]
  have hgen : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → Generic b (pt k).rep := by
    intro k hk0 hk1 hk2 hk3
    have hi := fun {i j : Fin 6} (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j) {c₁ c₂ : F}
      (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) =>
      hO.indep_smul hV hirr hij hik hjk h₁ h₂ (one_ne_zero (α := F))
    apply generic_of_indep b
    · rw [hb0, hb1]
      simpa using hi (Ne.symm hk0) (Ne.symm hk1) (by decide) hx0 hx1
    · rw [hb0, hb2]
      simpa using hi (Ne.symm hk0) (Ne.symm hk2) (by decide) hx0 hx2
    · rw [hb1, hb2]
      simpa using hi (Ne.symm hk1) (Ne.symm hk2) (by decide) hx1 hx2
    · rw [hsum, hb0]
      simpa using hi (Ne.symm hk0) (Ne.symm hk3) (by decide) hx0 (one_ne_zero (α := F))
    · rw [hsum, hb1]
      simpa using hi (Ne.symm hk1) (Ne.symm hk3) (by decide) hx1 (one_ne_zero (α := F))
    · rw [hsum, hb2]
      simpa using hi (Ne.symm hk2) (Ne.symm hk3) (by decide) hx2 (one_ne_zero (α := F))
  have hg4 := hgen 4 (by decide) (by decide) (by decide) (by decide)
  have hg5 := hgen 5 (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨semiPerm b σ, semiPerm_mem b σ⟩, ?_⟩
  have hfix : ∀ (j : Fin 3) (y : F), y ≠ 0 → ∀ r : V, b j = y • r →
      semiPerm b σ r = (σ y⁻¹ * y) • r := by
    intro j y hy r hr
    have hr' : r = y⁻¹ • b j := by rw [hr, smul_smul, inv_mul_cancel₀ hy, one_smul]
    rw [hr', semiPerm_smul, semiPerm_basis, smul_smul, mul_assoc, mul_inv_cancel₀ hy, mul_one]
  have hp0 : pointAct ⟨semiPerm b σ, semiPerm_mem b σ⟩ (pt 0) = pt (swap 4 5 0) := by
    rw [swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact pointAct_eq_of_smul _ (hfix 0 x0 hx0 _ hb0)
  have hp1 : pointAct ⟨semiPerm b σ, semiPerm_mem b σ⟩ (pt 1) = pt (swap 4 5 1) := by
    rw [swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact pointAct_eq_of_smul _ (hfix 1 x1 hx1 _ hb1)
  have hp2 : pointAct ⟨semiPerm b σ, semiPerm_mem b σ⟩ (pt 2) = pt (swap 4 5 2) := by
    rw [swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact pointAct_eq_of_smul _ (hfix 2 x2 hx2 _ hb2)
  have hp3 : pointAct ⟨semiPerm b σ, semiPerm_mem b σ⟩ (pt 3) = pt (swap 4 5 3) := by
    rw [swap_apply_of_ne_of_ne (by decide) (by decide)]
    refine pointAct_eq_of_smul _ (c := 1) ?_
    rw [one_smul, ← hsum]
    show semiPerm b σ (b 0 + b 1 + b 2) = _
    rw [semiPerm_add, semiPerm_add, semiPerm_basis, semiPerm_basis, semiPerm_basis]
  have hp4 : pointAct ⟨semiPerm b σ, semiPerm_mem b σ⟩ (pt 4) = pt (swap 4 5 4) := by
    rw [swap_apply_left]
    obtain ⟨c, -, hc⟩ := exists_smul_semiPerm_of_generic hF b hσ hg4 hg5
      (hO.not_smul_of_ne (by decide))
    exact pointAct_eq_of_smul _ hc
  have hp5 : pointAct ⟨semiPerm b σ, semiPerm_mem b σ⟩ (pt 5) = pt (swap 4 5 5) := by
    rw [swap_apply_right]
    obtain ⟨c, -, hc⟩ := exists_smul_semiPerm_of_generic hF b hσ hg5 hg4
      (hO.not_smul_of_ne (by decide))
    exact pointAct_eq_of_smul _ hc
  intro i
  fin_cases i
  exacts [hp0, hp1, hp2, hp3, hp4, hp5]

end CFSG.Quasithin.D35Core

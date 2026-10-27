module

public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityData

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

structure KernelLineDims {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) (Ã : Subgroup (orthDerived Q)) : Prop where
  line_fix : ∀ M : Subgroup Ã, Nat.card M = p → lineFixSpace M = planeFixSpace Ã ⊔ lineSpace M
  dvd : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
    0 < finrank K (lineSpace M) ∧
      Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ∣ finrank K (lineSpace M)
  le : 2 * Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤ finrank K V

open _root_.Classical in
theorem kernelLineDims {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpl : p ≠ ringChar K) (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q))
    (hÃ : Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      ∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype = Ã) :
    KernelLineData Q p Ã ∧ KernelLineDims Q p Ã := by
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  refine ⟨kernelLineData Q hQ hp hp2 hpl A hA hAc Ã hÃ, ?_⟩
  obtain ⟨Ã', hle', hsyl', e, he, huniq, hint, horth, hnd, hline, hex2, hact, hlcm, hrank, hζ⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ A hA hAc
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    DFunLike.coe_injective
  have hEq : Ã' = Ã := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p (A.comap
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))))
    exact (hsyl' P).symm.trans (hÃ.2 P)
  subst hEq
  refine ⟨fun M hM => ?_, hact, hlcm⟩
  have hM1 : 1 < Nat.card M := by rw [hM]; exact hp.one_lt
  have : Finite M := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp hM1
  obtain ⟨⟨a, haM⟩, ha1⟩ := exists_ne (1 : M)
  exact (hline M hM a haM (fun h => ha1 (Subtype.ext h))).2

section Numeric

variable {p : ℕ}

theorem three_le_orderOf_of_not_dvd (q : ℕ) (hpq : ¬ p ∣ q ^ 2 - 1)
    (h0 : Nat.lcm (orderOf (q : ZMod p)) 2 ≠ 0) : 3 ≤ orderOf (q : ZMod p) := by
  by_contra hlt
  push Not at hlt
  have hc0 : orderOf (q : ZMod p) ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hsq : (q : ZMod p) ^ 2 = 1 := by
    rcases (by omega : orderOf (q : ZMod p) = 1 ∨ orderOf (q : ZMod p) = 2) with h | h
    · rw [orderOf_eq_one_iff.mp h]
      simp
    · rw [← h]
      exact pow_orderOf_eq_one _
  apply hpq
  by_cases hq : 1 ≤ q ^ 2
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hq]
    rw [hsq]
    simp
  · have : q ^ 2 - 1 = 0 := by omega
    rw [this]
    exact dvd_zero p

theorem four_le_lcm_of_not_dvd (q : ℕ) (hpq : ¬ p ∣ q ^ 2 - 1)
    (h0 : Nat.lcm (orderOf (q : ZMod p)) 2 ≠ 0) : 4 ≤ Nat.lcm (orderOf (q : ZMod p)) 2 := by
  have h3 := three_le_orderOf_of_not_dvd q hpq h0
  have h2 : 2 ∣ Nat.lcm (orderOf (q : ZMod p)) 2 := Nat.dvd_lcm_right _ _
  have h1 : orderOf (q : ZMod p) ≤ Nat.lcm (orderOf (q : ZMod p)) 2 :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Nat.dvd_lcm_left _ _)
  omega

end Numeric

end CFSG.RankThree.PartOne.KCOrthogonal

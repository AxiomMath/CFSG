module

public import CFSG.LieType.Steinberg.Adjoint.Group
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore

public section

namespace CFSG.StandardType

namespace AutSt

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


variable {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]

theorem sum_cartan_mul_single_self (j : Fin τ.rank) :
    ∑ k, τ.cartan j k * (Pi.single j 1 : Fin τ.rank → ℤ) k = 2 := by
  rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one, Tag.cartan_self]

theorem exists_conj_xPar_single_eq_one [Finite K] [CharP K 2] (j : Fin τ.rank) {c : K}
    (hc : c ≠ 0) :
    ∃ g : adjointGroup τ K, g * xPar F (Pi.single j 1) c * g⁻¹ = xPar F (Pi.single j 1) 1 := by
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (c⁻¹)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact inv_ne_zero hc hs
  refine ⟨torusElement τ K j (Units.mk0 s hs0), ?_⟩
  rw [xPar_simple, F.torusElement_mul_eltElement_mul_inv, ← xPar_simple]
  congr 1
  change ((Units.mk0 s hs0 ^ (∑ k, τ.cartan j k * (Pi.single j 1 : Fin τ.rank → ℤ) k) : Kˣ) : K) *
    c = 1
  rw [sum_cartan_mul_single_self, zpow_two, Units.val_mul, Units.val_mk0, ← hs,
    inv_mul_cancel₀ hc]

theorem exists_conj_xPar_single [Finite K] [CharP K 2] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {z : adjointGroup τ K} (hz : z ∈ rootGroup F K γ) (hz1 : z ≠ 1) :
    ∃ (g : adjointGroup τ K) (j : Fin τ.rank), g * z * g⁻¹ = xPar F (Pi.single j 1) 1 := by
  induction hγ generalizing z with
  | basis j =>
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (IsRoot.basis j) z).1 hz
    have hc : c ≠ 0 := by
      rintro rfl
      exact hz1 (xPar_zero _)
    obtain ⟨g, hg⟩ := exists_conj_xPar_single_eq_one (F := F) j hc
    exact ⟨g, j, hg⟩
  | @reflect i v hv ih =>
    have h1 := weylElement_conj_mem (F := F) i (IsRoot.reflect i hv) hz
    rw [reflect_reflect] at h1
    have h2 : CFSG.LieType.Chevalley.weylElement τ K i * z *
        (CFSG.LieType.Chevalley.weylElement τ K i)⁻¹ ≠ 1 := by
      intro h
      apply hz1
      rw [mul_inv_eq_one, mul_eq_left] at h
      exact h
    obtain ⟨g, j, hg⟩ := ih h1 h2
    exact ⟨g * CFSG.LieType.Chevalley.weylElement τ K i, j, by rw [← hg]; group⟩

theorem orderOf_sl2Upper_mul_sl2Lower [CharP K 2] :
    orderOf (CFSG.LieType.Steinberg.sl2Upper (1 : K) * CFSG.LieType.Steinberg.sl2Lower 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hM : ((CFSG.LieType.Steinberg.sl2Upper (1 : K) * CFSG.LieType.Steinberg.sl2Lower 1 :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change !![(1 : K), 1; 0, 1] * !![(1 : K), 0; 1, 1] = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  refine orderOf_eq_prime ?_ ?_
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hM]
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]
  · intro h
    have e := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [hM, Matrix.SpecialLinearGroup.coe_one] at e
    simp at e

theorem orderOf_xPar_mul_xPar_neg [CharP K 2] {i k : Fin τ.rank} (hk : τ.cartan i k = -1) :
    orderOf (xPar F (Pi.single i 1) (1 : K) * xPar F (-Pi.single i 1) 1) = 3 := by
  obtain ⟨φ, hφ, hU, hL⟩ := exists_sl2_hom (K := K) F hk
  rw [xPar_simple, xPar_neg_simple, ← hU, ← hL, ← map_mul, orderOf_injective φ hφ,
    orderOf_sl2Upper_mul_sl2Lower]

theorem sum_cartan_mul_single (k j : Fin τ.rank) :
    ∑ l, τ.cartan k l * (Pi.single j 1 : Fin τ.rank → ℤ) l = τ.cartan k j := by
  rw [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]

theorem not_isRoot_single_add_single_of_cartan_eq_zero {j k : Fin τ.rank} (hjk : j ≠ k)
    (h0 : τ.cartan k j = 0) : ¬IsRoot τ (Pi.single k 1 + Pi.single j 1) := by
  intro h
  have h' := IsRoot.reflect k h
  have hs : ∑ l, τ.cartan k l * (Pi.single k 1 + Pi.single j 1 : Fin τ.rank → ℤ) l = 2 := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, sum_cartan_mul_single,
      Tag.cartan_self, h0, add_zero]
  have e : reflect τ k (Pi.single k 1 + Pi.single j 1) = Pi.single j 1 - Pi.single k 1 := by
    rw [reflect, hs]
    ext l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hl : l = k
    · subst hl
      simp [Pi.single_eq_of_ne hjk.symm]
    · simp [Pi.single_eq_of_ne hl]
  rw [e] at h'
  exact not_isRoot_single_sub_single hjk h'

theorem commute_xPar_single_xy {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ) {j k : Fin τ.rank}
    (hjk : j ≠ k) (h0 : τ.cartan k j = 0) (c : K) :
    Commute (xPar F (Pi.single j 1) c) (xPar F (Pi.single k 1) 1 * xPar F (-Pi.single k 1) 1) := by
  have hne1 : (Pi.single j 1 + Pi.single k 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
    have := congrFun h j
    simp [Pi.single_eq_of_ne hjk] at this
  have hne2 : (Pi.single j 1 + -Pi.single k 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
    have := congrFun h j
    simp [Pi.single_eq_of_ne hjk] at this
  have hn1 : ¬IsRoot τ (Pi.single j 1 + Pi.single k 1) := by
    rw [add_comm]
    exact not_isRoot_single_add_single_of_cartan_eq_zero hjk h0
  have hn2 : ¬IsRoot τ (Pi.single j 1 + -Pi.single k 1) := by
    rw [← sub_eq_add_neg]
    exact not_isRoot_single_sub_single hjk
  exact (commute_xPar hD hτ (isRoot_single τ j) (isRoot_single τ k) hne1 hn1 c 1).mul_right
    (commute_xPar hD hτ (isRoot_single τ j) (isRoot_neg_single τ k) hne2 hn2 c 1)

section Entrywise


theorem entrywiseAdjointAut_xPar (σ : K ≃+* K) (γ : Fin τ.rank → ℤ) (c : K) :
    entrywiseAdjointAut τ σ (xPar F γ c) = xPar F γ (σ c) := by
  by_cases hγ : IsRoot τ γ
  · apply Subtype.ext
    rw [coe_entrywiseAdjointAut, xPar_of_isRoot hγ, xPar_of_isRoot hγ,
      RootOperatorFamily.coe_eltElement, RootOperatorFamily.coe_eltElement,
      RootDetectExc.units_map_entrywiseHom_eltUnit]
  · rw [xPar_of_not_isRoot hγ, xPar_of_not_isRoot hγ, map_one]

theorem entrywiseAdjointAut_xPar_one (σ : K ≃+* K) (γ : Fin τ.rank → ℤ) :
    entrywiseAdjointAut τ σ (xPar F γ 1) = xPar F γ 1 := by
  rw [entrywiseAdjointAut_xPar, map_one]

end Entrywise

end AutSt

end CFSG.StandardType

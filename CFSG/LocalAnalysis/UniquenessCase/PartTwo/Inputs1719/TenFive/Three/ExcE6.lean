module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE6GraphCoset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ClassicalInvolution.Balance (rootDiagAut_xPar rootChar_single_eq)

theorem IsExtraGood.orderOf_eq_three {S : Type*} [Group S] {x : S} (h : IsExtraGood x)
    (hx : x ≠ 1) : orderOf x = 3 := by
  obtain ⟨H, N, hxH, hH, -⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ hx
  simpa using congrArg Subtype.val (hH.1 ⟨x, hxH⟩)

theorem rootDiagAut_E6_mem_inner_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (a : Fin Tag.E6.rank → Kˣ) :
    ∃ c : adjointGroup Tag.E6 K, MulAut.conj c = rootDiagAut Tag.E6 K a := by
  classical
  set R := (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Kˣ)
    Tag.E6.cartan.transpose).range with hR
  have h3 : R.index ∣ 3 := by
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.index_range_monomialHom_dvd K
      Tag.E6.cartan.transpose).2
    rwa [Matrix.det_transpose, det_cartan_E6] at h1
  have h2 : R.index ∣ (Nat.card K - 1) ^ Tag.E6.rank := by
    have h1 := R.index_dvd_card
    rwa [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_units] at h1
  have h1 : R.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
    · exact h1
    · rw [h1, hK] at h2
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h2) (by norm_num)
  rw [Subgroup.index_eq_one] at h1
  obtain ⟨t, ht⟩ : a ∈ R := h1 ▸ Subgroup.mem_top a
  rw [← ht, monomialHom_transpose_cartan]
  exact rootDiagAut_cartanChar_mem_inner t


theorem orderOf_xPar_zero_mul_five_E6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    orderOf (xPar (rootOperatorFamily .E6) (Pi.single ⟨0, by decide⟩ 1) (1 : K) *
      xPar (rootOperatorFamily .E6) (Pi.single ⟨5, by decide⟩ 1) (-1)) = 3 := by
  classical
  have : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three le_rfl (by rw [hK, pow_one])
  refine (isExtraGood_xPar_single_mul_E6 hK 1 (-1)).orderOf_eq_three fun h1 => ?_
  let b : Fin Tag.E6.rank → Kˣ := fun i => if i = ⟨0, by decide⟩ then -1 else 1
  have hb0 : b ⟨0, by decide⟩ = -1 := if_pos rfl
  have hb5 : b ⟨5, by decide⟩ = 1 := if_neg (by decide)
  have h := congrArg (rootDiagAut Tag.E6 K b) h1
  rw [map_mul, map_one, rootDiagAut_xPar b (isRoot_single Tag.E6 ⟨0, by decide⟩),
    rootDiagAut_xPar b (isRoot_single Tag.E6 ⟨5, by decide⟩), rootChar_single_eq,
    rootChar_single_eq, hb0, hb5] at h
  have h2 := h.trans h1.symm
  simp only [Units.val_neg, Units.val_one, mul_one, one_mul] at h2
  have h3 : (-1 : K) = 1 :=
    xPar_injective (F := rootOperatorFamily Tag.E6) (isRoot_single Tag.E6 ⟨0, by decide⟩)
      (mul_right_cancel h2)
  have h4 : ((2 : ℕ) : K) = 0 := by
    push_cast
    linear_combination -h3
  have h5 := (CharP.cast_eq_zero_iff K 3 2).1 h4
  norm_num at h5

theorem exists_inv_extraGood_E6_graph {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (β : MulAut (adjointGroup TwistTag.E6.tag K))
    (hβg : ∀ h : adjointGroup TwistTag.E6.tag K, (β h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hβ : β ^ 2 = 1) :
    ∃ x : adjointGroup TwistTag.E6.tag K, orderOf x = 3 ∧ β x = x⁻¹ ∧ IsExtraGood x := by
  have : CharP K 3 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_three le_rfl (by rw [hK, pow_one])
  have hQP : ∃ w : adjointGroup TwistTag.E6.tag K, (orderOf w = 3 ∧ IsExtraGood w) ∧
      diagramMap TwistTag.E6 K * (w : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ =
        (w : ModGL TwistTag.E6.tag K)⁻¹ := by
    refine ⟨_, ⟨?_, ?_⟩, diagramMap_conj_xPar_zero_mul_five_E6 K 1⟩
    · exact orderOf_xPar_zero_mul_five_E6 hK
    · exact isExtraGood_xPar_single_mul_E6 hK 1 (-1)
  have hQD : ∃ w : adjointGroup TwistTag.E6.tag K, (orderOf w = 3 ∧ IsExtraGood w) ∧
      rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 K *
          (w : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 K)⁻¹ =
        (w : ModGL TwistTag.E6.tag K)⁻¹ := by
    refine ⟨_, ⟨?_, ?_⟩, rootDiag_diagramMap_conj_xPar_one_E6 (K := K) ![1, -1, 1, 1, 1, 1] rfl 1⟩
    · exact orderOf_xPar Nat.prime_three (isRoot_single _ _) one_ne_zero
    · exact isExtraGood_xPar_single (τ := Tag.E6) (Or.inr (Or.inl rfl)) hK _ 1
  obtain ⟨x, hx, hxo, hxg⟩ := exists_inv_E6_graph_of Nat.prime_three (by norm_num) (e := 1)
    (by rw [hK, pow_one]) le_rfl (Q := fun w => orderOf w = 3 ∧ IsExtraGood w)
    (fun θ hθ w hw => ⟨(orderOf_injective θ hθ w).trans hw.1, hw.2.map hθ⟩) hQP hQD g a β hβg hβ
  exact ⟨x, hxo, hx, hxg⟩

theorem involGood_E6_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    InvolGood (adjointGroup .E6 K) := by
  classical
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hnf β
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  by_cases hσ1 : σ = 1
  swap
  · exact (Nat.not_even_one (hquad 3 1 Nat.prime_three le_rfl (by rw [hK, pow_one]) σ
      (hsq β g a σ ε hgaσ hβ2) hσ1).1).elim
  subst hσ1
  have h1 : ∀ u : adjointGroup Tag.E6 K,
      Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (u : ModGL Tag.E6 K) = u := fun u =>
    Units.ext (entrywise_id (R := K) _)
  have hQ : exactQ Tag.E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) ^ (ε : ℕ) := rfl
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h := ε.2
    change (ε : ℕ) < 2 at h
    omega
  rcases hε with h0 | h0
  ·
    have hQ0 : exactQ Tag.E6 K ε = 1 := by
      rw [hQ, h0, pow_zero]
      rfl
    obtain ⟨c, hc⟩ := rootDiagAut_E6_mem_inner_three hK a
    have hβeq : β = MulAut.conj (g * c) := by
      rw [map_mul, hc]
      exact MulEquiv.ext fun u => Subtype.ext (by
        rw [hgaσ u, hQ0, inv_one, mul_one, mul_one, h1, MulAut.mul_apply, MulAut.conj_apply,
          Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
        group)
    subst hβeq
    exact Or.inl (exists_inv_extraGood_of_conj_involution (Or.inr (Or.inl rfl)) hK _ hβ)
  ·
    have hQ1 : exactQ Tag.E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) := by
      rw [hQ, h0, pow_one]
    exact Or.inl (exists_inv_extraGood_E6_graph hK g a β (fun u => by
      have h2 := hgaσ u
      rw [hQ1, h1 u] at h2
      exact h2) hβ2)

theorem involAt_E6 : InvolAt .E6 := by
  intro S _ _ n _ _ hS
  obtain ⟨-, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  exact InvolGood.of_mulEquiv φ.symm (involGood_E6_three (by rw [hK, pow_one]))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

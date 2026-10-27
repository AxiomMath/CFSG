module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcTorus
public import CFSG.LieType.Chevalley.CLSOddG2F4E8AllInvolutionFourGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem involGood_F4_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    InvolGood (adjointGroup .F4 K) := by
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  obtain ⟨-, Θ, -, -, hker, hinv⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form Nat.prime_three (by norm_num) le_rfl K
      (by rw [hK, pow_one]) .F4 (Or.inl rfl)
  rcases hinv β hβ2 with h1 | ⟨hfe, -⟩
  · have h2 : β ∈ Θ.ker := MonoidHom.mem_ker.2 h1
    rw [hker] at h2
    obtain ⟨g, rfl⟩ := h2
    exact Or.inl (exists_inv_extraGood_of_conj_involution (Or.inl rfl) hK g hβ)
  · exact (Nat.not_even_one hfe).elim

theorem involGood_E8_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    InvolGood (adjointGroup .E8 K) := by
  classical
  intro β hβ
  have hβ2 : β ^ 2 = 1 := by rw [← hβ, pow_orderOf_eq_one]
  suffices hin :
      β ∈ (MulAut.conj : adjointGroup Tag.E8 K →* MulAut (adjointGroup Tag.E8 K)).range by
    obtain ⟨g, rfl⟩ := hin
    exact Or.inl (exists_inv_extraGood_of_conj_involution (Or.inr (Or.inr rfl)) hK g hβ)
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form .E8 (Or.inr (Or.inr rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hnf β
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E8 (Or.inr (Or.inr rfl)) K
  have hQ : exactQ Tag.E8 K ε = 1 := rfl
  have hβ' : ∀ u, (β u : ModGL Tag.E8 K) = (g : ModGL Tag.E8 K) * rootDiagUnit Tag.E8 a *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.E8 K) * (rootDiagUnit Tag.E8 a)⁻¹ *
        (g : ModGL Tag.E8 K)⁻¹ := fun u => by
    rw [hgaσ u, hQ, inv_one, mul_one, mul_one]
  by_cases hσ1 : σ = 1
  · subst hσ1
    obtain ⟨c, hc⟩ :=
      CFSG.LieType.Chevalley.OddG2F4E8AllInvolution.rootDiagAut_mem_inner_of_det_eq_one
        det_cartan_E8 a (K := K)
    have h1 : ∀ u : adjointGroup Tag.E8 K,
        Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (u : ModGL Tag.E8 K) = u := fun u =>
      Units.ext (entrywise_id (R := K) _)
    have hβeq : β = MulAut.conj g * rootDiagAut Tag.E8 K a := MulEquiv.ext fun u =>
      Subtype.ext (by
        rw [hβ' u, h1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, coe_rootDiagAut]
        group)
    exact ⟨g * c, by rw [map_mul, hc, hβeq]⟩
  · exact (Nat.not_even_one (hquad 3 1 Nat.prime_three le_rfl (by rw [hK, pow_one]) σ
      (hsq β g a σ ε hgaσ hβ2) hσ1).1).elim

theorem involAt_F4 : InvolAt .F4 := by
  intro S _ _ n _ _ hS
  obtain ⟨-, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
  exact InvolGood.of_mulEquiv φ.symm (involGood_F4_three (by rw [hK, pow_one]))

theorem involAt_E8 : InvolAt .E8 := by
  intro S _ _ n _ _ hS
  obtain ⟨-, hm⟩ := hS.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
  exact InvolGood.of_mulEquiv φ.symm (involGood_E8_three (by rw [hK, pow_one]))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

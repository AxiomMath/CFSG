module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Assembly
public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

open CFSG.Blueprint CFSG.SignalizerFunctorTheorem.NonLocalExc

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {a : ℕ} {K : Type} [Field K]

@[expose] noncomputable def suzukiRep (F : Type) [Field F] [Algebra K F] :
    suzukiGroup a K →* Module.End F (Fin 4 → F) :=
  ((CFSG.SignalizerFunctorTheorem.NonLocal.extendScalars K F (Fin 4)).toMonoidHom).comp
    ((Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp (suzukiGroup a K).subtype)

theorem suzukiRep_injective (F : Type) [Field F] [Algebra K F] :
    Function.Injective (suzukiRep (a := a) (K := K) F) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  exact CFSG.SignalizerFunctorTheorem.NonLocal.extendScalars_injective K F (Fin 4) hgh

theorem le_normalizer_of_conj_mem {X : Type*} [Group X] {J E : Subgroup X}
    (hnorm : ∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E) : J ≤ Subgroup.normalizer (E : Set X) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hnorm j hj x hx, fun hx => ?_⟩
  have := hnorm j⁻¹ (J.inv_mem hj) _ hx
  simpa [mul_assoc] using this

theorem nonLocalized_suzuki_of_simple
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {J : Subgroup (suzukiGroup a K)} (hJ : IsSimpleGroup J) (hns : ¬ Group.IsSolvable J)
    (hcent : ∀ x : suzukiGroup a K, (∀ j ∈ J, x * j = j * x) → x = 1) : NonLocalized J := by
  classical
  have hX : Finite (suzukiGroup a K) := inferInstance
  have h2 : CharP K 2 := (CFSG.LieType.Ree.suzuki_frobenius_exponents a K hK).1
  let F := AlgebraicClosure K
  have hF2 : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  refine nonLocalized_of_perm_data hJ hcent Nat.prime_two ?_ (suzukiRep F)
    (suzukiRep_injective F) J le_rfl ?_
  · intro E hE hnorm
    by_contra hE0
    obtain ⟨-, hsolv⟩ :=
      CFSG.LieType.suzuki_nontrivial_two_subgroup_normalizer_solvable hK E hE hE0
    apply hns
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_normalizer_of_conj_mem hnorm))
  · have hfin : Finite J := inferInstance
    have h60 : 60 ≤ Nat.card J := by
      by_contra hlt
      exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (not_le.1 hlt))
    have hdim : Module.finrank F (Fin 4 → F) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hdim]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num [Nat.factorial]) hdvd
    norm_num [Nat.factorial] at this
    omega

end CFSG.SignalizerFunctorTheorem.CatalogBridge

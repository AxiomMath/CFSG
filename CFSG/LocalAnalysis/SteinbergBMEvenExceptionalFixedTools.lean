module

public import CFSG.LieType.Chevalley.RootWeightFiltrationData
import CFSG.LieType.Chevalley.RootLocalComponentFree
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem not_normal_simple_inner_of_rootWeightDatum
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : RootWeightDatum K) (hZ : center D.group = ⊥) (t : D.group)
    (ht : orderOf (MulAut.conj t) = 2)
    (S : Subgroup ((MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id _))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL D.tag K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ hinj t]
    exact ht
  have hQp : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hQ : zpowers t ≠ ⊥ := by
    intro h
    have ht1 : t = 1 := zpowers_eq_bot.mp h
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨hchar, -⟩ := RootWeightDatum.defining_characteristic_root_local_groups_component_free
    D 2 (zpowers t) hQp hQ (centralizer (zpowers t : Set D.group)) (Or.inr rfl)
  have heq : (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id _) =
      centralizer (zpowers t : Set D.group) := by
    rw [zpowers_eq_closure, centralizer_closure]
    ext x
    rw [mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  obtain ⟨S', hS'n, hS's, hS'nab, -⟩ :=
    exists_normal_simple_of_mulEquiv (MulEquiv.subgroupCongr heq) S hSn hSs hSnab
  exact not_normal_simple_of_isCharacteristicP hchar S' hS'n hS's hS'nab

end CFSG.LocalAnalysis.SteinbergBM

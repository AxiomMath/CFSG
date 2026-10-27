module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathSolvable

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] [CharP k 2] {V : Type v} [AddCommGroup V] [Module k V] [Finite V]

theorem solvable_two_core_free_FF_action_three_in_fitting {H : Subgroup (V ≃ₗ[k] V)}
    [Group.IsSolvable H] (hO2 : pCore 2 H = ⊥) :
    (∀ A : Subgroup (V ≃ₗ[k] V), A ≤ H → CFSG.IsElementaryAbelian 2 A → A ≠ ⊥ →
        Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A →
        Nat.card k = 2 ∧ 3 ∣ Nat.card (fittingSubgroup H)) ∧
      (¬ 3 ∣ Nat.card (fittingSubgroup H) → ∀ A : Subgroup (V ≃ₗ[k] V), A ≤ H →
        CFSG.IsElementaryAbelian 2 A → A ≠ ⊥ →
        weight (MonoidHom.id (V ≃ₗ[k] V)) A < Nat.card V) ∧
      (¬ 3 ∣ Nat.card H → ∀ A : Subgroup (V ≃ₗ[k] V), A ≤ H →
        CFSG.IsElementaryAbelian 2 A → A ≠ ⊥ →
        weight (MonoidHom.id (V ≃ₗ[k] V)) A < Nat.card V) := by
  classical
  have : Finite (V ≃ₗ[k] V) := CFSG.QuasithinUnique.Setup.Layer.finite_linearEquiv
  set Fn : Subgroup (V ≃ₗ[k] V) := (fittingSubgroup H).map H.subtype with hFn
  have hFnH : Fn ≤ H := map_subtype_le _
  have hFsub : Fn.subgroupOf H = fittingSubgroup H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have hFnn : (Fn.subgroupOf H).Normal := by
    rw [hFsub]
    infer_instance
  have hcardF : Nat.card Fn = Nat.card (fittingSubgroup H) :=
    card_map_of_injective H.subtype_injective
  have : Group.IsNilpotent Fn := Group.nilpotent_of_mulEquiv
    ((fittingSubgroup H).equivMapOfInjective H.subtype H.subtype_injective)
  have hFodd : Odd (Nat.card Fn) :=
    hcardF ▸ CFSG.QuasithinUnique.Setup.Wreath.odd_card_fittingSubgroup hO2
  have hCF : H ⊓ centralizer (Fn : Set (V ≃ₗ[k] V)) ≤ Fn := by
    intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have hx' : (⟨x, hxH⟩ : H) ∈ centralizer (fittingSubgroup H : Set H) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp hxC _ ⟨y, hy, rfl⟩)
    exact ⟨_, CFSG.QuasithinUnique.Setup.Wreath.solvable_fitting_self_centralizing inferInstance
      hx', rfl⟩
  have hmain : ∀ A : Subgroup (V ≃ₗ[k] V), A ≤ H → CFSG.IsElementaryAbelian 2 A → A ≠ ⊥ →
      Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) A →
      Nat.card k = 2 ∧ 3 ∣ Nat.card (fittingSubgroup H) := by
    intro A hAH hAel hAne hAoff
    obtain ⟨B, hBH, hBne, hBel, hBoff, hBstrict⟩ := exists_minOffender hAH hAne hAel hAoff
    have hcomm := CFSG.QuasithinUnique.Setup.Wreath.commutator_ne_bot_of_centralizer_le hBH hBne
      hBel hFodd hCF
    obtain ⟨hk, -, -, h3, -⟩ := nilpotent_offender_natural_S3_factors.{_, _, 0} hFnH hFnn hFodd
      hBH hBel hBne hBoff hBstrict hcomm
    refine ⟨hk, ?_⟩
    have hle : ⁅Fn, B⁆ ≤ Fn := by
      rw [commutator_le]
      intro f hf b hb
      have h1 : b * f⁻¹ * b⁻¹ ∈ Fn :=
        (normal_subgroupOf_iff hFnH).1 hFnn _ _ (inv_mem hf) (hBH hb)
      have e : ⁅f, b⁆ = f * (b * f⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hf h1
    rw [← hcardF, ← h3]
    exact card_dvd_of_le hle
  refine ⟨hmain, fun h3 A hAH hAel hAne => lt_of_not_ge fun hoff =>
    h3 (hmain A hAH hAel hAne hoff).2, fun h3 A hAH hAel hAne => lt_of_not_ge fun hoff =>
    h3 ((hmain A hAH hAel hAne hoff).2.trans (card_subgroup_dvd_card _))⟩

end CFSG.Quasithin.SteinbergCD

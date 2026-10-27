module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint F4Weyl
  EvenG2 EvenF4QPlus CFSG.RankThree.E6
open scoped Pointwise commutatorElement

namespace EvenF4QPlus

theorem commutator_sup_le_of_le_normalizer {G : Type*} [Group G] {H Q : Subgroup G}
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hN : H ≤ Subgroup.normalizer (Q : Set G)) :
    ⁅H ⊔ Q, H ⊔ Q⁆ ≤ Q := by
  have hset : ((H ⊔ Q : Subgroup G) : Set G) = (H : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  have hconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.1 (hN hh) q).1 hq
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, hset] at hx hy
  obtain ⟨h, hh, q, hq, rfl⟩ := hx
  obtain ⟨h', hh', q', hq', rfl⟩ := hy
  have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
      (h' * q'⁻¹ * h'⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e1, ← hH h hh h' hh']
  have hq1 : h'⁻¹ * q * h'⁻¹⁻¹ ∈ Q := hconj _ (inv_mem hh') q hq
  rw [inv_inv] at hq1
  exact mul_mem (hconj _ (mul_mem hh hh') _ (mul_mem hq1 (mul_mem hq' (inv_mem hq))))
    (hconj _ hh' _ (inv_mem hq'))

end EvenF4QPlus

end CFSG.RankThree.Chevalley

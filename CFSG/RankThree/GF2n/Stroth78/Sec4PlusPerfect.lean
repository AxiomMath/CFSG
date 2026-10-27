module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs
public import CFSG.RankThree.GF2n.Stroth78.Sec3Perfect
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec3One

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem commutator_Xsub_eq_of_threeFourPlus (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) :
    ⁅Xsub S a, Xsub S a⁆ = Xsub S a := by
  obtain ⟨-, hroot, -, hclass⟩ := stroth78_31 S h h217
  obtain ⟨α, hα, β, hβ, h4⟩ := h34
  have hα2 : α * α = 1 := by
    rw [← pow_two, ← hroot.1 α hα]
    exact pow_orderOf_eq_one α
  have hβ2 : β * β = 1 := by
    rw [← pow_two, ← hroot.1 β hβ]
    exact pow_orderOf_eq_one β
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ2
  have hβα : orderOf (β * α) = 4 := by
    have : β * α = (α * β)⁻¹ := by rw [mul_inv_rev, hαinv, hβinv]
    rw [this, orderOf_inv, h4]
  have hsq : (β * α) ^ 2 ∈ Eset S a := hroot.2.2 β hβ α hα hβα
  have hconj : α * β * α⁻¹ ∈ Eset S a := Eset_conj_mem S a hβ α
  have hprod : β * (α * β * α⁻¹) ∈ Eset S a := by
    have : β * (α * β * α⁻¹) = (β * α) ^ 2 := by
      rw [hαinv, pow_two, mul_assoc, mul_assoc]
    rw [this]
    exact hsq
  exact commutator_Xsub_eq_of_mul_mem S
    (fun α hα α' hα' => (hclass α hα α').mp hα') hβ hconj hprod

end CFSG.RankThree.GF2n.Stroth78

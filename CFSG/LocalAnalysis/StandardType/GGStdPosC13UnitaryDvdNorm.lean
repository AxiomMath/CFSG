module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

theorem unitDvd_conj_perm_mem_normalizer {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hd : 3 ≤ d) {A : Subgroup (MulAut L')} (hAp : ∀ a ∈ A, a ^ p = 1)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (σ : Equiv.Perm (Fin d)) :
    MulAut.conj (φ (permSU hM.field σ)) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  have hHA : Subgroup.closure (heartSetU φ p) ≤ A := by
    refine (Subgroup.closure_le A).mpr ?_
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have key : ∀ τ : Equiv.Perm (Fin d), ∀ a ∈ A,
      MulAut.conj (φ (permSU hM.field τ)) * a * (MulAut.conj (φ (permSU hM.field τ)))⁻¹ ∈ A := by
    intro τ a ha
    have h := A.mul_mem (hHA (UnitAct.conj_mul_inv_mem_heart hM hp hpq hd hAp hdiag τ ha)) ha
    rwa [inv_mul_cancel_right] at h
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key σ h, fun hh => ?_⟩
  have h2 := key σ⁻¹ _ hh
  rw [← UnitAct.permSU_inv, map_inv, map_inv] at h2
  have e : (MulAut.conj (φ (permSU hM.field σ)))⁻¹ *
      (MulAut.conj (φ (permSU hM.field σ)) * h * (MulAut.conj (φ (permSU hM.field σ)))⁻¹) *
        ((MulAut.conj (φ (permSU hM.field σ)))⁻¹)⁻¹ = h := by group
  rwa [e] at h2

end CFSG.StandardType

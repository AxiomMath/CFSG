module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 1(a)
-/

public theorem proposition_1_a
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ g : G, g ∉ H →
      ∃ h : H,
        rightConjugate H g ⊓ H = rightConjugate D (h : G) ∧
          Odd (Nat.card (↥(rightConjugate H g ⊓ H))) := by
  classical
  obtain ⟨α, hH⟩ := hA1.point_stabilizer
  subst H
  intro g hgH
  let β : Ω := t⁻¹ • α
  let γ : Ω := g⁻¹ • α
  have hβ_ne : α ≠ β := by
    intro h
    apply hA1.t_not_mem_H
    change t • α = α
    have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
    simpa [β, htinv] using h.symm
  have hγ_ne : α ≠ γ := by
    intro h
    apply hgH
    change g • α = α
    simpa [γ, smul_smul] using congrArg (fun z => g • z) h
  obtain ⟨k, hkα, hkγ⟩ :=
    (MulAction.is_two_pretransitive_iff.mp hA1.two_transitive)
      hγ_ne hβ_ne
  have hkH : k ∈ MulAction.stabilizer G α := by
    change k • α = α
    exact hkα
  have hk_inv_α : k⁻¹ • α = α := by
    calc
      k⁻¹ • α = k⁻¹ • (k • α) := by rw [hkα]
      _ = α := by simp [smul_smul]
  have hk_inv_β : k⁻¹ • β = γ := by
    calc
      k⁻¹ • β = k⁻¹ • (k • γ) := by rw [hkγ]
      _ = γ := by simp [smul_smul]
  have hD :
      D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    simpa [β, rightConjugate_stabilizer] using hA1.D_eq
  have hconjD :
      rightConjugate D k =
        MulAction.stabilizer G γ ⊓ MulAction.stabilizer G α := by
    rw [hD, rightConjugate, Subgroup.conjBy,
      Subgroup.map_inf _ _ _ (MulAut.conj k⁻¹).injective]
    change rightConjugate (MulAction.stabilizer G α) k ⊓
        rightConjugate (MulAction.stabilizer G β) k =
      MulAction.stabilizer G γ ⊓ MulAction.stabilizer G α
    rw [rightConjugate_stabilizer, rightConjugate_stabilizer,
      hk_inv_α, hk_inv_β, inf_comm]
  have htarget :
      rightConjugate (MulAction.stabilizer G α) g ⊓ MulAction.stabilizer G α =
        MulAction.stabilizer G γ ⊓ MulAction.stabilizer G α := by
    simp [γ, rightConjugate_stabilizer]
  have hcard_conj :
      Nat.card (rightConjugate D k) = Nat.card D := by
    rw [rightConjugate, Subgroup.conjBy]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective D (MulAut.conj k⁻¹).toMonoidHom
        (MulAut.conj k⁻¹).injective).symm.toEquiv)
  refine ⟨⟨k, hkH⟩, htarget.trans hconjD.symm, ?_⟩
  rw [htarget, ← hconjD, hcard_conj]
  exact hA1.D_odd

end PFchapter1section1
end CFSG.BenderSuzuki

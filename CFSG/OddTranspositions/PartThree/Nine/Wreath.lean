module

public import CFSG.OddTranspositions.PartThree.Nine.WreathCases
public import CFSG.OddTranspositions.PartThree.Nine.WreathTwo
public import CFSG.OddTranspositions.SixSixWreathClass
import CFSG.Timmesfeld.Bridge.Asc72WreathConn
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.SixSix
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki Equiv SemidirectProduct

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_wreath_normalized (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G}
    (hM : Asc72.IsMinimalNormal M) (hMns : ¬ IsSimpleGroup M) :
    ∃ f n : ℕ, 2 ≤ f ∧ ∃ a b : Fin n, a ≠ b ∧ ∃ Ψ : G ≃* L2Wreath f n,
      Ψ hC.d = inr (swap a b) ∧ ∀ x, x ∈ D ↔ IsConj (inr (swap a b) : L2Wreath f n) (Ψ x) := by
  obtain ⟨f, n, hf, Φ, hΦ⟩ :=
    exists_l2Wreath_class_of_not_isSimpleGroup_minimalNormal hC hrad hM hMns
  obtain ⟨a, b, hab, -⟩ := hΦ hC.d hC.hd
  have hcl : ∀ x ∈ D, IsConj (inr (swap a b) : L2Wreath f n) (Φ x) := fun x hx =>
    (WreathConn.isConj_inr_swap_iff hab _).mpr (hΦ x hx)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hcl hC.d hC.hd)
  set Ψ : G ≃* L2Wreath f n := Φ.trans (MulAut.conj c⁻¹) with hΨdef
  have hΨ : ∀ x, Ψ x = c⁻¹ * Φ x * c⁻¹⁻¹ := fun x => by
    rw [hΨdef, MulEquiv.trans_apply, MulAut.conj_apply]
  have hΨu : Ψ hC.d = inr (swap a b) := by
    rw [hΨ, ← hc]
    group
  refine ⟨f, n, hf, a, b, hab, Ψ, hΨu, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [hΨ]
    exact (hcl x hx).trans (isConj_iff.mpr ⟨c⁻¹, rfl⟩)
  · rw [← hΨu] at hx
    have h := MonoidHom.map_isConj Ψ.symm.toMonoidHom hx
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
    rw [hC.setup.eq_setOf_isConj hC.hd]
    exact h

theorem lemma9_2Wreath : Lemma9_2Wreath := by
  intro G _ _ D hC hH ⟨M, hM, hMns⟩
  obtain ⟨f, n, hf, a, b, hab, Ψ, hΨu, hΨD⟩ := exists_wreath_normalized hC hH.solv hM hMns
  have hn : 2 ≤ n := by
    have := a.isLt
    have := b.isLt
    have := Fin.val_ne_of_ne hab
    omega
  rcases (show n = 2 ∨ (3 ≤ n ∧ n ≤ 4) ∨ 5 ≤ n by omega) with rfl | ⟨h3, h4⟩ | h5
  · have hs : swap a b = swap (0 : Fin 2) 1 := by
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · rfl
      · exact swap_comm _ _
      · exact absurd rfl hab
    rw [hs] at hΨu hΨD
    exact ⟨f, hf, nonempty_quotientCenter_mulEquiv_of_wreath_two hC hf Ψ hΨu hΨD, Or.inl ⟨Ψ⟩⟩
  · exact absurd (disconnected_of_wreath_le_four h3 h4 hab Ψ hΨD) hC.conn
  · exact (false_of_wreath_five_le hC hH.bender h5 hab Ψ hΨu hΨD).elim

end CFSG.OddTranspositions.PartThree.Nine

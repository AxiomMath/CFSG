module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralCoverIrreducible

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)

theorem suzukiCoverDerived_transitive (hm : 0 < m)
    (w z : commutator (suzukiCoverRoot m)) (hw : w ≠ 1) (hz : z ≠ 1) :
    ∃ t : suzukiCoverTorus m,
      coverDerivedAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) t w = z := by
  let e := suzukiCoverDerivedEquiv m hm
  have hw0 : (e w).toAdd ≠ 0 := by
    intro h
    apply hw
    apply e.injective
    simpa using congrArg Multiplicative.ofAdd h
  have hz0 : (e z).toAdd ≠ 0 := by
    intro h
    apply hz
    apply e.injective
    simpa using congrArg Multiplicative.ofAdd h
  let c : Kˣ := Units.mk0 ((e z).toAdd / (e w).toAdd) (div_ne_zero hz0 hw0)
  obtain ⟨x, hx⟩ := (suzukiCoverNorm_bijective m).2 c
  refine ⟨suzukiCoverTorusHom m x, e.injective ?_⟩
  apply Multiplicative.toAdd.injective
  rw [suzukiCoverDerived_action m hm, hx]
  exact div_mul_cancel₀ _ hw0

theorem suzukiCoverDerived_irreducible (hm : 0 < m) :
    CoverDerivedIrreducible (suzukiCoverRoot m) (suzukiCoverTorus m)
      (suzukiCoverTorus_le_normalizer m) := by
  intro R hR
  by_cases hbot : R = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    apply (Subgroup.eq_top_iff' R).mpr
    intro z
    by_cases hz : z = 1
    · exact hz ▸ R.one_mem
    · obtain ⟨t, ht⟩ := suzukiCoverDerived_transitive m hm w.val z
        (fun h => hw (Subtype.ext h)) hz
      exact ht ▸ hR t w.val w.property

theorem suzukiCoverAbelian_additive_action (hm : 0 < m) (x : Kˣ)
    (v : Additive (Abelianization (suzukiCoverRoot m))) :
    (suzukiCoverAbelianEquiv m hm).toAdditiveLeft
      (Additive.ofMul (coverAbelianAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x) v.toMul)) =
      (x : K) * (suzukiCoverAbelianEquiv m hm).toAdditiveLeft v :=
  suzukiCoverAbelian_action m hm x v.toMul

theorem suzukiCoverAbelian_inverse_action (hm : 0 < m) (x : Kˣ) (v : K) :
    (suzukiCoverAbelianEquiv m hm).toAdditiveLeft.symm ((x : K) * v) =
      Additive.ofMul (coverAbelianAction (suzukiCoverRoot m) (suzukiCoverTorus m)
        (suzukiCoverTorus_le_normalizer m) (suzukiCoverTorusHom m x)
        ((suzukiCoverAbelianEquiv m hm).toAdditiveLeft.symm v).toMul) := by
  apply (suzukiCoverAbelianEquiv m hm).toAdditiveLeft.injective
  rw [AddEquiv.apply_symm_apply, suzukiCoverAbelian_additive_action,
    AddEquiv.apply_symm_apply]

theorem suzukiCoverAbelian_invariant_eq_zero (hm : 0 < m)
    (b : Additive (Abelianization (suzukiCoverRoot m)) →+
      Additive (Abelianization (suzukiCoverRoot m)) →+ ZMod 2)
    (hb : CoverAbelianInvariant (suzukiCoverRoot m) (suzukiCoverTorus m)
      (suzukiCoverTorus_le_normalizer m) b) : b = 0 := by
  let e := (suzukiCoverAbelianEquiv m hm).toAdditiveLeft
  let c : K →+ K →+ ZMod 2 :=
    { toFun := fun x => (b (e.symm x)).comp e.symm.toAddMonoidHom
      map_zero' := by ext y; simp
      map_add' := by intro x y; ext z; simp }
  have hcard : 4 < Nat.card K := by
    rw [GaloisField.card 2 (2 * m + 1) (by omega)]
    have h := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (show 3 ≤ 2 * m + 1 by omega)
    norm_num at h ⊢
    omega
  have hc : ∀ x y, c x y = 0 := by
    apply binaryScalarInvariantAddHom_eq_zero hcard c
    intro a x y
    change b (e.symm ((a : K) * x)) (e.symm ((a : K) * y)) =
      b (e.symm x) (e.symm y)
    rw [suzukiCoverAbelian_inverse_action, suzukiCoverAbelian_inverse_action]
    exact hb (suzukiCoverTorusHom m a) (e.symm x).toMul (e.symm y).toMul
  apply AddMonoidHom.ext
  intro v
  apply AddMonoidHom.ext
  intro w
  have h := hc (e v) (e w)
  change b (e.symm (e v)) (e.symm (e w)) = 0 at h
  simpa only [AddEquiv.symm_apply_apply, AddMonoidHom.zero_apply] using h

end CFSG.ShultStronglyClosedTI

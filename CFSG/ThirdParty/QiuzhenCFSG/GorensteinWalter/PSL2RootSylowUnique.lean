module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Uniqueness of a defining-characteristic Sylow through a nontrivial element

A nonidentity element of a root Sylow subgroup of `PSL₂` fixes the unique
projective-line point attached to that Sylow.  Consequently two defining-
characteristic Sylow subgroups containing the same nonidentity element are
equal.  This is the uniqueness input for the equation-(11) root-Sylow count.
-/

noncomputable section
namespace CFSG.GorensteinWalter

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

private theorem upper_fixed_unique
    (K : Type u) [Field K]
    (a : K) (ha : a ≠ 0) (x : PSL2ProjectiveLine K) :
    psl2QuotientMap K (sl2UpperUnipotent a) • x = x ↔
      x = psl2ProjectiveInfinity K := by
  constructor
  · induction x using Projectivization.ind with
    | h v hv =>
        intro hfix
        rw [psl2QuotientMap_smul, Projectivization.smul_mk,
          Projectivization.mk_eq_mk_iff] at hfix
        obtain ⟨c, hc⟩ := hfix
        have hUv :
            sl2UpperUnipotent a • v = ![v 0 + a * v 1, v 1] := by
          change (sl2UpperUnipotent a).val *ᵥ v = _
          ext i
          fin_cases i <;>
            simp [sl2UpperUnipotent, Matrix.mulVec, Matrix.vecHead,
              Matrix.vecTail]
        rw [hUv] at hc
        by_cases hv1 : v 1 = 0
        · rw [psl2ProjectiveInfinity,
            Projectivization.mk_eq_mk_iff']
          refine ⟨v 0, ?_⟩
          ext i
          fin_cases i <;> simp [hv1]
        · have hc1 : (c : K) = 1 := by
            apply mul_right_cancel₀ hv1
            simpa [Units.smul_def] using congrFun hc 1
          have h0 : v 0 = v 0 + a * v 1 := by
            simpa [Units.smul_def, hc1] using congrFun hc 0
          have hav : a * v 1 = 0 := by
            apply add_left_cancel (a := v 0)
            simpa using h0.symm
          exact (ha (mul_eq_zero.mp hav |>.resolve_right hv1)).elim
  · rintro rfl
    have hu :
        psl2QuotientMap K (sl2UpperUnipotent a) ∈
          psl2UpperUnipotentSubgroup K :=
      (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨a, rfl⟩
    have hB := psl2UpperUnipotent_le_borel hu
    exact MulAction.mem_stabilizer_iff.mp hB

/-- Two defining-characteristic Sylow subgroups of `PSL₂(K)` containing the
same nonidentity element are equal. -/
public theorem psl2_sylow_eq_of_mem_nontrivial
    (K : Type u) [Field K] [Finite K]
    {r f : ℕ} [Fact r.Prime]
    (hKcard : Nat.card K = r ^ f)
    (S T : Sylow r (PSL2 K)) (g : PSL2 K)
    (hgS : g ∈ (S : Subgroup (PSL2 K))) (hg : g ≠ 1)
    (hgT : g ∈ (T : Subgroup (PSL2 K))) : S = T := by
  let U : Sylow r (PSL2 K) := psl2UpperUnipotentSylow K hKcard
  obtain ⟨a, ha⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := PSL2 K) S U
  let g' : PSL2 K := a * g * a⁻¹
  have hg'U : g' ∈ (U : Subgroup (PSL2 K)) := by
    have hgsmul : g' ∈
        ((a • S : Sylow r (PSL2 K)) : Subgroup (PSL2 K)) := by
      change a * g * a⁻¹ ∈
        (S : Subgroup (PSL2 K)).map (MulAut.conj a).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨g, hgS, rfl⟩
    rw [ha] at hgsmul
    exact hgsmul
  have hg'upper : g' ∈ psl2UpperUnipotentSubgroup K := by
    simpa [U] using hg'U
  obtain ⟨z, hz⟩ := (mem_psl2UpperUnipotentSubgroup_iff g').mp hg'upper
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hg
    apply (MulAut.conj a).injective
    have hg'one : g' = 1 := by
      rw [hz, hz0, sl2UpperUnipotent_zero]
      exact (psl2QuotientMap K).map_one
    simpa [MulAut.conj_apply, g'] using hg'one
  have hfix_unique : ∀ x : PSL2ProjectiveLine K,
      g • x = x → a • x = psl2ProjectiveInfinity K := by
    intro x hx
    apply (upper_fixed_unique K z hz0 (a • x)).mp
    rw [← hz]
    dsimp [g']
    simp only [mul_smul, inv_smul_smul]
    rw [hx]
  let e := psl2ProjectiveLineEquivSylow K hKcard
  let xS : PSL2ProjectiveLine K := e.symm S
  let xT : PSL2ProjectiveLine K := e.symm T
  have hgfixS : g • xS = xS := by
    rw [← MulAction.mem_stabilizer_iff]
    rw [psl2ProjectiveLineEquivSylow_stabilizer K hKcard]
    simpa [e, xS] using (Subgroup.le_normalizer hgS)
  have hgfixT : g • xT = xT := by
    rw [← MulAction.mem_stabilizer_iff]
    rw [psl2ProjectiveLineEquivSylow_stabilizer K hKcard]
    simpa [e, xT] using (Subgroup.le_normalizer hgT)
  apply e.symm.injective
  apply (EquivLike.injective (MulAction.toPerm a))
  exact (hfix_unique xS hgfixS).trans (hfix_unique xT hgfixT).symm

end CFSG.GorensteinWalter

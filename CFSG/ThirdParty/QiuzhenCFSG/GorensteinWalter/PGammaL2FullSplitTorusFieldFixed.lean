module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorus
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Full split-torus subgroups fixed by a field automorphism

The full split torus is parametrized injectively by `Kˣ` using projective
classes of `diag(a, 1)`.  Consequently projective commutation with a pure
field automorphism forces `a` itself into the fixed subfield, with no sign
ambiguity.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u


/-- Every subgroup of the full standard split torus that is projectively
centralized by a pure coefficient automorphism has order dividing the unit
order of the fixed subfield. -/
public theorem pGammaL2_pureField_splitTorus_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (A : Subgroup (PGL2 K))
    (hAtorus : A ≤ (pGammaL2FullSplitTorus K).range)
    (hcomm : ∀ x : PGL2 K, x ∈ A →
      Commute (SemidirectProduct.inr sigma : PGammaL2 K)
        (SemidirectProduct.inl x)) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    Nat.card A ∣ Nat.card R - 1 := by
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  let B : Subgroup Kˣ := A.comap (pGammaL2FullSplitTorus K)
  have hBmap : B.map (pGammaL2FullSplitTorus K) = A := by
    apply le_antisymm
    · exact Subgroup.map_comap_le (pGammaL2FullSplitTorus K) A
    · intro x hx
      rcases hAtorus hx with ⟨a, ha⟩
      exact Subgroup.mem_map.mpr ⟨a, by simpa [B, ha] using hx, ha⟩
  have hBcard : Nat.card B = Nat.card A := by
    rw [← hBmap]
    exact (Subgroup.card_map_of_injective (K := B)
      (pGammaL2FullSplitTorus_injective K)).symm
  have hfixed : ∀ a : Kˣ, a ∈ B → Units.map sigma.toRingHom a = a := by
    intro a ha
    apply pGammaL2FullSplitTorus_fixed K sigma a
    apply hcomm (pGammaL2FullSplitTorus K a)
    exact ha
  let f : B →* Rˣ :=
    { toFun := fun a => Units.mk0
        (⟨((a : Kˣ) : K), by
          change ((a : Kˣ) : K) ∈
            MulAction.fixedPoints (Subgroup.zpowers sigma) K
          rw [MulAction.mem_fixedPoints]
          intro tau
          rcases Subgroup.mem_zpowers_iff.mp tau.2 with ⟨z, hz⟩
          have haFix : ((a : Kˣ) : K) ∈ MulAction.fixedBy K sigma := by
            change sigma ((a : Kˣ) : K) = ((a : Kˣ) : K)
            exact congrArg (fun x : Kˣ => (x : K))
              (hfixed (a : Kˣ) a.2)
          change (tau : K ≃+* K) ((a : Kˣ) : K) = ((a : Kˣ) : K)
          rw [← hz]
          exact MulAction.mem_fixedBy_zpow haFix z⟩)
        (by
          intro ha0
          apply (a : Kˣ).ne_zero
          exact congrArg (fun x : R => (x : K)) ha0)
      map_one' := by
        apply Units.ext
        rfl
      map_mul' := by
        intro a b
        apply Units.ext
        rfl }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun x : Rˣ => ((x : R) : K)) hab
  have hdvd : Nat.card B ∣ Nat.card Rˣ :=
    Subgroup.card_dvd_of_injective f hfinj
  rw [hBcard] at hdvd
  simpa [Nat.card_units] using hdvd

end CFSG.GorensteinWalter

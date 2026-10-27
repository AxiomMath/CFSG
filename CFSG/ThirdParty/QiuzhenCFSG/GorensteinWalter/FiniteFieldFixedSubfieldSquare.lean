module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Square classes in an odd-prime fixed-field extension

A quadratic subextension cannot lie inside an extension of odd prime degree.
Hence an element of the fixed subfield is a square upstairs exactly when it
is already a square downstairs.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Polynomial

universe u

private theorem nonsquare_remains_nonsquare_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (lam : K)
    (hlamFixed : lam ∈ FixedPoints.subfield (Subgroup.zpowers sigma) K)
    (hlamNS : ¬ IsSquare (⟨lam, hlamFixed⟩ :
      FixedPoints.subfield (Subgroup.zpowers sigma) K)) :
    ¬ IsSquare lam := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  intro hlamK
  rcases hlamK with ⟨x, hx⟩
  have hx2 : x * x = lam := hx.symm
  let lamR : R := ⟨lam, hlamFixed⟩
  have haeval : Polynomial.aeval x (X ^ 2 - C lamR) = 0 := by
    calc
      Polynomial.aeval x (X ^ 2 - C lamR) = x ^ 2 - (lamR : K) := by
        simp [pow_two, Subfield.algebraMap_ofSubfield]
      _ = x ^ 2 - lam := by simp [lamR]
      _ = 0 := by rw [pow_two, ← hx2]; simp
  have hminpoly_dvd : minpoly R x ∣ X ^ 2 - C lamR :=
    minpoly.dvd R x haeval
  have hxint : IsIntegral R x := by
    refine ⟨X ^ 2 - C lamR, monic_X_pow_sub_C lamR (by norm_num), haeval⟩
  have hdeg : (minpoly R x).natDegree ≤ 2 := by
    calc
      (minpoly R x).natDegree ≤ (X ^ 2 - C lamR).natDegree :=
        natDegree_le_of_dvd hminpoly_dvd
          (X_pow_sub_C_ne_zero (by norm_num) lamR)
      _ = 2 := by rw [natDegree_X_pow_sub_C]
  have hfinrank_adjoin :
      Module.finrank R (IntermediateField.adjoin R {x}) =
        (minpoly R x).natDegree :=
    IntermediateField.adjoin.finrank hxint
  have hle2 : Module.finrank R (IntermediateField.adjoin R {x}) ≤ 2 := by
    rw [hfinrank_adjoin]
    exact hdeg
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  let : IsGaloisGroup (Subgroup.zpowers sigma) R K :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers sigma) K
  have hfinrankK : Module.finrank R K = p := by
    calc
      Module.finrank R K = Nat.card (Subgroup.zpowers sigma) := by
        symm
        dsimp [R]
        exact IsGaloisGroup.card_eq_finrank
          (Subgroup.zpowers sigma)
          (FixedPoints.subfield (Subgroup.zpowers sigma) K) K
      _ = orderOf sigma := Nat.card_zpowers sigma
      _ = p := hord
  have hdiv : Module.finrank R (IntermediateField.adjoin R {x}) ∣ p := by
    rw [← hfinrankK]
    have htower : Module.finrank R (IntermediateField.adjoin R {x}) *
          Module.finrank (IntermediateField.adjoin R {x}) K =
        Module.finrank R K :=
      Module.finrank_mul_finrank R (IntermediateField.adjoin R {x}) K
    rw [← htower]
    exact dvd_mul_right _ _
  have hpge3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    have hpne2 : p ≠ 2 := by
      intro hp2eq
      have hdiv2 : 2 ∣ p := by simp [hp2eq]
      exact hpodd.not_two_dvd_nat hdiv2
    omega
  have hlt : Module.finrank R (IntermediateField.adjoin R {x}) < p := by
    omega
  have hfin1 : Module.finrank R (IntermediateField.adjoin R {x}) = 1 :=
    ((Nat.dvd_prime hp).mp hdiv).resolve_right (ne_of_lt hlt)
  have hxbot : x ∈ (⊥ : IntermediateField R K) :=
    (IntermediateField.finrank_adjoin_simple_eq_one_iff
      (F := R) (E := K) (α := x)).mp hfin1
  rcases IntermediateField.mem_bot.mp hxbot with ⟨r, hr⟩
  have hlam_eq : lam = ((r * r : R) : K) := by
    calc
      lam = x * x := hx
      _ = (r : K) * (r : K) := by
        rw [← hr]
        simp [Subfield.algebraMap_ofSubfield]
      _ = ((r * r : R) : K) := by simp
  have hsq : IsSquare (⟨lam, hlamFixed⟩ : R) := by
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hlam_eq
  exact hlamNS hsq

/-- In the fixed field of an odd prime-order automorphism, the inclusion into
`K` reflects square classes. -/
public theorem fixedSubfield_isSquare_iff
    (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (x : FixedPoints.subfield (Subgroup.zpowers sigma) K) :
    IsSquare (x : K) ↔ IsSquare x := by
  constructor
  · intro hxK
    by_contra hxR
    exact nonsquare_remains_nonsquare_fixedSubfield K sigma p hp hpodd hord
      (x : K) x.2 hxR hxK
  · rintro ⟨y, hy⟩
    refine ⟨(y : K), ?_⟩
    exact congrArg (fun z : FixedPoints.subfield (Subgroup.zpowers sigma) K =>
      (z : K)) hy

end CFSG.GorensteinWalter

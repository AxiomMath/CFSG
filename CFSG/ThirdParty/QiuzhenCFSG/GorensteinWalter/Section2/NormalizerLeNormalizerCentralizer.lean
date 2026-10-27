module

public import Mathlib.GroupTheory.Commutator.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Normalizers act on centralizers

Conjugation by an element normalizing a subgroup preserves that subgroup's
centralizer.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The normalizer of `R` is contained in the normalizer of `C_G(R)`. -/
public theorem normalizer_le_normalizer_centralizer_subgroup
    {G : Type u} [Group G] (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hrn : n⁻¹ * r * n ∈ R := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (R : Set G)).inv_mem hn) _).1 hr
    have hcomm : (n⁻¹ * r * n) * c = c * (n⁻¹ * r * n) := hc _ hrn
    have hcomm' := congrArg (fun x : G => n * x * n⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hrn : n * r * n⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hn _).1 hr
    have hcomm :
        (n * r * n⁻¹) * (n * c * n⁻¹) =
          (n * c * n⁻¹) * (n * r * n⁻¹) :=
      hc _ hrn
    have hcomm' := congrArg (fun x : G => n⁻¹ * x * n) hcomm
    simpa [mul_assoc] using hcomm'

end CFSG.GorensteinWalter

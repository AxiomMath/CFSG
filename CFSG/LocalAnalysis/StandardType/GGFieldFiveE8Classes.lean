module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmCent

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

abbrev E8Two : Type := ↥(adjointGroup .E8 (GaloisField 2 1))

@[expose] def IsFiveB {H : Type} [Group H] (y : H) (K₀ : Subgroup H) : Prop :=
  IsComponentOf K₀ (Subgroup.centralizer {y}) ∧
    (∀ c ∈ Subgroup.centralizer {y}, ∃ n : ℤ, y ^ n * c ∈ K₀) ∧
    Subgroup.center K₀ = ⊥ ∧ 5 ∣ Nat.card K₀ ∧ OmNonsplit.OmModel (GaloisField 2 1) K₀

@[expose] def E8TwoFiveCentInput : Prop :=
  ∀ a : E8Two, orderOf a = 5 →
    (∃ K₀ : Subgroup E8Two, IsFiveB a K₀) ∨ IsQuasisimple ↥(Subgroup.centralizer {a})

@[expose] def E8TwoFivePlaneCentInput : Prop :=
  ∀ A : Subgroup E8Two, IsElemAbelian 5 A → Nat.card A = 5 ^ 2 →
    (∀ y ∈ A, y ≠ 1 → IsQuasisimple ↥(Subgroup.centralizer {y})) →
    IsMulCommutative ↥(Subgroup.centralizer (A : Set E8Two))

theorem exists_isFiveB_of_noncomm_centralizer_plane (h5 : E8TwoFiveCentInput)
    (hpl : E8TwoFivePlaneCentInput) (A : Subgroup E8Two) (hA : IsElemAbelian 5 A)
    (hcard : Nat.card A = 5 ^ 2)
    (hnc : ¬ IsMulCommutative ↥(Subgroup.centralizer (A : Set E8Two))) :
    ∃ y ∈ A, y ≠ 1 ∧ ∃ K₀ : Subgroup E8Two, IsFiveB y K₀ := by
  by_contra h
  push Not at h
  refine hnc (hpl A hA hcard fun y hy hy1 => ?_)
  have hy5 : orderOf y = 5 := by
    have hpow : y ^ 5 = 1 := hA.2 y hy
    rcases (Nat.dvd_prime Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hpow) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hy1
    · exact h1
  exact (h5 y hy5).resolve_left fun ⟨K₀, hK₀⟩ => h y hy hy1 K₀ hK₀

end FieldFiveE8

end CFSG.StandardType

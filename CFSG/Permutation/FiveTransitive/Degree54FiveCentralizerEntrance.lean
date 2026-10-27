module

public import CFSG.Permutation.FiveTransitive.CyclicNormalizerAlternating
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveCentralizerEntrance

open MulAction FixedNormalizerAction

private theorem exists_centralizing_lift
    {G F : Type*} [Group G] [Fintype F] [DecidableEq F]
    (Q : Subgroup G) (hQ : IsCyclic Q) (hF : 5 ≤ Nat.card F)
    (f : Normalizer Q →* Equiv.Perm F) (hAlt : alternatingGroup F ≤ f.range)
    (u : alternatingGroup F) :
    ∃ a : Normalizer Q, a.val ∈ Subgroup.centralizer (Q : Set G) ∧ f a = u.val := by
  let _ := hQ
  have hperfect : ⁅alternatingGroup F, alternatingGroup F⁆ = alternatingGroup F := by
    apply Subgroup.isPerfect_iff.mp
    rw [Group.isPerfect_def]
    exact commutator_alternatingGroup_eq_top hF
  have hle : alternatingGroup F ≤ (commutator (Normalizer Q)).map f := by
    rw [map_commutator_eq]
    rw [← hperfect]
    exact Subgroup.commutator_mono hAlt hAlt
  obtain ⟨a, ha, hfa⟩ := hle u.property
  exact ⟨a, CyclicNormalizerAlternating.commutator_le_centralizer Q ha, hfa⟩

theorem exists_subgroup
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] [DecidableEq (Fixed (X := X) Q)]
    (hQcard : Nat.card Q = 5) (hF : Nat.card (Fixed (X := X) Q) = 9)
    (hAlt : alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q) :
    ∃ K : Subgroup (Normalizer Q), ∃ rho : K →* alternatingGroup (Fixed (X := X) Q),
      Function.Surjective rho ∧
      (∀ k : K, ∀ q : Q, Commute k.val.val q.val) ∧
      (∀ k : K, (rho k).val = toPermHom (Normalizer Q) (Fixed (X := X) Q) k.val) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcyclic : IsCyclic Q := isCyclic_of_prime_card hQcard
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let C := (Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)
  let K : Subgroup (Normalizer Q) := C ⊓ (alternatingGroup (Fixed (X := X) Q)).comap f
  let rho : K →* alternatingGroup (Fixed (X := X) Q) :=
    (f.comp K.subtype).codRestrict _ (fun k => k.property.2)
  refine ⟨K, rho, ?_, ?_, fun _ => rfl⟩
  · intro u
    obtain ⟨a, ha, hfa⟩ := exists_centralizing_lift Q hcyclic (by omega) f hAlt u
    have haK : a ∈ K := ⟨ha, by change f a ∈ alternatingGroup _; rw [hfa]; exact u.property⟩
    exact ⟨⟨a, haK⟩, Subtype.ext hfa⟩
  · intro k q
    exact (Subgroup.mem_centralizer_iff.mp k.property.1 q.val q.property).symm

end FiveTransitive.Degree54FiveCentralizerEntrance

end CFSG

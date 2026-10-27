module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggE6TwoTwoLocalFour_holds :
    ∀ (H : Type) [Group H] [Finite H] [Group.IsPerfect H],
      GGHasLabel ⟨.E6, 0, 1⟩ (H ⧸ Subgroup.center H) →
      ∃ F U : Subgroup H, IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 4 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        F ≤ Subgroup.normalizer (U : Set H) := by
  intro H _ _ hperf hlab
  obtain ⟨K, hKfield, hKfinite, hKcard, hiso⟩ := hlab
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  obtain ⟨iso⟩ := hiso
  have hchar : CharP K 2 := charP_two_of_card hKcard
  haveI : CharP K 2 := hchar
  have hperf' : commutator H = ⊤ := Group.IsPerfect.commutator_eq_top
  let ψ := iso.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hsurj : Function.Surjective ψ :=
    iso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center H := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have h1 : iso (QuotientGroup.mk h) = 1 := hh
    exact (QuotientGroup.eq_one_iff h).mp (iso.map_eq_one_iff.mp h1)
  obtain ⟨U, E, hUne, hU2, hE, hEab, hEcard, -⟩ :=
    TableBExc.E6Three.ggTorusLift_E6_two (L' := H) ψ hsurj hker hperf'
  exact ⟨E, U, hEab, hEcard, hUne, hU2, hE⟩

end CFSG.StandardType

end

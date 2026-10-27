module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggCRN_twoLocalRank_of_lift {lab : LargeEvenLabel}
    (hall : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 9 R)
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (hlab : GGHasLabel lab (H ⧸ Subgroup.center H)) : 9 ≤ LargeEvenTwoLocalRank 3 H := by
  have hmain := hall (fun R _ _ _ => Nonempty ((H ⧸ Subgroup.center H) ≃* R)) hlab
  obtain ⟨R, _, I, F, hQe, hP⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨e⟩ := hQe
  let ψ : H →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center H))
  have hsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change e (QuotientGroup.mk' (Subgroup.center H) x) = 1 at hx
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard, -⟩ :=
    hP H ψ hsurj hker (Group.isPerfect_def.mp inferInstance)
  exact le_twoLocalRank_of_normalizes Nat.prime_three hU hU2 hE hEU hcard

end CFSG.StandardType

end

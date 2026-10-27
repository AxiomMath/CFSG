module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggCentreTwo_of_label (hZ : GGCentreTwoKnown) {lab : LargeEvenLabel}
    (hlab2 : LargeEvenInLambda2 lab)
    (htag : ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank) ∨ lab.tag = .F4)
    {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (hlab : GGHasLabel lab (Y ⧸ Subgroup.center Y)) :
    ∀ g ∈ Subgroup.center Y, ∃ k : ℕ, orderOf g = 2 ^ k := by
  have hAll := hZ lab hlab2 htag
  have hmain := hAll (fun R _ _ _ => Nonempty ((Y ⧸ Subgroup.center Y) ≃* R)) hlab
  obtain ⟨R, _, I, F, hQe, hP⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨e⟩ := hQe
  let ψ : Y →* R := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Y) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hP Y ψ hsurj hker.le hperf

end CFSG.StandardType

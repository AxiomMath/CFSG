module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalSect
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LargeExtraspecial.S12TriG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.AGLEmbedding.A15Local.Sect (SectionsOrder60)

theorem isAlt_five_of_sectionsOrder60 {Y S : Type} [Group Y] [Finite Y]
    [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤)
    (h60 : CFSG.AGLEmbedding.A15Local.Sect.SectionsOrder60 Y)
    (f : Y →* S) (hf : Function.Surjective f) : IsAlt S 5 := by
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hperf
  haveI : Group.IsPerfect S := Group.IsPerfect.ofSurjective (f := f) hf
  have hna : ∃ a b : S, a * b ≠ b * a := by
    by_contra h
    have hcomm : ∀ a b : S, a * b = b * a := fun a b =>
      not_not.mp fun hab => h ⟨a, b, hab⟩
    exact Group.IsPerfect.not_isSolvable S (IsSimpleGroup.comm_iff_isSolvable.1 hcomm)
  have hcard : Nat.card S = 60 :=
    h60 Y S (MonoidHom.id Y) Function.injective_id inferInstance hna f hf
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22

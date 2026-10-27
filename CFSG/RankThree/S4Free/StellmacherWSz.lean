module

import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
public import CFSG.RankThree.S4Free.StellmacherStatement

public section

universe u v

namespace CFSG.RankThree.S4Free

open Subgroup

variable (S : Type u) [Group S]

@[expose] def hostNormalSubgroupsSz : Set (Subgroup S) :=
  {U | ∀ (X : Type v) [Group X] (ι : S →* X), IsAdmissibleHost ι → SzSections X →
    (U.map ι).Normal}

@[expose] def stellmacherWSz : Subgroup S :=
  sSup (hostNormalSubgroupsSz.{u, v} S)

variable {S}

theorem stellmacherWSz_normal {X : Type v} [Group X] {ι : S →* X} (h : IsAdmissibleHost ι)
    (hX : SzSections X) : ((stellmacherWSz.{u, v} S).map ι).Normal := by
  rw [stellmacherWSz, (gc_map_comap ι).l_sSup, ← sSup_image]
  refine Subgroup.sSup_normal _ ?_
  rintro _ ⟨U, hU, rfl⟩
  exact hU X ι h hX

theorem le_stellmacherWSz {U : Subgroup S}
    (hU : ∀ (X : Type v) [Group X] (ι : S →* X), IsAdmissibleHost ι → SzSections X →
      (U.map ι).Normal) :
    U ≤ stellmacherWSz.{u, v} S :=
  le_sSup hU

theorem map_stellmacherWSz_le (α : S ≃* S) :
    (stellmacherWSz.{u, v} S).map α.toMonoidHom ≤ stellmacherWSz.{u, v} S := by
  refine le_stellmacherWSz fun X _ ι h hX => ?_
  rw [Subgroup.map_map]
  exact stellmacherWSz_normal (h.comp_mulEquiv α) hX

theorem stellmacherWSz_characteristic : (stellmacherWSz.{u, v} S).Characteristic :=
  characteristic_iff_map_le.2 fun α => map_stellmacherWSz_le α

theorem stellmacherClauseSz_iff :
    StellmacherClauseSz.{u, v} S ↔ stellmacherWSz.{u, v} S ≠ ⊥ := by
  refine ⟨fun ⟨W, _, hne, hnormal⟩ hbot => hne ?_, fun hne => ?_⟩
  · exact eq_bot_iff.2 (hbot ▸ le_stellmacherWSz hnormal)
  · exact ⟨_, stellmacherWSz_characteristic, hne, fun X _ ι hι hX => stellmacherWSz_normal hι hX⟩

open CFSG.Assembly in
theorem szSections_of_kProper (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {G : Type} [Group G]
    [Finite G] (hK : KProper InCatalog G) (h3 : 3 ∣ Nat.card G) {U : Subgroup G}
    (hU3 : ¬ 3 ∣ Nat.card U) : SzSections ↥U := by
  intro H K _ hsimple hnab
  have hUtop : U ≠ ⊤ := by
    rintro rfl
    exact hU3 (by rwa [Subgroup.card_top])
  haveI := hsimple
  have hcat : InCatalog (↥H ⧸ K) :=
    CFSG.ComponentClassification.CatalogueKProper.simple_section_of_surjective G hK U hUtop ↥U
      (MonoidHom.id ↥U) Function.surjective_id H (↥H ⧸ K) hnab (QuotientGroup.mk' K)
      (QuotientGroup.mk'_surjective K)
  have h3E : ¬ 3 ∣ Nat.card (↥H ⧸ K) := fun h =>
    hU3 (h.trans ((Subgroup.card_quotient_dvd_card K).trans (Subgroup.card_subgroup_dvd_card H)))
  obtain ⟨f, -, a, ha, F, _, _, rfl, hF, he⟩ := hSz (↥H ⧸ K) hnab hcat h3E
  exact ⟨a, ha, F, inferInstance, inferInstance, hF, he⟩

end CFSG.RankThree.S4Free

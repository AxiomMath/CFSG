module

public import CFSG.Quasithin.Background.Harris.Interfaces
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.ComponentList
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CentralizerOdd
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.SzG11SectionSQT
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris CFSG.SectionRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.mpr h.1, h.2, exists_noncomm_quotient_center h⟩

theorem odd_card_center_of_irr [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  have hodd := OrdinaryProofs.centralizer_card_odd hL
  have hle : (Subgroup.center ↥L).map L.subtype ≤ Subgroup.centralizer (L : Set (GLV V)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    simpa using this
  have hdvd : Nat.card ((Subgroup.center ↥L).map L.subtype) ∣
      Nat.card (Subgroup.centralizer (L : Set (GLV V))) := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective L.subtype_injective] at hdvd
  exact hodd.of_dvd_nat hdvd

theorem isSQTKCat_of_component
    [Finite V] {Γ L : Subgroup (GLV V)} (hq : IsQuotientOfSQTKTauCeti ↥Γ)
    (hL : IsComponentOf L Γ) : IsSQTKCat ↥L := by
  have : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) DFunLike.coe_injective
  have hQ := isQuasisimple_of_open hL.2.2
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := hq.of_le hL.1
  have hS : IsSQTKCat S := ⟨G11.isStronglyQuasithin_of_tc hst, hkg⟩
  have hsurj : Function.Surjective (φ.comp (⊤ : Subgroup S).subtype) := by
    intro y
    obtain ⟨s, hs⟩ := hφ y
    exact ⟨⟨s, Subgroup.mem_top s⟩, hs⟩
  exact (CFSG.QuasithinUnique.Setup.Layer.sqtk_two_power_index oddKernelCentralization catalogStepHyp hS ⊤
    (φ.comp (⊤ : Subgroup S).subtype) hsurj ⊤ (SzG11.layer_top_of_isQuasisimple hQ)
    (fun g => ⟨0, by
      have : Subsingleton (↥L ⧸ (⊤ : Subgroup ↥L)) := QuotientGroup.subsingleton_quotient_top
      simp [Subsingleton.elim g 1]⟩)).1

theorem descentOne_of_threeCover
    (hT : ThreeCoverFact) : DescentOne := by
  intro V _ _ _ Γ A L m h
  have : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) DFunLike.coe_injective
  have hQ : CFSG.IsQuasisimple ↥L := isQuasisimple_of_open h.L_comp.2.2
  have hSQTK : IsSQTKCat ↥L := isSQTKCat_of_component h.quotient h.L_comp
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := odd_card_center_of_irr h.H_irr
  have hSQTK' : SQTKGroup ↥L :=
    ⟨G11.tc_of_isStronglyQuasithin hSQTK.1, hSQTK.2⟩
  have hZ13 := catalogStepFact ↥L hQ hSQTK' hodd
  have hlist : A23List (↥L ⧸ Subgroup.center ↥L) := sqtkSimpleList_of_component h.quotient h.L_comp
  rcases hZ13 with h1 | h3
  · refine Or.inl ?_
    have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
    have := hQ.2.1
    exact ⟨e.symm.isSimpleGroup, CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e.symm hlist⟩
  · exact Or.inr ⟨h3, hT ↥L hQ h3 hlist⟩

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

module

public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Milestones CFSG.SectionRank
open scoped commutatorElement

theorem exists_noncomm_quotient_center {L : Type*} [Group L] (hL : CFSG.Open.IsQuasisimple L) :
    ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hperf, hsimple⟩ := hL
  have hle : commutator L ≤ Subgroup.center L := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    rw [show (QuotientGroup.mk ⁅g₁, g₂⁆ : L ⧸ Subgroup.center L) =
        ⁅(QuotientGroup.mk g₁ : L ⧸ Subgroup.center L), QuotientGroup.mk g₂⁆ from rfl]
    exact (commutatorElement_eq_one_iff_mul_comm).2 (hcon _ _)
  rw [hperf, top_le_iff] at hle
  have hone : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hle]; exact QuotientGroup.subsingleton_quotient_top
  exact (hsimple.toNontrivial.exists_pair_ne.elim fun x hx => hx.elim fun y hy =>
    hy (Subsingleton.elim x y))

theorem sqtkSimpleList_of_quotient
    {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnonab : ∃ a b : Y, a * b ≠ b * a) (h : IsQuotientOfSQTKTauCeti Y) :
    SQTKSimpleList Y := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h
  have hS : IsSQTKCat S := ⟨G11.isStronglyQuasithin_of_tc hst, hkg⟩
  let N : Subgroup (⊤ : Subgroup S) := (φ.comp (⊤ : Subgroup S).subtype).ker
  have hsurj : Function.Surjective (φ.comp (⊤ : Subgroup S).subtype) := by
    intro y
    obtain ⟨s, hs⟩ := hφ y
    exact ⟨⟨s, Subgroup.mem_top s⟩, hs⟩
  let e : ((⊤ : Subgroup S) ⧸ N) ≃* Y := QuotientGroup.quotientKerEquivOfSurjective _ hsurj
  have : IsSimpleGroup ((⊤ : Subgroup S) ⧸ N) := e.isSimpleGroup
  have hnonab' : ∃ a b : (⊤ : Subgroup S) ⧸ N, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hlist := cl_lit_sqtk_simple_list_section S hS (⊤ : Subgroup S) N hnonab'
  exact CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e.symm hlist

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem sqtkSimpleList_of_component
    [Finite V] {Γ L : Subgroup (GLV V)} (hq : IsQuotientOfSQTKTauCeti ↥Γ)
    (hL : IsComponentOf L Γ) : SQTKSimpleList (↥L ⧸ Subgroup.center ↥L) := by
  have : Finite (GLV V) :=
    Finite.of_injective (fun f : GLV V => (f : V → V)) DFunLike.coe_injective
  have hqL : IsQuotientOfSQTKTauCeti ↥L := hq.of_le hL.1
  have hYq : IsQuotientOfSQTKTauCeti (↥L ⧸ Subgroup.center ↥L) :=
    hqL.of_surjective (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  exact sqtkSimpleList_of_quotient (hnonab := exists_noncomm_quotient_center hL.2.2) hYq

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

module

public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.G10FifteenInputs
public import CFSG.Quasithin.Background.G11BridgeSQTK

public section

namespace CFSG.Quasithin

namespace SzG11

open CFSG
open scoped commutatorElement

theorem isQuasisimple_of_simple_nonabelian {Q : Type*} [Group Q] [hs : IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : IsQuasisimple Q := by
  have hc : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hcomm : commutator Q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator Q := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        at hmem
      exact hmem
    · exact h
  refine ⟨Group.isPerfect_def.mpr hcomm, ?_, ?_⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ hs e
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩

theorem layer_top_of_isQuasisimple {Q : Type*} [Group Q] (h : IsQuasisimple Q) :
    layer ↥(⊤ : Subgroup Q) = ⊤ := by
  have h1 : IsQuasisimple ↥(⊤ : Subgroup Q) :=
    LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h
  have h2 : IsQuasisimple ↥(⊤ : Subgroup ↥(⊤ : Subgroup Q)) :=
    LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h1
  exact eq_top_iff.mpr (LocalCores.component_le_layer
    (⟨h2, Subgroup.IsSubnormal.top⟩ : IsComponent (⊤ : Subgroup ↥(⊤ : Subgroup Q))))

theorem sectionSQTInput_of_asA21 (h : AsA21SQTKSection) : G11.SectionSQTInput := by
  intro X _ _ hX H N _ hsimple hnab
  have hq : IsQuasisimple (H ⧸ N) := isQuasisimple_of_simple_nonabelian hnab
  have hX' : SQTKGroup X := ⟨G11.tc_of_isStronglyQuasithin hX.1, hX.2⟩
  have key := h X hX' H (H ⧸ N) (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    (⊤ : Subgroup (H ⧸ N)) (layer_top_of_isQuasisimple hq)
    (by
      have : Subsingleton ((H ⧸ N) ⧸ (⊤ : Subgroup (H ⧸ N))) :=
        QuotientGroup.subsingleton_quotient_top
      exact IsPGroup.of_card (n := 0) (by rw [pow_zero]; exact Nat.card_unique))
  exact G11.isStronglyQuasithin_of_tc key.1

end SzG11

end CFSG.Quasithin

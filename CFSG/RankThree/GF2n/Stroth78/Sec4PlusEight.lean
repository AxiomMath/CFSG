module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusCenter
import CFSG.RankThree.GF2n.Stroth78.Sec3Six
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

@[expose] noncomputable def rhoX (S : Setting z E F) (a : G) :
    ↥(Xsub S a) →* (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
  (Subgroup.subtype _).comp ((rhoBar S).comp (Xsub S a).subtype)

theorem rhoX_apply (S : Setting z E F) (a : G) (x : ↥(Xsub S a)) :
    rhoX S a x =
      (rhoBar S (x : Hbar z) : Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
  rfl

theorem rootClass_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) :
    CFSG.LargeExtraspecial.A2Mod.RootClass ↥(Xsub S a) (Subtype.val ⁻¹' Eset S a) := by
  obtain ⟨hne, hroot, -, hclass⟩ := stroth78_31 S h h217
  obtain ⟨α₀, hα₀⟩ := hne
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, center_Xsub_eq_bot_of_threeFourPlus S h h217 h34, ?_⟩
  · exact Subgroup.closure_closure_coe_preimage
  · refine ⟨⟨α₀, subset_Xsub S a hα₀⟩, hα₀, fun d => ?_⟩
    constructor
    · intro hd
      obtain ⟨c, hc, hcx⟩ := (hclass α₀ hα₀ (d : Hbar z)).1 hd
      exact isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hcx.symm⟩
    · intro hconj
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      have hc' : (d : Hbar z) = (c : Hbar z) * α₀ * (c : Hbar z)⁻¹ := by
        simpa using (congrArg Subtype.val hc).symm
      exact (hclass α₀ hα₀ (d : Hbar z)).2 ⟨c, c.2, hc'⟩
  · intro d hd
    have h2 := hroot.1 (d : Hbar z) hd
    refine ⟨?_, ?_⟩
    · intro h1
      rw [h1] at h2
      simp at h2
    · apply Subtype.ext
      have := pow_orderOf_eq_one (d : Hbar z)
      rw [h2] at this
      simpa [pow_two] using this
  · intro d hd e he
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact orderOf_mul_le_four_of_mem_Eset S a hd he
  · intro d hd e he h4e
    exact hroot.2.2 (d : Hbar z) hd (e : Hbar z) he
      (by rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4e; exact h4e)
  · obtain ⟨α, hα, β, hβ, h4'⟩ := h34
    exact ⟨⟨α, subset_Xsub S a hα⟩, hα, ⟨β, subset_Xsub S a hβ⟩, hβ, by
      rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]; exact h4'⟩
  · intro N hN hp
    exact twoCore_Xsub S N hN hp

theorem a2Action_Xsub (S : Setting z E F) (a : G) :
    CFSG.LargeExtraspecial.A2Mod.A2Action (Subtype.val ⁻¹' Eset S a) (qS S) (rhoX S a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · letI := modAbF S
    exact q_nondegenerate S
  · intro x y hxy
    exact Subtype.ext (rhoBar_injective S (Subtype.ext hxy))
  · intro x v
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S (x : Hbar z)).2) v
  · intro d hd
    exact isTypeA_rhoBar_of_isA2Hbar S (Eset_subset_A2set S a hd)

end CFSG.RankThree.GF2n.Stroth78

module

import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec15.Y4Core

open CFSG CFSG.RankThree CFSG.GH74.GLS

@[expose] def Good3 (S : Type*) [Group S] : Prop :=
  IsQuasisimple S ∧ Subgroup.center S = ⊥ ∧ oPrimeResidual 3 S = ⊤

theorem good3_of_isSimpleGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S) : Good3 S :=
  ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hS).1,
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hS).2,
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup h3⟩

theorem Good3.of_mulEquiv {S S' : Type*} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S ≃* S') (h : Good3 S) : Good3 S' := by
  obtain ⟨hq, hz, h3⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e.symm h3⟩
  rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]

theorem Good3.quot_center {S : Type*} [Group S] [Finite S] (h : Good3 S) :
    Good3 (S ⧸ Subgroup.center S) :=
  Good3.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq h.2.1).trans
    QuotientGroup.quotientBot).symm h

@[expose] def CompOrBot {X : Type*} [Group X] (U : Subgroup X) : Prop :=
  U = ⊥ ∨ IsComponent U ∧ oPrimeResidual 3 ↥U = ⊤

@[expose] def ProdComp (X : Type*) [Group X] : Prop :=
  ∃ U V : Subgroup X, CompOrBot U ∧ CompOrBot V ∧ U ⊔ V = ⊤

theorem CompOrBot.map_mulEquiv {X X' : Type*} [Group X] [Group X'] [Finite X]
    (e : X ≃* X') {U : Subgroup X} (hU : CompOrBot U) : CompOrBot (U.map e.toMonoidHom) := by
  rcases hU with rfl | ⟨hU, hU3⟩
  · exact Or.inl (Subgroup.map_bot _)
  · exact Or.inr ⟨CFSG.LocalCores.isComponent_map_mulEquiv e hU,
      Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv
        (U.equivMapOfInjective e.toMonoidHom e.injective).symm hU3⟩

theorem ProdComp.of_mulEquiv {X X' : Type*} [Group X] [Group X'] [Finite X] (e : X ≃* X')
    (h : ProdComp X) : ProdComp X' := by
  obtain ⟨U, V, hU, hV, hsup⟩ := h
  refine ⟨U.map e.toMonoidHom, V.map e.toMonoidHom, hU.map_mulEquiv e, hV.map_mulEquiv e, ?_⟩
  rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]

theorem ProdComp.of_isQuasisimple {X : Type*} [Group X] [Finite X] (hq : IsQuasisimple X)
    (h3 : oPrimeResidual 3 X = ⊤) : ProdComp X :=
  ⟨⊤, ⊥, Or.inr ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩,
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv Subgroup.topEquiv h3⟩,
    Or.inl rfl, sup_bot_eq ⊤⟩

theorem ProdComp.of_good3 {X : Type*} [Group X] [Finite X] (h : Good3 X) : ProdComp X :=
  ProdComp.of_isQuasisimple h.1 h.2.2

theorem ProdComp.prod {S₁ S₂ : Type*} [Group S₁] [Group S₂] [Finite S₁] [Finite S₂]
    (h₁ : Good3 S₁) (h₂ : Good3 S₂) : ProdComp (S₁ × S₂) := by
  set U := (MonoidHom.inl S₁ S₂).range with hU
  set V := (MonoidHom.inr S₁ S₂).range with hV
  have e₁ : S₁ ≃* ↥U := MonoidHom.ofInjective (f := MonoidHom.inl S₁ S₂)
    fun a b h => by simpa using congrArg Prod.fst h
  have e₂ : S₂ ≃* ↥V := MonoidHom.ofInjective (f := MonoidHom.inr S₁ S₂)
    fun a b h => by simpa using congrArg Prod.snd h
  have hUn : U.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨a, rfl⟩ := hx
    exact ⟨g.1 * a * g.1⁻¹, by ext <;> simp⟩
  have hVn : V.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨b, rfl⟩ := hx
    exact ⟨g.2 * b * g.2⁻¹, by ext <;> simp⟩
  refine ⟨U, V, Or.inr ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁ h₁.1, hUn.isSubnormal⟩,
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e₁.symm h₁.2.2⟩,
    Or.inr ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e₂ h₂.1, hVn.isSubnormal⟩,
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e₂.symm h₂.2.2⟩, ?_⟩
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = (x.1, 1) * (1, x.2) := by ext <;> simp
  rw [hx]
  exact mul_mem (Subgroup.mem_sup_left ⟨x.1, rfl⟩) (Subgroup.mem_sup_right ⟨x.2, rfl⟩)

theorem good_commutator {W : Type*} [Group W] [Finite W] (h : Good3 (W ⧸ Subgroup.center W)) :
    IsQuasisimple (commutator W) ∧ oPrimeResidual 3 (commutator W) = ⊤ := by
  have hq : IsQuasisimple (commutator W) :=
    CFSG.LocalCores.quasisimple_central_extension_derived (Subgroup.center W) le_rfl h.1
  refine ⟨hq, ?_⟩
  obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived (Subgroup.center W) le_rfl
    h.1.1
  set f := (QuotientGroup.mk' (Subgroup.center W)).comp (commutator W).subtype with hf
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (Sec17.Proof171Steps.oPrimeResidual_three_normal' (X := commutator W)) with htop | hcen
  · exact htop
  · exfalso
    have hmap := Sec17.Proof171Steps.map_oPrimeResidual_three f hsurj
    rw [h.2.2] at hmap
    have hle : (⊤ : Subgroup (W ⧸ Subgroup.center W)) ≤ ⊥ := by
      rw [← hmap, ← h.2.1]
      exact (Subgroup.map_mono hcen).trans (Subgroup.map_center_le_center hsurj)
    have : Nontrivial (W ⧸ Subgroup.center W) := CFSG.LocalCores.isQuasisimple_nontrivial h.1
    exact bot_ne_top (le_bot_iff.mp hle).symm

theorem ProdComp.of_central {X : Type*} [Group X] [Finite X] (hX : Group.IsPerfect X)
    {U V : Subgroup X} [U.Normal] [V.Normal] (hsup : U ⊔ V = ⊤) (hcomm : ⁅U, V⁆ = ⊥)
    (hU : Good3 (↥U ⧸ Subgroup.center ↥U)) (hV : Good3 (↥V ⧸ Subgroup.center ↥V)) :
    ProdComp X := by
  have key : ∀ (W : Subgroup X) [W.Normal], Good3 (↥W ⧸ Subgroup.center ↥W) →
      CompOrBot ⁅W, W⁆ := by
    intro W _ hW
    obtain ⟨hq, h3⟩ := good_commutator hW
    have hmap : (commutator ↥W).map W.subtype = ⁅W, W⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have e : commutator ↥W ≃* ↥⁅W, W⁆ :=
      ((commutator ↥W).equivMapOfInjective W.subtype W.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)
    have : (⁅W, W⁆ : Subgroup X).Normal := Subgroup.commutator_normal W W
    exact Or.inr ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, this.isSubnormal⟩,
      Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e.symm h3⟩
  refine ⟨⁅U, U⁆, ⁅V, V⁆, key U hU, key V hV, ?_⟩
  have hUV : (U ⊔ V).Normal := Subgroup.sup_normal U V
  have htop : ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤ := hX.commutator_eq_top
  rw [← htop, ← hsup, Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
    Subgroup.commutator_sup_left, hcomm, Subgroup.commutator_comm V U, hcomm, sup_bot_eq,
    bot_sup_eq]

theorem ProdComp.read {Q : Type*} [Group Q] [Finite Q] {D : Subgroup Q} (hD : D.IsSubnormal)
    (h : ProdComp ↥D) : ∃ U V : Subgroup Q, CompOrBot U ∧ CompOrBot V ∧ D ≤ U ⊔ V := by
  obtain ⟨U, V, hU, hV, hsup⟩ := h
  have key : ∀ W : Subgroup ↥D, CompOrBot W → CompOrBot (W.map D.subtype) := by
    rintro W (rfl | ⟨hW, hW3⟩)
    · exact Or.inl (Subgroup.map_bot _)
    · have e := W.equivMapOfInjective D.subtype D.subtype_injective
      exact Or.inr ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hW.1, hW.2.trans' hD⟩,
        Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv e.symm hW3⟩
  refine ⟨U.map D.subtype, V.map D.subtype, key U hU, key V hV, ?_⟩
  rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem isQuasisimple_of_isTripleCover {X S : Type*} [Group X] [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (hX : Group.IsPerfect X) (h : Sec4.IsTripleCover X S) :
    IsQuasisimple X := by
  obtain ⟨-, ⟨φ⟩⟩ := h
  obtain ⟨a, b, hab⟩ := hS
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := φ.isSimpleGroup
  refine ⟨hX, this, φ.symm a, φ.symm b, fun h' => hab (φ.symm.injective ?_)⟩
  rw [map_mul, map_mul, h']

theorem Good3.of_isTripleCover {X S : Type*} [Group X] [Group S] [Finite X] [Finite S]
    (h : Good3 S) (hX : Sec4.IsTripleCover X S) : Good3 (X ⧸ Subgroup.center X) := by
  obtain ⟨-, ⟨φ⟩⟩ := hX
  exact Good3.of_mulEquiv φ.symm h

end CFSG.RankThree.PartTwo.Sec15.Y4Core

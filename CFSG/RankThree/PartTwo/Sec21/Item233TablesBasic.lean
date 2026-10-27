module

public import CFSG.RankThree.PartTwo.Sec21.Item233Pieces
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def OrderThreeAt (I A B : Subgroup G) : Prop :=
  ((∀ a ∈ A, ∃ y ∈ layerCent I B,
      y⁻¹ * a ∈ Subgroup.centralizer (layerCent I B : Set G)) ∨
    Nonempty (layerCent I B ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) ∧
  ∃ B₁ B₂ : Subgroup G, B₁ ≤ A ∧ Nat.card B₁ = 3 ∧ B₁ ≤ layerCent I B ⊔ B ∧
    B₂ ≤ A ∧ Nat.card B₂ = 3 ∧ B₂ ≤ layerCent I B₁ ⊔ B₁ ∧ A ≤ layerCent I B₂ ⊔ B₂

theorem terminalOrderThree_iff : TerminalOrderThree ↔
    ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
      ((Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
        (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
        (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3)) →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 → OrderThreeAt I A B :=
  Iff.rfl

section Transport

variable {G' : Type} [Group G']

theorem map_layerCent (φ : G ≃* G') (I B : Subgroup G) :
    (layerCent I B).map φ.toMonoidHom = layerCent (I.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  rw [layerCent, layerCent, map_inSubgroup_layer, Subgroup.map_inf_eq _ _ _ φ.injective,
    map_centralizer_mulEquiv, Subgroup.coe_map]
  rfl

theorem map_centralizer_subgroup (φ : G ≃* G') (Y : Subgroup G) :
    (Subgroup.centralizer (Y : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((Y.map φ.toMonoidHom : Subgroup G') : Set G') := by
  rw [map_centralizer_mulEquiv, Subgroup.coe_map]
  rfl

theorem OrderThreeAt.map (φ : G ≃* G') {I A B : Subgroup G} (h : OrderThreeAt I A B) :
    OrderThreeAt (I.map φ.toMonoidHom) (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) := by
  obtain ⟨h1, B₁, B₂, hB₁A, hB₁, hB₁Y, hB₂A, hB₂, hB₂Y, hAY⟩ := h
  have hcard : ∀ X : Subgroup G, Nat.card (X.map φ.toMonoidHom) = Nat.card X :=
    fun X => Subgroup.card_map_of_injective φ.injective
  refine ⟨?_, B₁.map φ.toMonoidHom, B₂.map φ.toMonoidHom, Subgroup.map_mono hB₁A,
    (hcard B₁).trans hB₁, ?_, Subgroup.map_mono hB₂A, (hcard B₂).trans hB₂, ?_, ?_⟩
  · rcases h1 with hin | hSL
    · refine Or.inl ?_
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, hya⟩ := hin a ha
      refine ⟨φ y, ?_, ?_⟩
      · rw [← map_layerCent]
        exact ⟨y, hy, rfl⟩
      · rw [← map_layerCent, ← map_centralizer_subgroup]
        exact ⟨y⁻¹ * a, hya, by simp⟩
    · obtain ⟨e⟩ := hSL
      refine Or.inr ⟨?_⟩
      rw [← map_layerCent]
      exact ((layerCent I B).equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e
  · rw [← map_layerCent, ← Subgroup.map_sup]
    exact Subgroup.map_mono hB₁Y
  · rw [← map_layerCent, ← Subgroup.map_sup]
    exact Subgroup.map_mono hB₂Y
  · rw [← map_layerCent, ← Subgroup.map_sup]
    exact Subgroup.map_mono hAY

end Transport

theorem map_inSubgroup_layer_of_injective {G' : Type} [Group G'] {f : G →* G'}
    (hf : Function.Injective f) (X : Subgroup G) :
    (inSubgroup CFSG.layer X).map f = inSubgroup CFSG.layer (X.map f) := by
  have e1 : (inSubgroup CFSG.layer X).map f =
      ((CFSG.layer X).map (X.equivMapOfInjective f hf).toMonoidHom).map (X.map f).subtype := by
    rw [inSubgroup, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [e1, layer_map_mulEquiv', inSubgroup]

theorem map_layerCent_subgroupOf {I B : Subgroup G} (hBI : B ≤ I) :
    (layerCent (⊤ : Subgroup I) (B.subgroupOf I)).map I.subtype = layerCent I B := by
  rw [layerCent, layerCent, map_inSubgroup_layer_of_injective I.subtype_injective, top_inf_eq]
  congr 1
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp hy) ⟨b, hBI hb⟩ (Subgroup.mem_subgroupOf.mpr hb))
  · rintro ⟨hxI, hx⟩
    refine ⟨⟨x, hxI⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) _ (Subgroup.mem_subgroupOf.mp hb))

theorem OrderThreeAt.of_subgroupOf {I A B : Subgroup G} (hAI : A ≤ I) (hBA : B ≤ A)
    (h : OrderThreeAt (⊤ : Subgroup I) (A.subgroupOf I) (B.subgroupOf I)) :
    OrderThreeAt I A B := by
  have hBI := hBA.trans hAI
  obtain ⟨h1, B₁, B₂, hB₁A, hB₁, hB₁Y, hB₂A, hB₂, hB₂Y, hAY⟩ := h
  have hcard : ∀ X : Subgroup I, Nat.card (X.map I.subtype) = Nat.card X :=
    fun X => Subgroup.card_map_of_injective I.subtype_injective
  have hmapA : (A.subgroupOf I).map I.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAI
  have hmapB : (B.subgroupOf I).map I.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBI
  have hX : ∀ X : Subgroup I, X ≤ A.subgroupOf I → X.map I.subtype ≤ A := fun X hX =>
    hmapA ▸ Subgroup.map_mono hX
  have hsub : ∀ X : Subgroup I, X.map I.subtype ≤ I := fun X => Subgroup.map_subtype_le X
  have hlay : ∀ X : Subgroup I, layerCent (⊤ : Subgroup I) X =
      layerCent (⊤ : Subgroup I) ((X.map I.subtype).subgroupOf I) := by
    intro X
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective I.subtype_injective]
  have hlayY : ∀ X : Subgroup I,
      (layerCent (⊤ : Subgroup I) X).map I.subtype = layerCent I (X.map I.subtype) := by
    intro X
    rw [hlay X]
    exact map_layerCent_subgroupOf (hsub X)
  refine ⟨?_, B₁.map I.subtype, B₂.map I.subtype, hX B₁ hB₁A, (hcard B₁).trans hB₁, ?_,
    hX B₂ hB₂A, (hcard B₂).trans hB₂, ?_, ?_⟩
  · rcases h1 with hin | e
    · refine Or.inl fun a ha => ?_
      obtain ⟨y, hy, hya⟩ := hin ⟨a, hAI ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      refine ⟨y, ?_, ?_⟩
      · rw [← map_layerCent_subgroupOf hBI]
        exact ⟨y, hy, rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [← map_layerCent_subgroupOf hBI] at hz
        obtain ⟨z', hz', rfl⟩ := hz
        have := (Subgroup.mem_centralizer_iff.mp hya) z' hz'
        exact congrArg Subtype.val this
    · obtain ⟨e⟩ := e
      refine Or.inr ⟨?_⟩
      rw [← map_layerCent_subgroupOf hBI]
      exact ((layerCent (⊤ : Subgroup I) (B.subgroupOf I)).equivMapOfInjective I.subtype
        I.subtype_injective).symm.trans e
  · calc B₁.map I.subtype
        ≤ (layerCent (⊤ : Subgroup I) (B.subgroupOf I) ⊔ B.subgroupOf I).map I.subtype :=
          Subgroup.map_mono hB₁Y
      _ = layerCent I B ⊔ B := by rw [Subgroup.map_sup, map_layerCent_subgroupOf hBI, hmapB]
  · rw [← hlayY, ← Subgroup.map_sup]
    exact Subgroup.map_mono hB₂Y
  · rw [← hlayY, ← Subgroup.map_sup, ← hmapA]
    exact Subgroup.map_mono hAY

@[expose] def TerminalOrderThreeU58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    Nonempty (I ≃* projSU 5 2 3) → Nat.card A = 3 ^ 4 →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 → OrderThreeAt I A B

@[expose] def TerminalOrderThreeL44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    Nonempty (I ≃* projSL 4 (GaloisField 2 2)) → Nat.card A = 3 ^ 3 →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 → OrderThreeAt I A B

@[expose] def TerminalOrderThreeSp64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    Nonempty (I ≃* projSp 3 (GaloisField 2 2)) → Nat.card A = 3 ^ 3 →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 → OrderThreeAt I A B

theorem terminalOrderThree_of (hU : TerminalOrderThreeU58) (hL : TerminalOrderThreeL44)
    (hS : TerminalOrderThreeSp64) : TerminalOrderThree := by
  rw [terminalOrderThree_iff]
  intro G _ _ I A hAI hAe hT B hBA hB3
  rcases hT with ⟨he, hA⟩ | ⟨he, hA⟩ | ⟨he, hA⟩
  · exact hU G I A hAI hAe he hA B hBA hB3
  · exact hL G I A hAI hAe he hA B hBA hB3
  · exact hS G I A hAI hAe he hA B hBA hB3

theorem le_inSubgroup_layer_of_normal {C S : Subgroup G} (hSC : S ≤ C)
    (hCS : C ≤ Subgroup.normalizer (S : Set G)) (hS : CFSG.IsQuasisimple S) :
    S ≤ inSubgroup CFSG.layer C := by
  have hn : (S.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSC).mpr hCS
  have hq : CFSG.IsQuasisimple (S.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSC).symm hS
  have hcomp : CFSG.IsComponent (S.subgroupOf C) := ⟨hq, hn.isSubnormal⟩
  have h := Subgroup.map_mono (f := C.subtype) (CFSG.LocalCores.component_le_layer hcomp)
  rwa [Subgroup.map_subgroupOf_eq_of_le hSC] at h

theorem inSubgroup_layer_le_of_commutator_le {C D : Subgroup G} (h : ⁅C, C⁆ ≤ D) :
    inSubgroup CFSG.layer C ≤ D := by
  have h1 : CFSG.layer C ≤ commutator C := by
    rw [← CFSG.LocalCores.layer_perfect, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  calc inSubgroup CFSG.layer C = (CFSG.layer C).map C.subtype := rfl
    _ ≤ (commutator C).map C.subtype := Subgroup.map_mono h1
    _ = ⁅C, C⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
    _ ≤ D := h

end CFSG.RankThree.PartTwo.Sec21

module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralizerPushing
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem card_subgroupOf_of_le {T L : Subgroup G} (h : T ≤ L) :
    Nat.card (T.subgroupOf L) = Nat.card T :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem subgroupOf_eq_bot_iff_of_le {T L : Subgroup G} (h : T ≤ L) :
    T.subgroupOf L = ⊥ ↔ T = ⊥ := by
  constructor
  · intro h0
    have := congrArg (Subgroup.map L.subtype) h0
    rwa [subgroupOf_map_subtype, inf_of_le_left h, Subgroup.map_bot] at this
  · rintro rfl
    exact bot_subgroupOf L

theorem subgroupOf_injective_of_le {T₁ T₂ L : Subgroup G} (h₁ : T₁ ≤ L) (h₂ : T₂ ≤ L)
    (h : T₁.subgroupOf L = T₂.subgroupOf L) : T₁ = T₂ := by
  have := congrArg (Subgroup.map L.subtype) h
  rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left h₁,
    inf_of_le_left h₂] at this

theorem commutator_le_of_le {T₁ T₂ S : Subgroup G} (h₁ : T₁ ≤ S) (h₂ : T₂ ≤ S) :
    ⁅T₁, T₂⁆ ≤ S := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact S.mul_mem (S.mul_mem (S.mul_mem (h₁ ha) (h₂ hb)) (S.inv_mem (h₁ ha))) (S.inv_mem (h₂ hb))

theorem subgroupOf_commutator_of_le {T₁ T₂ L : Subgroup G} (h₁ : T₁ ≤ L) (h₂ : T₂ ≤ L) :
    ⁅T₁, T₂⁆.subgroupOf L = ⁅T₁.subgroupOf L, T₂.subgroupOf L⁆ := by
  apply map_injective L.subtype_injective
  rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left h₁, inf_of_le_left h₂, inf_of_le_left (commutator_le_of_le h₁ h₂)]

theorem subgroupOf_le_normalizer_of_le {T₁ T₂ L : Subgroup G}
    (h : T₁ ≤ normalizer (T₂ : Set G)) :
    T₁.subgroupOf L ≤ normalizer ((T₂.subgroupOf L : Subgroup L) : Set L) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro z
  simp only [mem_subgroupOf, coe_mul, coe_inv]
  exact mem_normalizer_iff.mp (h (mem_subgroupOf.mp hy)) z

theorem coe_subgroupOf_mul_of_le {T₀ T₁ T₂ L : Subgroup G} (h₀ : T₀ ≤ L) (h₁ : T₁ ≤ L)
    (h₂ : T₂ ≤ L) (h : (T₀ : Set G) = (T₁ : Set G) * (T₂ : Set G)) :
    ((T₀.subgroupOf L : Subgroup L) : Set L) =
      ((T₁.subgroupOf L : Subgroup L) : Set L) * ((T₂.subgroupOf L : Subgroup L) : Set L) := by
  apply Set.image_injective.mpr L.subtype_injective
  rw [Set.image_mul, ← coe_map, ← coe_map, ← coe_map, subgroupOf_map_subtype,
    subgroupOf_map_subtype, subgroupOf_map_subtype, inf_of_le_left h₀, inf_of_le_left h₁,
    inf_of_le_left h₂, h]

theorem isSylowOf_subgroupOf_iff [Finite G] {p : ℕ} [Fact p.Prime] {T X L : Subgroup G}
    (hT : T ≤ L) (hX : X ≤ L) :
    IsSylowOf p (T.subgroupOf L) (X.subgroupOf L) ↔ IsSylowOf p T X := by
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, subgroupOf_map_subtype,
    subgroupOf_map_subtype, inf_of_le_left hT, inf_of_le_left hX]

theorem pCore_subgroupOf_of_le {X L : Subgroup G} (hX : X ≤ L) :
    (CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype =
      ((CFSG.pCore 2 X).map X.subtype).subgroupOf L := by
  apply map_injective L.subtype_injective
  rw [CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, subgroupOf_map_subtype,
    subgroupOf_map_subtype, inf_of_le_left hX, inf_of_le_left ((map_subtype_le _).trans hX)]

theorem subgroupOf_inf {T₁ T₂ L : Subgroup G} :
    (T₁ ⊓ T₂).subgroupOf L = T₁.subgroupOf L ⊓ T₂.subgroupOf L :=
  comap_inf _ _ _

end CFSG.Quasithin.H13.NQRigid

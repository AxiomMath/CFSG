module

public import CFSG.Quasithin.Vol2.Ch11SecSQuot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G]

theorem modO2Image_pCoreOf_le [Finite G] {Y A : Subgroup G} (hAY : A ≤ Y) :
    modO2Image Y (pCoreOf 2 A) ≤ pCoreOf 2 (modO2Image Y A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : modO2Image Y (pCoreOf 2 A) ≤ modO2Image Y A :=
    Subgroup.map_mono fun x hx => CFSG.LieType.BorelTits.pCoreOf_le 2 A hx
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle
    (modO2Image_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)) ?_
  have hp : IsPGroup 2 ↥((pCoreOf 2 A).subgroupOf Y) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A).of_equiv
      (Subgroup.subgroupOfEquivOfLe ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAY)).symm
  exact hp.map _

theorem mk_mem_normalizer_modO2Image {Y A : Subgroup G} {x : G} (hx : x ∈ Y)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hx⟩ ∈
      Subgroup.normalizer (modO2Image Y A : Set (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
  have hz : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.zpowers_le).mpr hxA
  exact modO2Image_le_normalizer hz ⟨⟨x, hx⟩, Subgroup.mem_zpowers x, rfl⟩

theorem mk_mem_sectionCentralizer [Finite G] {Y A : Subgroup G} {x : G} (hAY : A ≤ Y)
    (hx : x ∈ Y) (hxA : x ∈ sectionCentralizer A (pCoreOf 2 A)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨x, hx⟩ ∈
      sectionCentralizer (modO2Image Y A) (pCoreOf 2 (modO2Image Y A)) := by
  obtain ⟨hxN, -, hxc⟩ := hxA
  have hN := mk_mem_normalizer_modO2Image hx hxN
  refine ⟨hN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hN, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have ha' : (a : G) ∈ A := ha
  refine modO2Image_pCoreOf_le hAY ⟨⟨x, hx⟩ * a * ⟨x, hx⟩⁻¹ * a⁻¹, ?_, ?_⟩
  · exact hxc _ ha'
  · simp

end CFSG.Quasithin.Vol2.Ch11.SecS

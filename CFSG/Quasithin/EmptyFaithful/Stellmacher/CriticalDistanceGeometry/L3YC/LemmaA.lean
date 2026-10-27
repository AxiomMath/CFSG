module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.RowsTheoremA
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem eq_of_modO2Image_eq {H S L L₁ : Subgroup G} (hS : IsSylowTwoOf S H)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hL₁perf : ⁅L₁, L₁⁆ = L₁)
    (hLL₁ : L ≤ L₁) (hL₁H : L₁ ≤ H) (hbar : modO2Image H L = modO2Image H L₁) : L₁ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype
  have hPS : P ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact pCore_two_le_subgroupOf hS hy
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hPS.trans hSL
  have hP2 : IsPGroup 2 ↥P := hS.2.1.to_le hPS
  have hL₁le : L₁ ≤ L ⊔ P := by
    intro x hx
    have hxH : x ∈ H := hL₁H hx
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨x, hxH⟩ ∈ modO2Image H L₁ :=
      ⟨⟨x, hxH⟩, hx, rfl⟩
    rw [← hbar] at hmem
    obtain ⟨⟨l, hlH⟩, hl, hlx⟩ := hmem
    have hk : (⟨l, hlH⟩ : H)⁻¹ * ⟨x, hxH⟩ ∈ CFSG.pCore 2 ↥H :=
      (QuotientGroup.eq (s := CFSG.pCore 2 ↥H)).mp hlx
    have hk' : l⁻¹ * x ∈ P :=
      Subgroup.mem_map.mpr ⟨(⟨l, hlH⟩ : H)⁻¹ * ⟨x, hxH⟩, hk, rfl⟩
    have hl' : l ∈ L := hl
    have : x = l * (l⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hl' hk'
  have hLnorm : (L.subgroupOf (L ⊔ P)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le (fun x hx => Subgroup.le_normalizer hx) hPN)
  have hnil : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hsolv : Group.IsSolvable ↥P := @IsNilpotent.to_isSolvable _ _ hnil
  have hcore : perfectCore (L ⊔ P) ≤ L :=
    perfectCore_le_of_sup_solvable le_sup_left hLnorm rfl hsolv
  exact le_antisymm ((le_perfectCore_of_perfect hL₁le hL₁perf).trans hcore) hLL₁

theorem exists_component_row_ne (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) {H S L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H)
    (hLH : L ≤ H) (hL : L ∈ lFamily S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hnn : ¬ H ≤ Subgroup.normalizer (L : Set G)) :
    ∃ L₁ ∈ cComp H, L ≤ L₁ ∧
      (A312Case (modO2Image H L) (modO2Image H L₁) ∨
        A312Nonquasi (modO2Image H L) (modO2Image H L₁)) := by
  obtain ⟨L₁, h1, h2, h3⟩ := exists_component_row hQ hs hnab h37 h39 h312 hH hS hLH hL
  refine ⟨L₁, h1, h2, ?_⟩
  rcases h3 with h3 | h3
  · exfalso
    have hL₁eq : L₁ = L :=
      eq_of_modO2Image_eq hS hSL (perfect_of_mem_cComp h1) h2 (le_of_mem_cComp h1) h3
    have hnorm : (L₁.subgroupOf H).Normal :=
      lemma_1_2_4_normal hQ hs hnab h37 h38 hH hS hL h2 h1 hSL
    rw [hL₁eq] at hnorm
    exact hnn ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mp hnorm)
  · exact h3

end Stellmacher.CD.L3YC

end CFSG.Quasithin

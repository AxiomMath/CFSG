module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.GoldschmidtS146PGroups
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin

theorem card_sl4_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_SL_field]
  simp [Fin.prod_univ_four, ZMod.card]

section Step1

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_quot {K₁ : Subgroup G}
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) :
    IsSimpleGroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
  obtain ⟨e⟩ := hK4
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    CFSG.Quasithin.GoldS146P.sl_simple 4 (by norm_num)
  exact e.isSimpleGroup

theorem index_pCore_eq {K₁ : Subgroup G}
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) :
    (CFSG.pCore 2 ↥K₁).index = 20160 := by
  obtain ⟨e⟩ := hK4
  rw [Subgroup.index, Nat.card_congr e.toEquiv, card_sl4_two]

theorem perfect_top_of_cComp {K₁ H : Subgroup G} (hK : quasithinIsCComponent K₁ H) :
    ⁅(⊤ : Subgroup ↥K₁), (⊤ : Subgroup ↥K₁)⁆ = ⊤ := by
  have htop : (⊤ : Subgroup ↥K₁).map K₁.subtype = K₁ := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype K₁
  apply Subgroup.map_injective (f := K₁.subtype) Subtype.val_injective
  rw [Subgroup.map_commutator, htop]
  exact hK.2.1

theorem conj_eq_of_mem_centralizer {V₂ : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (V₂ : Set G)) {v : G} (hv : v ∈ V₂) : x * v * x⁻¹ = v := by
  have h := Subgroup.mem_centralizer_iff.1 hx v hv
  rw [← h]
  group

theorem L0_le_K₁ {K₁ V₁ V₂ L : Subgroup G} (hLK : lOne L V₁ ≤ K₁)
    (hV : V₁ ≤ V₂) :
    oTwoUpper (L ⊓ Subgroup.centralizer (V₂ : Set G)) ≤ K₁ := by
  have hle : oTwoUpper (L ⊓ Subgroup.centralizer (V₂ : Set G)) ≤ lOne L V₁ := by
    unfold oTwoUpper
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨⟨hxL, hxC⟩, hodd⟩
    have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [conj_eq_of_mem_centralizer hxC (hV hh)]
        exact hh
      · intro hh
        have h1 : x⁻¹ * (x * h * x⁻¹) * x = h := by group
        have h2 := conj_eq_of_mem_centralizer (Subgroup.inv_mem _ hxC) (hV hh)
        rw [inv_inv] at h2
        rw [← h1, h2]
        exact hh
    unfold lOne
    exact Subgroup.subset_closure ⟨⟨hxL, hxN⟩, hodd⟩
  exact le_trans hle hLK

end Step1

end CFSG.Quasithin.H13.C1294

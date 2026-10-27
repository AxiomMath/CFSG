module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Main

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Orbit CFSG.Quasithin.H13.U3.GC137.S2

theorem g2Facts_transport {M₂ MK : Type} [CommGroup M₂] [CommGroup MK] [Finite M₂] [Finite MK]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (e : M₂ ≃* MK)
    (ρ₂ : Gam →* MulAut M₂) (ρK : ↥(quasithinG2 K) →* MulAut MK)
    (hρ : ∀ g, MulAut.congr e.symm (ρK g) = ρ₂ (conjF2Hom hK g))
    (h : G2Facts ρ₂.range ((g2Derived (ZMod 2)).map ρ₂)) :
    G2Facts ρK.range ((g2Derived K).map ρK) := by
  refine G2Facts.of_equiv e.symm (Xm := ρ₂.range) (Lm := (g2Derived (ZMod 2)).map ρ₂) ?_ ?_ h
  · ext y
    constructor
    · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
      exact ⟨conjF2Hom hK g, (hρ g).symm⟩
    · rintro ⟨g', rfl⟩
      obtain ⟨g, rfl⟩ := conjF2Hom_surjective hK g'
      exact ⟨ρK g, ⟨g, rfl⟩, hρ g⟩
  · rw [← map_g2Derived_conjF2Hom hK, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g : 1
    exact hρ g

theorem u33G2Facts_holds :
    U33G2Facts := by
  intro K _ _ _ hK
  refine ⟨?_, ?_⟩
  · have : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
    exact g2Facts_transport hK (modQEquivK hK) _ _ (congr_modQEquivK_symm hK) g2Facts_Q
  · have : Finite ModO := Nat.finite_of_card_ne_zero (by rw [card_ModO]; norm_num)
    exact g2Facts_transport hK (modOEquivK hK) _ _ (congr_modOEquivK_symm hK) g2Facts_O

end CFSG.Quasithin.H13.U3.GC137

module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2NoOffMod
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2At
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Line
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Pt

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
  CFSG.Quasithin.H13.Orbit CFSG.Quasithin.H13.U3.GC137.S2 CFSG.ABGLocalTools
  CFSG.QuasithinUnique.Setup.X6

variable {W : Type} [CommGroup W]

theorem cg_map_image (ρ : Gam →* MulAut W) (c : Gam) (K : Subgroup Gam) :
    (K.map ρ).map (cg (ρ c)) = (K.map (MulAut.conj c).toMonoidHom).map ρ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [cg_apply_self, MulAut.conj_apply]

theorem map_conj_derived (c : Gam) :
    (g2Derived (ZMod 2)).map (MulAut.conj c).toMonoidHom = g2Derived (ZMod 2) := by
  have hn : (g2Derived (ZMod 2)).Normal := by
    rw [g2Derived_eq_commutator]
    exact Subgroup.commutator_normal ⊤ ⊤
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hn.conj_mem _ hy c
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · simpa using hn.conj_mem _ hx c⁻¹
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

theorem isSylowOf_S_top : IsSylowOf 2 sSubG (⊤ : Subgroup Gam) := by
  rw [isSylowOf_iff]
  refine ⟨le_top, isPGroup_S, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index sSubG
  rw [card_sSubG, card_g2Two] at h
  rw [show sSubG.index = 189 by omega]
  decide

theorem isSylowTwoOf_S_range (ρ : Gam →* MulAut W) (hρ : Function.Injective ρ) [Finite W] :
    IsSylowTwoOf (sSubG.map ρ) ρ.range := by
  have h := isSylowOf_map_injective ρ hρ isSylowOf_S_top
  rw [← MonoidHom.range_eq_map] at h
  exact isSylowTwoOf_iff_isSylowOf.2 h

theorem g2Facts_two_of [Finite W] (ρ : Gam →* MulAut W) (hρ : Function.Injective ρ)
    (hrk : rkIdx (fixV ((g2Derived (ZMod 2)).map ρ)) = 6)
    (hnoOff : ∀ B : Subgroup (MulAut W), B ≤ (g2Derived (ZMod 2)).map ρ → B ≠ ⊥ →
      IsElemAbelian2 B → Nat.card W ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False)
    (hline : ∃ l₀ : Subgroup W, fixV ((g2Derived (ZMod 2)).map ρ) ≤ l₀ ∧
      Nat.card ↥l₀ = 4 * Nat.card ↥(fixV ((g2Derived (ZMod 2)).map ρ)) ∧
      ∀ g ∈ Pline, ∀ w ∈ l₀, ρ g w ∈ l₀)
    (hpoint : G2Point ρ.range ((g2Derived (ZMod 2)).map ρ) (Ppt.map ρ)) :
    G2Facts ρ.range ((g2Derived (ZMod 2)).map ρ) := by
  refine G2Facts.of_at (isSylowTwoOf_S_range ρ hρ) ?_
    (g2FactsAt_of ρ hρ hrk hnoOff hline hpoint)
  rintro _ ⟨c, rfl⟩
  rw [cg_map_image, map_conj_derived]

theorem g2Facts_Q :
    G2Facts (g2QAct (ZMod 2)).range ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2))) :=
  haveI : Finite ModQ := Nat.finite_of_card_ne_zero (by rw [card_ModQ]; norm_num)
  g2Facts_two_of _ g2QAct_injective rk_L_Q noOff_Q lineQ_facts g2Point_Q

theorem g2Facts_O :
    G2Facts (g2OAct (ZMod 2)).range ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) :=
  haveI : Finite ModO := Nat.finite_of_card_ne_zero (by rw [card_ModO]; norm_num)
  g2Facts_two_of _ g2OAct_injective rk_L_O noOff_O lineO_facts g2Point_O

end CFSG.Quasithin.H13.U3.GC137

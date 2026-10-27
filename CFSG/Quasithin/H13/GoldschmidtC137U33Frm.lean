module

public import CFSG.Quasithin.Background.C124BlkTop
public import CFSG.Quasithin.H13.GoldschmidtC137U33Mod
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ent

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autI_le_normalizer {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hn : X ≤ normalizer (L : Set G)) :
    autI hV X ≤ normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
      Set (MulAut (IntMod V hV))) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => C124.autI_conj_mem hV hn y hy h hh
  · intro hh
    have := C124.autI_conj_mem hV hn y⁻¹ (Subgroup.inv_mem _ hy) _ hh
    simpa [mul_assoc] using this

omit [Finite G] in
theorem commV_autI_eq_top {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLN : L ≤ normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V) :
    commV (autI hV L) = ⊤ :=
  CFSG.Quasithin.C124.commV_autI_eq_top hV hLN hVL

theorem g2Facts_of_entry33 (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hfacts : U33G2Facts) {X T V L R : Subgroup G} {hV : IsElemAbelian 2 V}
    (E : Entry33 X T V L R hV) (hVL : ⁅V, L⁆ = V) : G2Facts (autI hV X) (autI hV L) := by
  have hLX : L ≤ X := le_of_mem_cComp E.comp
  have hLN : L ≤ normalizer (V : Set G) := hLX.trans E.red.2.1
  have hcomm := commV_autI_eq_top hV hLN hVL
  have hpair := E.case1i.2.1
  rw [hcomm, inf_top_eq] at hpair
  have hnat := g2NaturalDerived_of_modulePair E.card hpair
  obtain ⟨A, hA⟩ : ∃ A, IsFFStarOffender (autI hV X) A := by
    obtain ⟨A, hA⟩ := E.stab.1
    exact ⟨A, E.stab.2.1 A hA⟩
  exact g2Facts_of_natural hcov hnorm hfacts IntMod.sq_eq_one (autI_mono hV hLX)
    (autI_le_normalizer hV E.normal) hcomm hnat E.card ⟨A, hA⟩

end CFSG.Quasithin.H13.U3.GC137

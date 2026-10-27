module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15HeB
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Sub
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Types
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem core3HeBorel_of_inputs
    (h56 : AsB56) (hcover : AsA36NoOddCover) (hG2 : FactG2Cayley)
    (h210 : Lemma14210) (hC : Core3HeLnTwo) (hA7 : Core3HeA7) : Core3HeBorel := by
  intro G _ _ T M H K1 L M₁ c hchar hq hY
  have hl := c.listTypes h56 hcover hG2 h210 hchar hq hY
  have hO2 : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    Setup.Campbell.pCore_quotient_pCore_eq_bot' 2
  have hnC : ¬ (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    fun h => hC G T M H K1 L M₁ c hchar hq hY h
  have hnA7 : ¬ IsAlt 7 ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    fun h => hA7 G T M H K1 L M₁ c hchar hq hY h
  refine c.le_normalizer_of_bar hY ?_
  refine QA23.borel_of_listAD hq hO2 hl hnC hnA7 c.bar_sylow ?_ c.bar_solvable c.bar_perfect
    c.bar_ne_bot c.bar_sup_ne_top c.bar_bender
  exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
    ⟨(le_sup_right : S1421.sOf T K1 ≤ _) (Subgroup.mem_subgroupOf.mp hx).1,
      (Subgroup.mem_subgroupOf.mp hx).2⟩)

end CFSG.Quasithin

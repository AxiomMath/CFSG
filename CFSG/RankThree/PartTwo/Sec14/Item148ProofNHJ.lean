module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepsNHJ
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem allPointsHJ_of_isLBConfig (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {B L' : Subgroup G} {b d : G} (hc : IsLBConfig A B b d L')
    (hB : IsHyperplane A B) : AllPointsHJ A := by
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLb, ⟨φ⟩, hdL, S, hdS, hSd⟩ := hc
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hL'mem : L' ∈ lA A b := hLb ▸ Set.mem_singleton L'
  have hc0 : Subgroup.center (↥L' ⧸ CFSG.pCore 2 ↥L') = ⊥ := by
    have hmap := Subgroup.map_center_eq φ
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  have hq := isQuasisimple_of_mulEquiv_nativeJ2 hJ2 hJ2c φ
  have hθ := aschbacherSolvableCore_eq_pCore_two hq hc0
  have hJ2θ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans φ⟩
  intro e he
  exact exists_hj_of_hj_point h134 h48 h415 h hbΩ hL'mem hJ2θ hdA hd1 ⟨hdL, S, hdS, hSd⟩ he

theorem lB_eq_bot_of_not_allPointsHJ (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) {B : Subgroup G} (hB : IsHyperplane A B) :
    lB A B = ⊥ :=
  lB_eq_bot fun _ _ _ hc => hNHJ (allPointsHJ_of_isLBConfig h134 hJ2 h48 h415 hJ2c h hc hB)

section Certificates


theorem rank3II_14_8_of_steps_nhj (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)
    (hN : Step148Normal) (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType)
    (hLift : Step148Lift) (hD4 : Step148D4) (hOne : Step148One) (hRank : Step148Rank)
    (hPGL : Step148PGL) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hNHJ : ¬ AllPointsHJ A) : Item148 A (lB A) :=
  rank3II_14_8_of_steps_of_lB_eq_bot hN hCore hPoint hKT hLift hD4 hOne hRank hPGL h
    fun _ hB => lB_eq_bot_of_not_allPointsHJ h134 hJ2 h48 h415 hJ2c h hNHJ hB

theorem item148NHJS14_of_steps (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hN : Step148Normal) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    (hOne : Step148One) (hRank : Step148Rank) (hPGL : Step148PGL) : Item148NHJS14 :=
  fun _ _ _ _ _ _ h hNHJ =>
    rank3II_14_8_of_steps_nhj h134 CFSG.Sporadic.J2.isSimpleGroup_J2 h48 h415
      (KFacts.KS14.center_nativeJ2_eq_bot h415) hN hCore hPoint hKT hLift hD4 hOne hRank hPGL h
      hNHJ

theorem item148S14_of_hj_nhj (hHJ : Item148HJS14) (hNHJ : Item148NHJS14) : Item148S14 := by
  intro G _ _ A c L h
  by_cases hall : AllPointsHJ A
  · exact hHJ G A c L h hall
  · exact hNHJ G A c L h hall

end Certificates

end CFSG.RankThree.PartTwo.Sec14

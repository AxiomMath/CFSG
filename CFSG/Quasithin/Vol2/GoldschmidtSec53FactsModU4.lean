module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU4Cent
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.Sec53F.BA

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem normalizer_hypUnitriangular_four :
    Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) = hypBorel h 2 0 :=
  UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)

theorem parP_inf_parP2 : parP h ⊓ parP2 h = hypBorel h 2 0 := by
  ext g
  rw [Subgroup.mem_inf, mem_hypBorel]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact MulAction.mem_stabilizer_iff.mp h1
    · exact MulAction.mem_stabilizer_iff.mp h2
  · intro hg
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hg 1 le_rfl (by norm_num)),
      MulAction.mem_stabilizer_iff.mpr (hg 2 (by norm_num) le_rfl)⟩

theorem u4_yamStd : Yam.YamStd (hypSU h 2 0) (hypUnitriangular h 2 0) (parP h) (parP2 h) := by
  have := U4Par.finite_hypSU h
  have hB := normalizer_hypUnitriangular_four h
  have hBP : hypBorel h 2 0 ≤ parP h :=
    UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num)
  have hBP2 : hypBorel h 2 0 ≤ parP2 h :=
    UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) le_rfl
  refine ⟨isSylowTwoOf_hypUnitriangular h, ?_, parP_ne_parP2 h, hB ▸ hBP, hB ▸ hBP2,
    isCoatom_parP h, isCoatom_parP2 h, ?_, (isMaximalTwoLocal_parP h).1,
    (isMaximalTwoLocal_parP2 h).1⟩
  · intro R hR hRp
    have := isSimpleGroup_hypSU h
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with h0 | h0
    · exact h0
    · exfalso
      apply not_isPGroup_hypSU h
      rw [h0] at hRp
      exact hRp.of_equiv Subgroup.topEquiv
  · intro A hNA hAt
    obtain ⟨A', hA', hAA'⟩ := (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hAt
    rw [hB] at hNA
    rcases eq_parP_or_eq_parP2 h hA' (hNA.trans hAA') with rfl | rfl
    · exact Or.inl hAA'
    · exact Or.inr hAA'

theorem u4_lieFactsOf (hm : 2 ≤ m) :
    Yam.LieFactsOf (hypUnitriangular h 2 0) (parP h) (parP2 h) := by
  have := U4Par.finite_hypSU h
  have hB := normalizer_hypUnitriangular_four h
  refine ⟨⟨?_, fun a ha a' ha' h1 h1' => ?_, fun a ha _ _ h1 _ => ?_⟩, ?_,
    hypUnitriangular_le_perfectCore_parP h hm, hypUnitriangular_le_perfectCore_parP2 h hm⟩
  · rw [parP_inf_parP2, ← hB]
    exact (borelAutData_u4 h).isSolvable_B
  · exact trans_zRad h (centerOf_perfectCore_parP_le h hm ha)
      (centerOf_perfectCore_parP_le h hm ha') h1 h1'
  · rw [centerOf_perfectCore_parP2_eq_bot h hm, Subgroup.mem_bot] at ha
    exact absurd ha h1
  · rw [parP_inf_parP2, hB]

end CFSG.Quasithin.H13.Sec53F.Unit

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Blueprint CFSG.Quasithin.H13.U4Par

theorem lieModelFacts_u4 : LieModelFacts .PSU 4 :=
  Yam.lieModelFacts_of_std fun Y _ f hpar hY => by
    obtain ⟨K, _, h, ⟨e⟩⟩ := exists_hypSU_equiv_of_lieModel hY
    exact ⟨_, inferInstance, finite_hypSU h, _, _, _, Unit.u4_yamStd h,
      Unit.u4_lieFactsOf h hpar.1, ⟨e.symm⟩⟩

end CFSG.Quasithin.H13.Sec53F

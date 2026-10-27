module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeALeech
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo13

public section

namespace CFSG.Sporadic.MI301Three

open CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem exists_elemAbelian_mem_of_isConj_c0 {y : CFSG.Blueprint.NativeSporadic.Co1}
    (hy : IsConj CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech.c0 y) :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.Co1, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card ↥E = 3 ^ 6 ∧ y ∈ E := by
  obtain ⟨v, rfl⟩ := isConj_iff.1 hy
  obtain ⟨u, x, hux, hx⟩ := CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech.exists_conj_root
  have hxr : co1MatEquiv x = Co1T.root 1 := Subtype.ext (hx.eq (Co1T.wordL_rep _))
  have hgx : gaToCo1 (Co1T.root 1) = x :=
    Units.ext (Subtype.ext (by rw [gaToCo1_val, ← hxr, co1MatEquiv_val]))
  obtain ⟨n, -, hnT, -⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co13.plane_data
  have hw : Function.Injective (MulAut.conj (v * u * gaToCo1 n)).toMonoidHom := by
    rw [MulEquiv.coe_toMonoidHom]
    exact (MulAut.conj _).injective
  refine ⟨(Co1T.eSplit.T.map gaToCo1).map (MulAut.conj (v * u * gaToCo1 n)).toMonoidHom,
    (Co1T.eSplit.T_elemAbelian.map _).map _, ?_,
    Subgroup.mem_map.2 ⟨gaToCo1 (n⁻¹ * Co1T.root 1 * n), Subgroup.mem_map.2 ⟨_, hnT, rfl⟩, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective hw, Subgroup.card_map_of_injective gaToCo1_injective]
    exact CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co13.card_T.trans (by norm_num)
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, hgx, hux]
    group

end CFSG.Sporadic.MI301Three

end

module

public import CFSG.Quasithin.H13.LocDblMatrix
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Quasithin

theorem degree_two_matrix_Ccomponents_quasisimple_and_unique {k : Type*} [Field k] [Finite k]
    (H : Subgroup (GL (Fin 2) k)) :
    (∀ B ∈ cComp H, CFSG.IsQuasisimple ↥B) ∧ (cComp H).Subsingleton := by
  obtain ⟨p, hchar⟩ := CharP.exists k
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite k p
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero k p).resolve_right hp0⟩
  let e : GL (Fin 2) k ≃* LinearMap.GeneralLinearGroup k (Fin 2 → k) :=
    Matrix.GeneralLinearGroup.toLin
  have h := LocDbl.cComp_quasisimple_and_subsingleton_of_finrank_two (Module.finrank_fin_fun k)
    (H.map e.toMonoidHom)
  refine ⟨fun B hB => ?_, fun B hB C hC => ?_⟩
  · have hq := h.1 _ (cComp_map_mulEquiv e hB)
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (B.equivMapOfInjective e.toMonoidHom e.injective)).2 hq
  · exact Subgroup.map_injective e.injective
      (h.2 (cComp_map_mulEquiv e hB) (cComp_map_mulEquiv e hC))

end CFSG.Quasithin.H13.NQCat

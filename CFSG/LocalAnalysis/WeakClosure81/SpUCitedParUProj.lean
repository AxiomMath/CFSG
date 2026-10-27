module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUStd
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParQuot
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParQuotInv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {r ε : ℕ}

theorem uCited_rootParabolic_proj {f : ℕ} (h : UnitaryFieldData 2 f K) (hr : 2 ≤ r)
    (hε : ε ≤ 1) :
    RootParabolic
      ((uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))).map
        (hypProj h r ε))
      ((hypUnitriangular h r ε).map (hypProj h r ε))
      ((uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K))).map
        (hypProj h r ε))
      ((uCitedPar h r ε).map (hypProj h r ε)) 2 := by
  haveI : Finite ↥(hypSU h r ε) := inferInstance
  obtain ⟨T, hT⟩ :=
    (unitary_order_and_Sylow (p := 2) (r := r) (ε := ε) h (by omega) hε).2.1
  have hU : IsPGroup 2 ↥(hypUnitriangular h r ε) := hT ▸ T.isPGroup'
  have hR : IsPGroup 2
      ↥(uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))) :=
    IsPGroup.to_le hU (uCited_root_le_unipotent h ⟨0, by omega⟩)
  have hker : (hypProj h r ε).ker ≤ Subgroup.center ↥(hypSU h r ε) := by
    rw [ker_hypProj]
    exact normOneScalars_le_center h _ _
  have hodd : ¬ 2 ∣ Nat.card (hypProj h r ε).ker := by
    rw [ker_hypProj, card_hypScalars h (by omega)]
    exact not_dvd_gcd_pow_add_one h _
  have hPα : (hypProj h r ε).ker ≤ uCitedPar h r ε := by
    rw [ker_hypProj]
    exact uCited_hypScalars_le_par h
  have hinv := spUCited_invariant_map (hypProj h r ε) (hypProj_surjective h r ε) hker hodd
    hU hR (uCited_normalizer_le_par h (by omega) hε) (uCited_cover h hr hε)
    (uCited_not_par_le_normalizer h hr hε)
    (fun P' h1 h2 h3 => uCited_unique_cover h hr hε P' h1 h2 h3)
  exact spUCited_rootParabolic_map (hypProj h r ε) (hypProj_surjective h r ε) hker hodd
    hR hPα (uCited_rootParabolic_std h hr hε) hinv

end CFSG.LocalAnalysis.WeakClosure81

end

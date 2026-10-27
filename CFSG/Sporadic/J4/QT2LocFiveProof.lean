
module

public import CFSG.Sporadic.J4.QT2LocFiveProofBase

public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem radical_eta_T (hF : J4Facts) {c : ℕ} (hc : c ∈ tMasks) :
    Radical (eta uJ 11 c) (Eg uJ 11) := by
  have hM := hF.mat
  refine radical_of_centralizer_le Hj (Eg uJ 11) (eta uJ 11 c) (isPGroup_Eg (elem_uJ hM)) ?_
    (eta_mem_Eg 11 le_rfl c) (Hj_normalizes_Eg hM) (centralizer_Hj hM hF) ?_ ?_
  · intro x hx e he
    obtain ⟨c₁, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hx
    obtain ⟨c₂, -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 he
    exact eta_comm (elem_uJ hM) c₁ c₂
  · intro q hq
    have h := comm_of_mem_centralizer hq
    exact centralizer_le_Hj_of_T hF hc h
  · intro g hg h5
    exact lt_relIndex_Eg_of_order_five hF hg h5

end CFSG.Sporadic.J4.QT2

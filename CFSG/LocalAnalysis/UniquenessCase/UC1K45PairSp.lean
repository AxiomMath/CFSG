module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpCases
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open PairSpLem

theorem z3E9A5Mod2_of_pairShapeHom {H : Type} [Group H] (Y : Subgroup H)
    (h : PairShapeHom ↥Y) : Z3E9A5Mod2 Y := by
  obtain ⟨Q, _, f, hf, hker, hQ, hshape⟩ := h
  intro N hNnorm hN
  have hNker : N = f.ker := by
    rw [hN, CFSG.openPCoreOf_subgroupOf]
    exact pCore_eq_ker f hf hker hQ
  subst hNker
  let e : ↥Y ⧸ f.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hf
  rcases hshape with ⟨hcyc, hcard⟩ | ⟨hcard, hcomm⟩ | halt
  · exact Or.inl ⟨(MulEquiv.isCyclic e).mpr hcyc, (Nat.card_congr e.toEquiv).trans hcard⟩
  · refine Or.inr (Or.inl ⟨(Nat.card_congr e.toEquiv).trans hcard, ?_⟩)
    exact IsMulCommutative.of_comm fun x y =>
      e.injective (by rw [map_mul, map_mul]; exact hcomm.is_comm.comm _ _)
  · refine Or.inr (Or.inr ?_)
    rcases halt with ⟨g⟩
    exact ⟨e.trans g⟩

theorem pairSp_holds : PairSp := by
  intro W _ _ _ B hB hAlt a b ha hb hoa hob hra hrb
  exact z3E9A5Mod2_of_pairShapeHom _
    (pairShapeHom_closure_pair ⟨hB, hAlt, ⟨ha, hoa, hra⟩, ⟨hb, hob, hrb⟩⟩)

end CFSG.LocalAnalysis.UniquenessCase.UCK

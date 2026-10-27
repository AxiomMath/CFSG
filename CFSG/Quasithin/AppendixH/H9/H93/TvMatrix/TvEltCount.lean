module

public import CFSG.Quasithin.AppendixH.H9.H93.H93Defs
public import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix.RankOneCriterion
public import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix.TransvectionMatrix

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem isTvElt_pairActN_iff (A : GL (Fin 4) (ZMod 2)) :
    IsTvElt (pairActN 4 A) ↔ IsTvMat A :=
  ⟨fun h => (rk_commOn_V1n_zpowers_pairActN_eq_one_iff A).mp h.2,
    fun h => ⟨pairActN_mem_Lg A, (rk_commOn_V1n_zpowers_pairActN_eq_one_iff A).mpr h⟩⟩

@[expose] def tvPairs4 : Finset ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  Finset.univ.filter fun p => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ⬝ᵥ p.1 = 0

theorem card_tvPairs4 : tvPairs4.card = 105 := by
  decide +kernel

@[expose] noncomputable def tvMap4 (p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :
    MulAut (PairN 4) :=
  if h : p.2 ⬝ᵥ p.1 = 0 then pairActN 4 (transvectionGL p.1 p.2 h) else 1

theorem isTvElt_subset_tvMap4_image :
    {g : MulAut (PairN 4) | IsTvElt g} ⊆ tvMap4 '' (tvPairs4 : Set _) := by
  intro g hg
  obtain ⟨A, rfl⟩ := mem_Lg_iff.mp hg.1
  obtain ⟨u, f, h, hu, hf, rfl⟩ := ((isTvElt_pairActN_iff A).mp hg).exists_eq_transvectionGL
  refine ⟨(u, f), ?_, ?_⟩
  · simp only [tvPairs4, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨hu, hf, h⟩
  · simp only [tvMap4, dif_pos h]

theorem ncard_isTvElt_le_105 : Set.ncard {g : MulAut (PairN 4) | IsTvElt g} ≤ 105 :=
  calc Set.ncard {g : MulAut (PairN 4) | IsTvElt g}
      ≤ (tvMap4 '' (tvPairs4 : Set ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)))).ncard :=
        Set.ncard_le_ncard isTvElt_subset_tvMap4_image (Set.toFinite _)
    _ ≤ (tvPairs4 : Set ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2))).ncard :=
        Set.ncard_image_le (Finset.finite_toSet _)
    _ = tvPairs4.card := Set.ncard_coe_finset _
    _ = 105 := card_tvPairs4

end CFSG.ASVolI.ChH

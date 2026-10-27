module

public import CFSG.Quasithin.AppendixH.H9.H92.RadCard
public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad
public import CFSG.Quasithin.AppendixH.H9.H92.QuadRad
public import CFSG.Quasithin.AppendixH.H9.H92.RadTransfer.ElemAbelianLift

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem exists_radV1_of_card_ge (E : Subgroup (MulAut (PairN 5))) (hE : E ≤ Lg 5)
    (hab : IsElemAbelian2 E) (h32 : 32 ≤ Nat.card E) :
    ∃ D : Subgroup (PairN 5), D ≤ V1n 5 ∧ (rk ↥D = 2 ∨ rk ↥D = 3) ∧ E ≤ RadV1 5 D := by
  obtain ⟨E', rfl⟩ := exists_map_pairActN_eq_of_le_Lg hE
  obtain ⟨hcomm, hsq⟩ := comm_sq_of_isElemAbelian2_map (pairActN 5) pairActN_injective E' hab
  have h32' : 32 ≤ Nat.card E' := by
    have h := card_map_pairActN E'
    omega
  have hq : ∀ g ∈ E', ∀ h ∈ E', ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
      ((h : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) = 0 := by
    by_contra hnq
    push_neg at hnq
    have := card_le_sixteen_of_not_quadratic E' hcomm hsq hnq
    omega
  obtain ⟨D', hD'r, hD'⟩ := exists_rad_of_quadratic E' hcomm hsq hq h32'
  refine ⟨v1Sub 5 D', v1Sub_le_V1n D', ?_, ?_⟩
  · rw [← finrank_v1Space_eq_rk _ (v1Sub_le_V1n D'), v1Space_v1Sub]
    exact hD'r
  · have hR : RadV1 5 (v1Sub 5 D') = (RadMat 5 D').map (pairActN 5) := by
      unfold RadV1
      rw [v1Space_v1Sub]
    rw [hR]
    exact Subgroup.map_mono fun g hg => hD' g hg

end CFSG.ASVolI.ChH

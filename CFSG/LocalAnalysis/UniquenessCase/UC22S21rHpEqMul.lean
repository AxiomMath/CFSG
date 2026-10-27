module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteFX
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.W3Lem45Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin (IsSylowIn)
open CFSG.Quasithin.E3 (wClos cClos sParam)
open CFSG.LocalAnalysis.WeakClosure81 (InFSq)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rhp_eq_mul_of_isSolvable {V H S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : IsSylowIn 2 S H) {i j : ℕ} (hj1 : 1 ≤ j) (hH : Group.IsSolvable ↥H)
    (hij : i + j < sParam hV) :
    (H : Set G) = ((H ⊓ centralizer (cClos V (i + j) S : Set G) : Subgroup G) : Set G) *
      ((H ⊓ normalizer (wClos V i S : Set G) : Subgroup G) : Set G) := by
  have h45 := PartTwo.w3Lem45_2_holds G H S j (CFSG.Quasithin.E3.gammaSet V i H) hj1 hS
    (CFSG.Quasithin.E3.isInvColl_gammaSet hV i H)
    (PartTwo.s16c11_compFactorAutInF_of_isSolvable j hH)
  rw [CFSG.Quasithin.E3.weakClosure_gammaSet hS.le] at h45
  have h45' : (H : Set G) =
      (CFSG.Quasithin.E1.eGen j H S (CFSG.Quasithin.E3.gammaSet V i H) : Set G) *
        ((H ⊓ normalizer (wClos V i S : Set G) : Subgroup G) : Set G) := h45
  have hSN : S ≤ H ⊓ normalizer (wClos V i S : Set G) :=
    fun s hs => ⟨hS.le hs,
      (Subgroup.le_normalizer.trans (CFSG.Quasithin.E3.normalizer_le_normalizer_wClos S)) hs⟩
  have hSC : S ≤ normalizer
      ((H ⊓ centralizer (cClos V (i + j) S : Set G) : Subgroup G) : Set G) :=
    CFSG.Quasithin.A1a.le_normalizer_inf (hS.le.trans Subgroup.le_normalizer)
      (CFSG.Quasithin.A1a.le_normalizer_centralizer (Subgroup.le_normalizer.trans
        (CFSG.Quasithin.E3.normalizer_le_normalizer_cClos (V := V) (i := i + j) S)))
  exact PartTwo.TwelveShort.eq_mul_of_le_sup (H := H) (S := S) inf_le_left inf_le_left hSN hSC
    (PartTwo.TwelveShort.eGen_le_sup_of_lt_sParam hV hS hij) h45'

theorem uc22s21rhp_eq_mul_of_or {V H S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hS : IsSylowIn 2 S H) {i j : ℕ} (hj1 : 1 ≤ j) (hF : InFSq j H ∨ Group.IsSolvable ↥H)
    (hij : i + j < sParam hV) :
    (H : Set G) = ((H ⊓ centralizer (cClos V (i + j) S : Set G) : Subgroup G) : Set G) *
      ((H ⊓ normalizer (wClos V i S : Set G) : Subgroup G) : Set G) :=
  hF.elim (fun hF => uc22p22tb_eq_mul hV hS hF hij)
    fun hH => uc22s21rhp_eq_mul_of_isSolvable hV hS hj1 hH hij

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

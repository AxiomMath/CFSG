module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfStarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfPull

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16fh_delta_le_two_of_star_sum
    (hAlt : ∀ (X : Type) [CommGroup X] [Finite X], (∀ x : X, x ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut X)) (U Z : Subgroup X) (n : ℕ), 6 ≤ n → n ≤ 8 →
        IsAlt ↥L n → (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) → commSub U L = U → Z ≤ fixV L →
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) L U Z 2 → rk ↥Z ≤ 2)
    (D : Data G) (h1217 : R1217 D) {V L : Subgroup G} (h : Hyp151 D ⊥ V L) {n : ℕ} (hn6 : 6 ≤ n)
    (hn8 : n ≤ 8) (hLn : IsAlt ↥(lBar ⊥ V h.isElemAbelian L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M ⊥ V h.isElemAbelian L) (wStar D.M ⊥ V h.isElemAbelian L) ⊥ 2) :
    delta15 D.M ⊥ V h.isElemAbelian L ≤ 2 := by
  obtain ⟨ρ, hρ⟩ := s16fh_lbar_lstar_equiv D h1217 h
  have hmap := s16fh_wStar_eq_map D h
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M ⊥ V h.isElemAbelian L)
      ((wTil ⊥ V h.isElemAbelian L).map (s16fhKappa D h)) ⊥ 2 := by
    rw [← hmap]
    exact hsum
  have hP : ∀ S : Subgroup (vStar D.M ⊥ V h.isElemAbelian L),
      S ≤ (wTil ⊥ V h.isElemAbelian L).map (s16fhKappa D h) →
      AlternatingNatural (lStar D.M ⊥ V h.isElemAbelian L) S ⊥ n →
      AlternatingNatural (lBar ⊥ V h.isElemAbelian L)
        (wTil ⊥ V h.isElemAbelian L ⊓ S.comap (s16fhKappa D h))
        (wTil ⊥ V h.isElemAbelian L ⊓ (s16fhKappa D h).ker) n := by
    intro S hS hSP
    exact s16fh_realizes_pull ρ (s16fhKappa D h) hρ (s16fh_wTil_stable D h) hS hSP
  have hsum'' : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar ⊥ V h.isElemAbelian L) (wTil ⊥ V h.isElemAbelian L)
      (wTil ⊥ V h.isElemAbelian L ⊓ (s16fhKappa D h).ker) 2 :=
    s16fh_sumOfNat_pull (s16fhKappa D h) hP hsum'
  have hrk := hAlt (Vtil ⊥ V h.isElemAbelian)
    (s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V h.isElemAbelian)
    (lBar ⊥ V h.isElemAbelian L) (wTil ⊥ V h.isElemAbelian L)
    (wTil ⊥ V h.isElemAbelian L ⊓ (s16fhKappa D h).ker) n hn6 hn8 hLn
    (s16fh_wTil_stable D h) (s16fh_wTil_comm D h) (s16fh_ker_wTil_le_fixV D h) hsum''
  exact (s16fh_delta_le_rk_ker D h).trans hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

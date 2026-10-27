module

public import CFSG.Quasithin.Background.F918Z3A1Qhat

public section

namespace CFSG.Quasithin

theorem caseII_good_module {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)}
    {s : MulAut V} (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G)
    (hAT : A ≤ T') (hAD : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D)
    (hnc : ∃ a ∈ A, ∃ y ∈ D, a * y ≠ y * a) :
    ∃ I : Subgroup V, I ≠ ⊥ ∧ (∀ y ∈ D, ∀ v ∈ I, y v ∈ I) ∧
      (∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) ∧
      (∀ a ∈ A, ∀ v ∈ I, a v ∈ I) ∧ qhatOf (autSub (D ⊔ A) I) < qhatOf G := by
  have _ := hAT
  obtain ⟨r, hr, -, hAr, -⟩ := QhatStar_spec hA
  have hA2 : IsPGroup 2 ↥A := hAr.1.1.isElemAbelian2.isPGroup
  obtain ⟨I, hI, hIA⟩ := Z3A1.exists_irr_inv hZ hA2 hAD
  obtain ⟨hIne, hID, hImin⟩ := Z3A1.isIrr_iff.mp hI
  refine ⟨I, hIne, hID, hImin, hIA, ?_⟩
  by_contra hnlt
  have hq : (r : WithTop ℚ) ≤ qhatOf (autSub (D ⊔ A) I) := by
    rw [← hr]
    exact not_lt.mp hnlt
  have hHG : D ⊔ A ≤ G := sup_le (le_sup_left.trans hZ.DX_le) hAr.1.1.le
  obtain ⟨hHeq, hAH⟩ := Z3A1.QhatStar_of_le hHG le_sup_right hA
  obtain ⟨-, -, hsup, -⟩ := D2_8 hZ.exp (hHeq.trans hr) hAH (Z3A1.le_stabSub_of_inv hIA)
    (Z3A1.commSub_ne_bot hZ hIne hID hAD hnc) hq
  exact Z3A1.false_of_sup_eq_top hZ hI hIA hnc hAD hsup

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.F918Z7bSymm
public import CFSG.Quasithin.Background.F918Z7aTwo
public import CFSG.Quasithin.Background.F918Z2Swap
public import CFSG.Quasithin.Background.F918Z3A1
public import CFSG.Quasithin.Background.F918Z3A2
public import CFSG.Quasithin.Background.F918Z3DNat
public import CFSG.Quasithin.Background.F918Z3CbModel
public import CFSG.Quasithin.Vol2.Ch5ModulesOrthA5
public import CFSG.Quasithin.Background.F918Z3Cg2

public section

namespace CFSG.Quasithin

open scoped Matrix
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

theorem caseII_core
    (h45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hX : Insp5aNonShape)
    {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
    (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G) (hAT : A ≤ T')
    (hAD : ∀ a ∈ A, D.map (MulAut.conj a).toMonoidHom = D)
    (hnc : ∃ a ∈ A, ∃ y ∈ D, a * y ≠ y * a) : Z37Concl D X := by
  have := hZ.nontrivial
  obtain ⟨F, _, _, _, d, β, ρ, σ, ϑ, Q, R, hd, hM, hQ, hR, hform⟩ :=
    hasSqModel_swap_form hZ.exp hZ.comm hZ.irr hZ.swapDX hZ.swapXD
  rcases Nat.lt_or_ge d 3 with hlt | hd3
  · have hd12 : d = 1 ∨ d = 2 := by omega
    rcases hd12 with rfl | rfl
    · exact (z37_dim_ne_one hZ β ρ σ hM).elim
    · exact z37Concl_of_sqModel_two hZ β ρ σ hM
  have hAD' : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D := Z7b.forall_map_conj_eq_iff.1 hAD
  obtain ⟨r, -, -, hAr, -⟩ := QhatStar_spec hA
  have hA2 : IsPGroup 2 ↥A := hAr.1.1.isElemAbelian2.isPGroup
  obtain ⟨I, hIne, hID, hImin, hIA, hq⟩ := caseII_good_module hZ hA hAT hAD' hnc
  have hfaith := Z3A1.faithful hZ hIne hID
  have hnt : ∃ y ∈ D, ∃ v ∈ I, y v ≠ v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, q, hq', hpq⟩ := hZ.nonab
    exact hpq (by rw [hfaith p hp (hcon p hp), hfaith q hq' (hcon q hq')])
  have hq2 : qhatOf (autSub (D ⊔ A) I) < ((2 : ℚ) : WithTop ℚ) := hq.trans_le hZ.qhat
  rcases caseII_shape h45 hF hX hZ.exp hZ.simple hZ.nonab hZ.typeD hZ.sqtkD hA2 hAD' hIne hID
    hImin hIA hnt hq2 with h2 | h3 | h5 | ⟨m, hm, h4⟩
  · exact Z3D.natural_case hZ hd3 β ρ σ hM hIne hID hImin (Or.inl h2)
  · exact Z3D.natural_case hZ hd3 β ρ σ hM hIne hID hImin (Or.inr h3)
  · exact (orth_exclusion hZ hd3 β ρ σ hM ϑ Q R hQ hR hform hIne hID hImin
      (orthMinusData_of_binaryOrthogonalFour hID hfaith le_rfl
          (H13.OrthFour.binaryOrthogonalFour_one_of_alternatingNatural_five h5)) hA hAD).elim
  · exact (orth_exclusion hZ hd3 β ρ σ hM ϑ Q R hQ hR hform hIne hID hImin
      (orthMinusData_of_binaryOrthogonalFour hID hfaith hm h4) hA hAD).elim

end CFSG.Quasithin

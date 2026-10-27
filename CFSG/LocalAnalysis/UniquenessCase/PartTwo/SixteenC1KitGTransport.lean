module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGCodes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitBTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] Multiplicative.mul Multiplicative.semigroup Multiplicative.commSemigroup
attribute [-instance] Multiplicative.mulOneClass Multiplicative.monoid Multiplicative.commMonoid
attribute [-instance] Multiplicative.divInvMonoid Multiplicative.divisionMonoid
attribute [-instance] Multiplicative.divisionCommMonoid Multiplicative.group

theorem s16c1g_omega0_plane (Pa : AddSubgroup V₀) (h4 : Nat.card Pa = 4)
    (hsing : ∀ v ∈ Pa, qModel true v = 0) :
    ∃ E : Subgroup (V₀ ≃ₗ[ZMod 2] V₀), E ≤ Ω₀ true ∧ IsPGroup 3 E ∧ ¬ IsCyclic E ∧
      ∀ g ∈ E, ∀ v ∈ Pa, g v ∈ Pa := by
  obtain ⟨a, b, ha, hb, hpl, hPa⟩ := s16c1g_exists_codes Pa h4 hsing
  obtain ⟨p, -, hgood, hstab⟩ := s16c1g_exists_cand ha hb hpl
  obtain ⟨hle, hpg, hnc⟩ := s16c1g_E_spec hgood
  obtain ⟨-, -, h1, h2, -⟩ := s16c1g_goodE_spec hgood
  simp only [s16c1g_stabE, Bool.and_eq_true] at hstab
  refine ⟨s16c1g_E p, hle, hpg, hnc, fun g hg v hv => ?_⟩
  exact (hPa _).2 (s16c1g_closure_stable (s16c1g_plane a b) h1 h2
    (s16c1g_stabPlane_spec hstab.1) (s16c1g_stabPlane_spec hstab.2) g hg v ((hPa v).1 hv))

theorem omegaPlaneE9_model : OmegaPlaneE9 s16c1b_ΩM := by
  intro P hP4 hP960
  let Pa : AddSubgroup V₀ := Subgroup.toAddSubgroup' P
  have hPa4 : Nat.card Pa = 4 := by
    rw [← hP4]
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))
  have hsing : ∀ v ∈ Pa, qModel true v = 0 := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]
      exact QuadraticMap.map_zero _
    · have hvP : Multiplicative.ofAdd v ∈ P := (Subgroup.mem_toAddSubgroup' P v).1 hv
      have hne : (Multiplicative.ofAdd v : Multiplicative V₀) ≠ 1 := fun h => hv0 (by simpa using h)
      have h1 := (s16c1b_card_ptCent_eq_960_iff hne).1 (hP960 _ hvP hne)
      simpa using h1
  obtain ⟨E, hEΩ, hE3, hEnc, hEst⟩ := s16c1g_omega0_plane Pa hPa4 hsing
  refine ⟨E.map s16c1b_κ, Subgroup.map_mono hEΩ, hE3.map _, ?_, ?_⟩
  · intro hc
    exact hEnc ((Subgroup.equivMapOfInjective E s16c1b_κ s16c1b_κ_injective).isCyclic.2 hc)
  · rintro - ⟨g, hg, rfl⟩ u hu
    have h1 : Multiplicative.toAdd u ∈ Pa := (Subgroup.mem_toAddSubgroup' P _).2 (by simpa using hu)
    have h2 := hEst g hg _ h1
    have h3 : s16c1b_κ g u = Multiplicative.ofAdd (g (Multiplicative.toAdd u)) :=
      s16c1b_κ_apply g (Multiplicative.toAdd u)
    rw [h3]
    exact (Subgroup.mem_toAddSubgroup' P _).1 h2

private lemma s16c1g_congr_apply {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    (φ : MulAut W) (x : W) : MulAut.congr e φ (e x) = e (φ x) := by
  simp [MulAut.congr, MulAut.congr_apply, MulEquiv.trans_apply]

private lemma s16c1g_stabilizer_map_congr {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') (w : W) :
    (MulAction.stabilizer (MulAut W) w).map (MulAut.congr e).toMonoidHom =
      MulAction.stabilizer (MulAut W') (e w) := by
  ext φ
  rw [Subgroup.mem_map_equiv, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    MulAut.smul_def, MulAut.smul_def]
  constructor
  · intro h
    simpa [MulAut.congr, MulEquiv.trans_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa [MulAut.congr, MulEquiv.trans_apply] using h

private theorem s16c1g_ptCent_map_congr {W W' : Type} [CommGroup W] [CommGroup W']
    (e : W ≃* W') (H : Subgroup (MulAut W)) (w : W) :
    ptCent (H.map (MulAut.congr e).toMonoidHom) (e w) =
      (ptCent H w).map (MulAut.congr e).toMonoidHom := by
  rw [ptCent, ptCent, Subgroup.map_inf _ _ _ (MulAut.congr e).injective,
    s16c1g_stabilizer_map_congr e w]

theorem omegaPlaneE9_congr {W W' : Type} [CommGroup W] [CommGroup W'] (e : W ≃* W')
    {H : Subgroup (MulAut W)} (h : OmegaPlaneE9 (H.map (MulAut.congr e).toMonoidHom)) :
    OmegaPlaneE9 H := by
  intro P hP4 hP960
  let c : MulAut W →* MulAut W' := (MulAut.congr e).toMonoidHom
  let s : MulAut W' →* MulAut W := (MulAut.congr e).symm.toMonoidHom
  have hs_inj : Function.Injective s := (MulAut.congr e).symm.injective
  have hsc : s.comp c = MonoidHom.id (MulAut W) := by ext φ; simp [s, c]
  have hHmap : (H.map c).map s = H := by
    rw [Subgroup.map_map, hsc, Subgroup.map_id]
  have hP'4 : Nat.card (P.map e.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact hP4
  have hP'960 : ∀ w' ∈ P.map e.toMonoidHom, w' ≠ 1 →
      Nat.card (ptCent (H.map c) w') = 960 := by
    rintro - ⟨w, hw, rfl⟩ hw1
    have hw1' : w ≠ 1 := fun h1 => hw1 (by rw [h1, map_one])
    change Nat.card (ptCent (H.map c) (e w)) = 960
    rw [s16c1g_ptCent_map_congr e H w,
      Subgroup.card_map_of_injective (f := c) (MulAut.congr e).injective]
    exact hP960 w hw hw1'
  obtain ⟨E', hE'le, hE'P, hE'nc, hE'st⟩ := h (P.map e.toMonoidHom) hP'4 hP'960
  refine ⟨E'.map s, ?_, hE'P.map s, ?_, ?_⟩
  · have h1 := Subgroup.map_mono (f := s) hE'le
    rwa [hHmap] at h1
  · intro hc
    exact hE'nc ((Subgroup.equivMapOfInjective E' s hs_inj).isCyclic.2 hc)
  · rintro - ⟨x', hx', rfl⟩ u hu
    obtain ⟨v, hv, hvx⟩ := hE'st x' hx' (e u) ⟨u, hu, rfl⟩
    have h2 : e (s x' u) = x' (e u) := by
      have h3 := s16c1g_congr_apply e (s x') u
      have h4 : MulAut.congr e (s x') = x' := by
        change MulAut.congr e ((MulAut.congr e).symm x') = x'
        exact MulEquiv.apply_symm_apply (MulAut.congr e) x'
      rw [h4] at h3
      exact h3.symm
    have h5 : s x' u = v := e.injective (by rw [h2]; exact hvx.symm)
    rw [h5]
    exact hv

theorem omegaKitG_holds : OmegaKitG := by
  intro W _ _ H hH
  obtain ⟨β, hβ⟩ := natOmegaMinus_exists_model hH
  have hmap := s16c1b_map_congr_eq hβ
  exact omegaPlaneE9_congr β
    (by have h' := omegaPlaneE9_model; rw [← hmap] at h'; exact h')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoModel
public import CFSG.Quasithin.Vol2.F48GenGeom

public noncomputable section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen
  CFSG.Quasithin.H13.F431.F45 CFSG.RuF45 CFSG.TitsF46

variable
  (h : Certificates.titsGeoFacts)

@[expose] def titsE : titsSetting.ι.Γ ≃ Vtx := (tits_geometry h).choose

theorem titsE_xv : titsE h titsSetting.ι.xv = Sum.inl 0 := (tits_geometry h).choose_spec.1

theorem titsE_lv : titsE h titsSetting.ι.lv = Sum.inr 0 := (tits_geometry h).choose_spec.2.1

theorem titsE_smul (y : ↥titsD) (a : titsSetting.ι.Γ) :
    titsE h (phiD y • a) = y • titsE h a := (tits_geometry h).choose_spec.2.2.1 y a

theorem titsE_adj (a b : titsSetting.ι.Γ) :
    titsSetting.ι.graph.Adj a b ↔ octGraph.Adj (titsE h a) (titsE h b) :=
  (tits_geometry h).choose_spec.2.2.2.1 a b

theorem titsE_inl (z : Pt titsSetting.ι) : ∃ m : Fin 1755, titsE h (Sum.inl z) = Sum.inl m := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₀ (G₂ := titsSetting.ι.φ2.range) z
  obtain ⟨y, rfl⟩ := phiD_surjective g
  have h1 := titsE_smul h y (CosetGeom.γ₀ _ _ _)
  refine ⟨y.1 0, ?_⟩
  rw [show (Sum.inl z : titsSetting.ι.Γ) = phiD y • CosetGeom.γ₀ _ _ _ from hg.symm, h1]
  show _ • titsE h titsSetting.ι.xv = _
  rw [titsE_xv, dsmul_inl]

theorem titsE_inr (w : titsSetting.ι.G0 ⧸
    titsSetting.ι.φ2.range.subgroupOf (titsSetting.ι.φ1.range ⊔ titsSetting.ι.φ2.range)) :
    ∃ k : Fin 2925, titsE h (Sum.inr w) = Sum.inr k := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₁ (G₁ := titsSetting.ι.φ1.range) w
  obtain ⟨y, rfl⟩ := phiD_surjective g
  have h1 := titsE_smul h y (CosetGeom.γ₁ _ _ _)
  refine ⟨titsLineHom (Subgroup.inclusion titsD_le_titsA y) 0, ?_⟩
  rw [show (Sum.inr w : titsSetting.ι.Γ) = phiD y • CosetGeom.γ₁ _ _ _ from hg.symm, h1]
  show _ • titsE h titsSetting.ι.lv = _
  rw [titsE_lv, dsmul_inr]

@[expose] def titsKappaF (z : Pt titsSetting.ι) : Fin 1755 := (titsE_inl h z).choose

theorem titsE_kappaF (z : Pt titsSetting.ι) :
    titsE h (Sum.inl z) = Sum.inl (titsKappaF h z) := (titsE_inl h z).choose_spec

theorem titsKappaF_injective : Function.Injective (titsKappaF h) := by
  intro z z' hzz
  have := (titsE h).injective ((titsE_kappaF h z).trans
    ((congrArg Sum.inl hzz).trans (titsE_kappaF h z').symm))
  exact Sum.inl_injective this

theorem titsKappaF_surjective : Function.Surjective (titsKappaF h) := by
  intro m
  rcases hv : (titsE h).symm (Sum.inl m) with z | w
  · refine ⟨z, ?_⟩
    have := titsE_kappaF h z
    rw [← hv, Equiv.apply_symm_apply] at this
    exact (Sum.inl_injective this).symm
  · obtain ⟨k, hk⟩ := titsE_inr h w
    have := congrArg (titsE h) hv
    rw [Equiv.apply_symm_apply, hk] at this
    exact absurd this Sum.inl_ne_inr

@[expose] def titsKappa : Pt titsSetting.ι ≃ Fin 1755 :=
  Equiv.ofBijective (titsKappaF h) ⟨titsKappaF_injective h, titsKappaF_surjective h⟩

theorem titsE_kappa (z : Pt titsSetting.ι) :
    titsE h (Sum.inl z) = Sum.inl (titsKappa h z) := titsE_kappaF h z

theorem titsKappa_smul (g : titsSetting.ι.G0) (z : Pt titsSetting.ι) :
    titsKappa h (g • z) = toPermD g (titsKappa h z) := by
  obtain ⟨y, rfl⟩ := phiD_surjective g
  have h1 := titsE_smul h y (Sum.inl z)
  rw [CosetGeom.smul_inl, titsE_kappa, titsE_kappa, dsmul_inl] at h1
  rw [toPermD_phiD]
  exact Sum.inl_injective h1

include h in
theorem toPermD_injective :
    Function.Injective (MulAction.toPermHom titsSetting.ι.G0 (Pt titsSetting.ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨y, rfl⟩ := phiD_surjective g
  have hy : y.1 = 1 := by
    refine Equiv.ext fun m => ?_
    obtain ⟨z, rfl⟩ := (titsKappa h).surjective m
    have h1 := titsKappa_smul h (phiD y) z
    have h2 := congrArg (fun σ : Equiv.Perm (Pt titsSetting.ι) => σ z) hg
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at h2
    rw [h2, toPermD_phiD] at h1
    exact h1.symm
  have : y = 1 := Subtype.ext hy
  rw [this, map_one]

theorem titsKappa_near (z : Pt titsSetting.ι) :
    Near 8 titsSetting.ι z ↔ octGraph.dist (Sum.inl 0) (Sum.inl (titsKappa h z)) ≤ 6 := by
  let iso : titsSetting.ι.graph ≃g octGraph := ⟨titsE h, fun {a b} => (titsE_adj h a b).symm⟩
  have hd := iso_dist iso titsSetting.ι.xv (Sum.inl z)
  have hd' : titsSetting.ι.graph.dist titsSetting.ι.xv (Sum.inl z) =
      octGraph.dist (Sum.inl 0) (Sum.inl (titsKappa h z)) := by
    rw [← hd]
    change octGraph.dist (titsE h titsSetting.ι.xv) (titsE h (Sum.inl z)) = _
    rw [titsE_xv, titsE_kappa]
  change titsSetting.ι.graph.dist titsSetting.ι.xv (Sum.inl z) ≤ 8 - 2 ↔ _
  rw [hd']

end CFSG.Quasithin.TitsGeo

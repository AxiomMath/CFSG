module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Geom
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Ln2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F45Poly2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Wrd

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.H13.F431.F45
  CFSG.Quasithin.H13.F431.U42.F48

section Model

theorem u42_exists_equiv :
    ∃ e : u42Setting.ι.Γ ≃ Vtx, e u42Setting.ι.xv = Sum.inl 0 ∧
    e u42Setting.ι.lv = Sum.inr 0 ∧ (∀ (y : Y) (a : u42Setting.ι.Γ), e (toG0 y • a) = y • e a) ∧
    ∀ a b : u42Setting.ι.Γ, u42Setting.ι.graph.Adj a b ↔ incGraph.Adj (e a) (e b) := by
  have f₁ := modelBase_pt.flag (by rw [card_nbrs_inl]) u42XDatum.adj12
  have f₂ := modelBase_ln.flag (by rw [card_nbrs_inr]; decide) u42XDatum.adj12.symm
  exact u42XDatum.exists_equiv (cov_of_flags isGenPolygon_incGraph.connected f₁ f₂) f₁

@[expose] noncomputable def u42E :
    u42Setting.ι.Γ ≃ Vtx := (u42_exists_equiv).choose


theorem u42E_xv : u42E u42Setting.ι.xv = Sum.inl 0 := (u42_exists_equiv).choose_spec.1

theorem u42E_smul (y : Y) (a : u42Setting.ι.Γ) : u42E (toG0 y • a) = y • u42E a :=
  (u42_exists_equiv).choose_spec.2.2.1 y a

theorem u42E_adj (a b : u42Setting.ι.Γ) :
    u42Setting.ι.graph.Adj a b ↔ incGraph.Adj (u42E a) (u42E b) :=
  (u42_exists_equiv).choose_spec.2.2.2 a b

@[expose] noncomputable def stdG0 : u42Setting.ι.G0 →* P45 := Xs.subtype.comp eG.symm.toMonoidHom

theorem stdG0_eG (y : Y) : stdG0 (eG y) = (y : P45) := by
  simp [stdG0]

theorem stdG0_injective : Function.Injective stdG0 := by
  intro a b h
  have : eG.symm a = eG.symm b := Subtype.ext h
  exact eG.symm.injective this

theorem u42E_inl (z : Pt u42Setting.ι) : ∃ m : Fin 45, u42E (Sum.inl z) = Sum.inl m := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₀ (G₂ := u42Setting.ι.φ2.range) z
  have h := u42E_smul (eG.symm g) (CosetGeom.γ₀ _ _ _)
  rw [show toG0 (eG.symm g) = g from eG.apply_symm_apply g] at h
  refine ⟨(eG.symm g : P45) 0, ?_⟩
  rw [show (Sum.inl z : u42Setting.ι.Γ) = g • CosetGeom.γ₀ _ _ _ from hg.symm, h]
  show _ • u42E u42Setting.ι.xv = _
  rw [u42E_xv, Sum.smul_inl]
  rfl

theorem u42E_lv : u42E u42Setting.ι.lv = Sum.inr 0 := (u42_exists_equiv).choose_spec.2.1

theorem u42E_inr (w : Ln u42Setting.ι) :
    ∃ k : Fin 27, u42E (Sum.inr w) = Sum.inr k := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₁ (G₁ := u42Setting.ι.φ1.range) w
  have h := u42E_smul (eG.symm g) (CosetGeom.γ₁ _ _ _)
  rw [show toG0 (eG.symm g) = g from eG.apply_symm_apply g] at h
  refine ⟨(eG.symm g) • (0 : Fin 27), ?_⟩
  rw [show (Sum.inr w : u42Setting.ι.Γ) = g • CosetGeom.γ₁ _ _ _ from hg.symm, h]
  show _ • u42E u42Setting.ι.lv = _
  rw [u42E_lv, Sum.smul_inr]

@[expose] noncomputable def u42KappaF (z : Pt u42Setting.ι) : Fin 45 := (u42E_inl z).choose

theorem u42E_kappaF (z : Pt u42Setting.ι) : u42E (Sum.inl z) = Sum.inl (u42KappaF z) :=
  (u42E_inl z).choose_spec

theorem u42KappaF_injective : Function.Injective u42KappaF := by
  intro z z' h
  have := u42E.injective ((u42E_kappaF z).trans ((congrArg Sum.inl h).trans (u42E_kappaF z').symm))
  exact Sum.inl_injective this

theorem u42KappaF_surjective : Function.Surjective u42KappaF := by
  intro m
  rcases hv : u42E.symm (Sum.inl m) with z | w
  · refine ⟨z, ?_⟩
    have := u42E_kappaF z
    rw [← hv, Equiv.apply_symm_apply] at this
    exact (Sum.inl_injective this).symm
  · obtain ⟨k, hk⟩ := u42E_inr w
    have := congrArg u42E hv
    rw [Equiv.apply_symm_apply, hk] at this
    exact absurd this Sum.inl_ne_inr

@[expose] noncomputable def u42Kappa : Pt u42Setting.ι ≃ Fin 45 :=
  Equiv.ofBijective u42KappaF ⟨u42KappaF_injective, u42KappaF_surjective⟩

theorem u42Kappa_smul (g : u42Setting.ι.G0) (z : Pt u42Setting.ι) :
    u42Kappa (g • z) = stdG0 g (u42Kappa z) := by
  have h := u42E_smul (eG.symm g) (Sum.inl z)
  rw [show toG0 (eG.symm g) = g from eG.apply_symm_apply g, CosetGeom.smul_inl, u42E_kappaF,
    u42E_kappaF] at h
  have h2 : Sum.inl (u42KappaF (g • z)) = ((eG.symm g : Y) • Sum.inl (u42KappaF z) : Vtx) := h
  rw [Sum.smul_inl] at h2
  exact Sum.inl_injective h2

theorem near_of_coll {z : Pt u42Setting.ι} (h : f48Coll0 (u42Kappa z)) : Near u42Setting.ι z := by
  obtain ⟨k, hk, h0, hm⟩ := h
  have hk' : (⟨k, hk⟩ : Fin 27) = ⟨k, hk⟩ := rfl
  have a1 : incGraph.Adj (Sum.inl 0) (Sum.inr ⟨k, hk⟩) := by
    rw [adj_inl_inr]
    exact List.contains_iff_mem.1 h0
  have a2 : incGraph.Adj (Sum.inr ⟨k, hk⟩) (Sum.inl (u42Kappa z)) := by
    rw [adj_inr_inl]
    exact List.contains_iff_mem.1 hm
  have b1 : u42Setting.ι.graph.Adj u42Setting.ι.xv (u42E.symm (Sum.inr ⟨k, hk⟩)) := by
    rw [u42E_adj, u42E_xv, Equiv.apply_symm_apply]
    exact a1
  have b2 : u42Setting.ι.graph.Adj (u42E.symm (Sum.inr ⟨k, hk⟩)) (Sum.inl z) := by
    rw [u42E_adj, Equiv.apply_symm_apply, u42E_kappaF]
    exact a2
  have := SimpleGraph.dist_le (SimpleGraph.Walk.cons b1 (SimpleGraph.Walk.cons b2
    SimpleGraph.Walk.nil))
  exact this

end Model

end CFSG.Quasithin.H13.F431.U42

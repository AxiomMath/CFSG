module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuFinal
public import CFSG.Quasithin.Vol2.F48GenGeom
public import CFSG.Quasithin.Vol2.TwoF4F48Spec
public import Certificates.Certificate4160

public section

namespace CFSG.Quasithin.H13.TwoF4F48

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Quasithin.RuType
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.H13.F48Gen
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.TwoF4F48

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

section Model


theorem twoF4_exists_equiv : ∃ e : twoF4Setting.ι.Γ ≃ Vtx, e twoF4Setting.ι.xv = Sum.inl 0 ∧
    e twoF4Setting.ι.lv = Sum.inr 0 ∧
    (∀ (y : ↥TA) (a : twoF4Setting.ι.Γ), e (phiA y • a) = y • e a) ∧
    ∀ a b : twoF4Setting.ι.Γ, twoF4Setting.ι.graph.Adj a b ↔ octGraph.Adj (e a) (e b) := by
  obtain ⟨hpoly, -, hloc⟩ := Certificates.certificate4160
  obtain ⟨⟨b₁, w₁₀, w₁₁, Fg₁, L₁, D₁⟩, ⟨b₂, w₂₀, w₂₁, Fg₂, L₂, D₂⟩, -⟩ := hloc
  have h00' : (0 : Fin 1755) ∈ titsLine (0 : Fin 2925) :=
    (RuType.J47.titsLine_mem_iff 0 0).2 RuType.J47.onLine_0_0
  have M₁ := modelBase_of_local hpoly.connected D₁
  have M₂ := modelBase_of_local hpoly.connected D₂
  have n1 := D₁.card_N
  have n2 := D₂.card_N
  have X := xdatum_oct h00'
  have f₁ := M₁.flag (by omega) X.adj12
  have f₂ := M₂.flag (by omega) X.adj12.symm
  exact X.exists_equiv (cov_of_flags hpoly.connected f₁ f₂) f₁

@[expose] noncomputable def twoF4E : twoF4Setting.ι.Γ ≃ Vtx := twoF4_exists_equiv.choose

theorem twoF4E_xv : twoF4E twoF4Setting.ι.xv = Sum.inl 0 := twoF4_exists_equiv.choose_spec.1

theorem twoF4E_lv : twoF4E twoF4Setting.ι.lv = Sum.inr 0 := twoF4_exists_equiv.choose_spec.2.1

theorem twoF4E_smul (y : ↥TA) (a : twoF4Setting.ι.Γ) : twoF4E (phiA y • a) = y • twoF4E a :=
  twoF4_exists_equiv.choose_spec.2.2.1 y a

theorem twoF4E_adj (a b : twoF4Setting.ι.Γ) :
    twoF4Setting.ι.graph.Adj a b ↔ octGraph.Adj (twoF4E a) (twoF4E b) :=
  twoF4_exists_equiv.choose_spec.2.2.2 a b

theorem twoF4E_inl (z : Pt twoF4Setting.ι) : ∃ m : Fin 1755, twoF4E (Sum.inl z) = Sum.inl m := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₀ (G₂ := twoF4Setting.ι.φ2.range) z
  obtain ⟨y, rfl⟩ := phiA_surjective g
  have h := twoF4E_smul y (CosetGeom.γ₀ _ _ _)
  refine ⟨y.1 0, ?_⟩
  rw [show (Sum.inl z : twoF4Setting.ι.Γ) = phiA y • CosetGeom.γ₀ _ _ _ from hg.symm, h]
  show _ • twoF4E twoF4Setting.ι.xv = _
  rw [twoF4E_xv, smul_inl]

theorem twoF4E_inr (w : twoF4Setting.ι.G0 ⧸
      twoF4Setting.ι.φ2.range.subgroupOf (twoF4Setting.ι.φ1.range ⊔ twoF4Setting.ι.φ2.range)) :
    ∃ k : Fin 2925, twoF4E (Sum.inr w) = Sum.inr k := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₁ (G₁ := twoF4Setting.ι.φ1.range) w
  obtain ⟨y, rfl⟩ := phiA_surjective g
  have h := twoF4E_smul y (CosetGeom.γ₁ _ _ _)
  refine ⟨titsLineHom y 0, ?_⟩
  rw [show (Sum.inr w : twoF4Setting.ι.Γ) = phiA y • CosetGeom.γ₁ _ _ _ from hg.symm, h]
  show _ • twoF4E twoF4Setting.ι.lv = _
  rw [twoF4E_lv, smul_inr]

@[expose] noncomputable def twoF4KappaF (z : Pt twoF4Setting.ι) : Fin 1755 :=
  (twoF4E_inl z).choose

theorem twoF4E_kappaF (z : Pt twoF4Setting.ι) :
    twoF4E (Sum.inl z) = Sum.inl (twoF4KappaF z) :=
  (twoF4E_inl z).choose_spec

theorem twoF4KappaF_injective : Function.Injective twoF4KappaF := by
  intro z z' h
  have := twoF4E.injective ((twoF4E_kappaF z).trans
    ((congrArg Sum.inl h).trans (twoF4E_kappaF z').symm))
  exact Sum.inl_injective this

theorem twoF4KappaF_surjective : Function.Surjective twoF4KappaF := by
  intro m
  rcases hv : twoF4E.symm (Sum.inl m) with z | w
  · refine ⟨z, ?_⟩
    have := twoF4E_kappaF z
    rw [← hv, Equiv.apply_symm_apply] at this
    exact (Sum.inl_injective this).symm
  · obtain ⟨k, hk⟩ := twoF4E_inr w
    have := congrArg twoF4E hv
    rw [Equiv.apply_symm_apply, hk] at this
    exact absurd this Sum.inl_ne_inr

@[expose] noncomputable def twoF4Kappa : Pt twoF4Setting.ι ≃ Fin 1755 :=
  Equiv.ofBijective twoF4KappaF ⟨twoF4KappaF_injective, twoF4KappaF_surjective⟩

theorem twoF4E_kappa (z : Pt twoF4Setting.ι) :
    twoF4E (Sum.inl z) = Sum.inl (twoF4Kappa z) :=
  twoF4E_kappaF z

theorem kappa_smul (g : twoF4Setting.ι.G0) (z : Pt twoF4Setting.ι) :
    twoF4Kappa (g • z) = toPerm g (twoF4Kappa z) := by
  obtain ⟨y, rfl⟩ := phiA_surjective g
  have h := twoF4E_smul y (Sum.inl z)
  rw [CosetGeom.smul_inl, twoF4E_kappa, twoF4E_kappa, smul_inl] at h
  rw [toPerm_phiA]
  exact Sum.inl_injective h

theorem toPerm_injective :
    Function.Injective (MulAction.toPermHom twoF4Setting.ι.G0 (Pt twoF4Setting.ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨y, rfl⟩ := phiA_surjective g
  have hy : y.1 = 1 := by
    refine Equiv.ext fun m => ?_
    obtain ⟨z, rfl⟩ := twoF4Kappa.surjective m
    have h1 := kappa_smul (phiA y) z
    have h2 := congrArg (fun σ : Equiv.Perm (Pt twoF4Setting.ι) => σ z) hg
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.one_apply] at h2
    rw [h2, toPerm_phiA] at h1
    exact h1.symm
  have : y = 1 := Subtype.ext hy
  rw [this, map_one]

theorem near_iff (z : Pt twoF4Setting.ι) :
    Near 8 twoF4Setting.ι z ↔ octGraph.dist (Sum.inl 0) (Sum.inl (twoF4Kappa z)) ≤ 6 := by
  let iso : twoF4Setting.ι.graph ≃g octGraph := ⟨twoF4E, fun {a b} => (twoF4E_adj a b).symm⟩
  have hd := iso_dist iso twoF4Setting.ι.xv (Sum.inl z)
  have hd' : twoF4Setting.ι.graph.dist twoF4Setting.ι.xv (Sum.inl z) =
      octGraph.dist (Sum.inl 0) (Sum.inl (twoF4Kappa z)) := by
    rw [← hd]
    change octGraph.dist (twoF4E twoF4Setting.ι.xv) (twoF4E (Sum.inl z)) = _
    rw [twoF4E_xv, twoF4E_kappa]
  change twoF4Setting.ι.graph.dist twoF4Setting.ι.xv (Sum.inl z) ≤ 8 - 2 ↔ _
  rw [hd']

end Model

end CFSG.Quasithin.H13.TwoF4F48

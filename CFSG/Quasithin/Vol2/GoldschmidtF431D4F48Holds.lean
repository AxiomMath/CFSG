module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48D4
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Concl
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Kappa
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Faith
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexGraph

public noncomputable section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F48Gen CFSG.D4Hex
  CFSG.Quasithin.H13.F431.F45 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.Quasithin.TitsGeo (TitsModel)

structure D4Geom where
  e : d4Setting.ι.Γ ≃ HexVtx
  e_xv : e d4Setting.ι.xv = Sum.inl pt0
  e_lv : e d4Setting.ι.lv = Sum.inr 0
  e_smul : ∀ (g : D) (a : d4Setting.ι.Γ), e (d4Phi g • a) = g • e a
  e_adj : ∀ a b : d4Setting.ι.Γ, d4Setting.ι.graph.Adj a b ↔ hexGraph.Adj (e a) (e b)
  dist_lay : ∀ p : Fin 819, hexGraph.dist (Sum.inl pt0) (Sum.inl p) = lay0[(p : ℕ)]!

namespace D4Geom

variable (Gm : D4Geom)

theorem e_inl (z : Pt d4Setting.ι) : ∃ m : Fin 819, Gm.e (Sum.inl z) = Sum.inl m := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₀ (G₂ := d4Setting.ι.φ2.range) z
  obtain ⟨y, rfl⟩ := d4Phi_surjective g
  have h1 := Gm.e_smul y (CosetGeom.γ₀ _ _ _)
  refine ⟨act y pt0, ?_⟩
  rw [show (Sum.inl z : d4Setting.ι.Γ) = d4Phi y • CosetGeom.γ₀ _ _ _ from hg.symm, h1]
  show _ • Gm.e d4Setting.ι.xv = _
  rw [Gm.e_xv]
  rfl

theorem e_inr (w : d4Setting.ι.G0 ⧸
    d4Setting.ι.φ2.range.subgroupOf (d4Setting.ι.φ1.range ⊔ d4Setting.ι.φ2.range)) :
    ∃ k : Fin 2457, Gm.e (Sum.inr w) = Sum.inr k := by
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_γ₁ (G₁ := d4Setting.ι.φ1.range) w
  obtain ⟨y, rfl⟩ := d4Phi_surjective g
  have h1 := Gm.e_smul y (CosetGeom.γ₁ _ _ _)
  refine ⟨y • (0 : Fin 2457), ?_⟩
  rw [show (Sum.inr w : d4Setting.ι.Γ) = d4Phi y • CosetGeom.γ₁ _ _ _ from hg.symm, h1]
  show _ • Gm.e d4Setting.ι.lv = _
  rw [Gm.e_lv]
  rfl

@[expose] noncomputable def κF (z : Pt d4Setting.ι) : Fin 819 := (Gm.e_inl z).choose

theorem e_κF (z : Pt d4Setting.ι) : Gm.e (Sum.inl z) = Sum.inl (Gm.κF z) :=
  (Gm.e_inl z).choose_spec

theorem κF_injective : Function.Injective Gm.κF := by
  intro z z' hzz
  have := Gm.e.injective ((Gm.e_κF z).trans ((congrArg Sum.inl hzz).trans (Gm.e_κF z').symm))
  exact Sum.inl_injective this

theorem κF_surjective : Function.Surjective Gm.κF := by
  intro m
  rcases hv : Gm.e.symm (Sum.inl m) with z | w
  · refine ⟨z, ?_⟩
    have := Gm.e_κF z
    rw [← hv, Equiv.apply_symm_apply] at this
    exact (Sum.inl_injective this).symm
  · obtain ⟨k, hk⟩ := Gm.e_inr w
    have := congrArg Gm.e hv
    rw [Equiv.apply_symm_apply, hk] at this
    exact absurd this Sum.inl_ne_inr

@[expose] noncomputable def κ : Pt d4Setting.ι ≃ Fin 819 :=
  Equiv.ofBijective Gm.κF ⟨Gm.κF_injective, Gm.κF_surjective⟩

theorem e_κ (z : Pt d4Setting.ι) : Gm.e (Sum.inl z) = Sum.inl (Gm.κ z) := Gm.e_κF z

theorem κ_phi (x : D) (z : Pt d4Setting.ι) : Gm.κ (d4Phi x • z) = act x (Gm.κ z) := by
  have h1 := Gm.e_smul x (Sum.inl z)
  rw [CosetGeom.smul_inl, Gm.e_κ, Gm.e_κ] at h1
  exact Sum.inl_injective h1

theorem κ_one : Gm.κ ((1 : d4Setting.ι.G0) : Pt d4Setting.ι) = pt0 := by
  have h := Gm.e_xv
  have h2 : Gm.e (Sum.inl ((1 : d4Setting.ι.G0) : Pt d4Setting.ι)) = Sum.inl pt0 := h
  rw [Gm.e_κ] at h2
  exact Sum.inl_injective h2

theorem κ_near (z : Pt d4Setting.ι) :
    Near d4Setting.m d4Setting.ι z ↔ lay0[((Gm.κ z : Fin 819) : ℕ)]! ≤ 4 := by
  let iso : d4Setting.ι.graph ≃g hexGraph := ⟨Gm.e, fun {a b} => (Gm.e_adj a b).symm⟩
  have hd := iso_dist iso d4Setting.ι.xv (Sum.inl z)
  have hd' : d4Setting.ι.graph.dist d4Setting.ι.xv (Sum.inl z) =
      lay0[((Gm.κ z : Fin 819) : ℕ)]! := by
    rw [← hd]
    show hexGraph.dist (Gm.e d4Setting.ι.xv) (Gm.e (Sum.inl z)) = _
    rw [Gm.e_xv, Gm.e_κ]
    exact Gm.dist_lay _
  show d4Setting.ι.graph.dist d4Setting.ι.xv (Sum.inl z) ≤ 6 - 2 ↔ _
  rw [hd']

end D4Geom

section Wiring


@[expose] noncomputable def f48ToD : d4Setting.ι.G0 →* D where
  toFun := d4ToD
  map_one' := rfl
  map_mul' _ _ := rfl

theorem f48ToD_phi (x : D) : f48ToD (d4Phi x) = x := rfl

theorem f48ToD_injective : Function.Injective f48ToD := by
  intro k k' h
  obtain ⟨x, rfl⟩ := d4Phi_surjective k
  obtain ⟨x', rfl⟩ := d4Phi_surjective k'
  rw [f48ToD_phi, f48ToD_phi] at h
  rw [h]

@[expose] noncomputable def d4Rho1 : d4Setting.α.G1 →* Equiv.Perm (Fin 819) :=
  act.comp d4H.subtype

@[expose] noncomputable def d4Rho2 : d4Setting.α.G2 →* Equiv.Perm (Fin 819) :=
  act.comp d4N.subtype

theorem f48_smul_xv_iff (k : d4Setting.ι.G0) :
    k • d4Setting.ι.xv = d4Setting.ι.xv ↔ f48ToD k ∈ d4H := by
  rw [show f48ToD k = d4ToD k from rfl, ← mem_range_φ1_iff]
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₀ (G₀ := d4Setting.ι.φ1.range ⊔ d4Setting.ι.φ2.range) le_sup_left] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₀ (G₀ := d4Setting.ι.φ1.range ⊔ d4Setting.ι.φ2.range) le_sup_left]

theorem f48_smul_lv_iff (k : d4Setting.ι.G0) :
    k • d4Setting.ι.lv = d4Setting.ι.lv ↔ f48ToD k ∈ d4N := by
  rw [show f48ToD k = d4ToD k from rfl, ← mem_range_φ2_iff]
  constructor
  · intro h
    have := CosetGeom.mem_stab_of_smul_eq h
    rwa [CosetGeom.stab_γ₁ (G₀ := d4Setting.ι.φ1.range ⊔ d4Setting.ι.φ2.range) le_sup_right] at this
  · intro h
    apply CosetGeom.smul_eq_of_mem_stab
    rwa [CosetGeom.stab_γ₁ (G₀ := d4Setting.ι.φ1.range ⊔ d4Setting.ι.φ2.range) le_sup_right]

end Wiring

namespace D4Geom

variable (Gm : D4Geom)

theorem κ_smul (g : d4Setting.ι.G0) (z : Pt d4Setting.ι) :
    Gm.κ (g • z) = (act.comp f48ToD) g (Gm.κ z) := by
  obtain ⟨x, rfl⟩ := d4Phi_surjective g
  rw [Gm.κ_phi]
  rfl

include Gm in
theorem d4_ptRigid :
    PtRigid d4Setting ⟨d4Word f48NWord, d4_nH⟩ ⟨d4Word f48QWord, d4_qN⟩ f48Order := by
  refine ptRigid_of_fin d4Setting Gm.κ d4Rho1 d4Rho2 lay0 (fun y z => ?_) (fun q z => ?_)
    Gm.κ_near ?_
  · have : f1 (c := d4Setting.ι) y = d4Phi (show ↥d4H from y).1 := rfl
    rw [this, Gm.κ_phi]
    rfl
  · have : f2 (c := d4Setting.ι) q = d4Phi (show ↥d4N from q).1 := rfl
    rw [this, Gm.κ_phi]
    rfl
  · intro π' hB hN hX y
    refine d4_rigid π' (fun x hx hxN => ?_) (fun x hx p hp => ?_) hX y
    · exact hB ⟨x, Subgroup.mem_inf.2 ⟨hx, hxN⟩⟩
    · exact hN ⟨x, hx⟩ p hp

include Gm in
theorem d4_toPerm_injective (hact : Function.Injective act) :
    Function.Injective (MulAction.toPermHom d4Setting.ι.G0 (Pt d4Setting.ι)) :=
  toPerm_injective_of_kappa d4Setting Gm.κ (act.comp f48ToD) Gm.κ_smul
    (hact.comp f48ToD_injective)

include Gm in
theorem d4_hfix : ∀ v : d4Setting.ι.Γ,
    CosetGeom.vtype v = false →
      (∀ b ∈ stv d4Setting.ι d4Setting.ι.xv ⊓ stv d4Setting.ι d4Setting.ι.lv, b • v = v) →
      v = d4Setting.ι.xv :=
  fix_of_kappa d4Setting Gm.κ (act.comp f48ToD) Gm.κ_smul fun w hw => by
    rw [Gm.κ_one]
    refine d4_fixed_point fun x hx => ?_
    have h1 : d4Phi x • d4Setting.ι.xv = d4Setting.ι.xv :=
      (f48_smul_xv_iff _).2 (by rw [f48ToD_phi]; exact (Subgroup.mem_inf.1 hx).1)
    have h2 : d4Phi x • d4Setting.ι.lv = d4Setting.ι.lv :=
      (f48_smul_lv_iff _).2 (by rw [f48ToD_phi]; exact (Subgroup.mem_inf.1 hx).2)
    exact hw (d4Phi x) (Subgroup.mem_inf.2 ⟨MulAction.mem_stabilizer_iff.2 h1,
      MulAction.mem_stabilizer_iff.2 h2⟩)

include Gm in
theorem d4F48
    (hD : IsSimpleGroup D) (M : CFSG.Quasithin.TitsGeo.TitsModel d4Setting.ι 4)
    (hpoly : IsGenPolygon d4Setting.ι.graph 6) (Y : Type) [Group Y] [Finite Y]
    (β : d4Setting.α.Completion Y) (hβ : β.IsFaithful) (hs : β.IsSmall d4Setting.m) :
    d4Setting.F48Concl β :=
  f48Concl_of_rigid d4Setting (k := 4) rfl M hpoly
    (dvd_of_eq (card_d4Setting_Yb.trans rfl : Nat.card d4Setting.Yb = f48Order))
    Gm.d4_ptRigid (Gm.d4_toPerm_injective (act_injective hD)) Gm.d4_hfix rfl Y β hβ hs

end D4Geom

end CFSG.Quasithin.D4Hex

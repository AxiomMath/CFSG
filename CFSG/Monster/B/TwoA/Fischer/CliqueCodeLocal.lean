module

public import CFSG.Monster.B.TwoA.Fischer.CliqueCodeDefs
public import CFSG.Monster.B.TwoA.Unitary.CliqueFiberMain
public import CFSG.Monster.B.Classical.HermitianRankOne
public import CFSG.Monster.B.TwoA.Fischer.CliqueKernel

public section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary
open scoped IsMulCommutative LinearAlgebra.Projectivization

@[expose] noncomputable def lift3L : (Fin 3 → F4) →ₗ[F4] UnitarySix.V where
  toFun := lift3
  map_add' a b := by
    change ofHyp (a + b) 0 = ofHyp a 0 + ofHyp b 0
    rw [ofHyp_add, add_zero]
  map_smul' c a := (lift3_smul c a).symm

@[expose] noncomputable def planeEmb (g : SU frobeniusF4 6) :
    (Fin 3 → F4) →ₗ[F4] UnitarySix.V :=
  (suEquiv g).toLinearMap ∘ₗ lift3L

theorem planeEmb_apply (g : SU frobeniusF4 6) (w : Fin 3 → F4) :
    planeEmb g w = g • lift3 w := rfl

theorem planeEmb_injective (g : SU frobeniusF4 6) : Function.Injective (planeEmb g) :=
  (suEquiv g).injective.comp lift3_injective

theorem planeEmb_mem (g : SU frobeniusF4 6) (w : Fin 3 → F4) : planeEmb g w ∈ smulSub g W0 :=
  smul_mem_smulSub.2 (lift3_mem_W0 w)

theorem range_planeEmb (g : SU frobeniusF4 6) :
    LinearMap.range (planeEmb g) = smulSub g W0 := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact planeEmb_mem g w
  · intro v hv
    rw [mem_smulSub] at hv
    refine ⟨hypA (g⁻¹ • v), ?_⟩
    rw [planeEmb_apply, ← eq_lift3_of_mem_W0 hv, smul_inv_smul]

theorem finrank_comap_planeEmb {g : SU frobeniusF4 6} {A : Submodule F4 UnitarySix.V}
    (hA : A ≤ smulSub g W0) :
    Module.finrank F4 (A.comap (planeEmb g)) = Module.finrank F4 A := by
  have h1 : (A.comap (planeEmb g)).map (planeEmb g) = A := by
    rw [Submodule.map_comap_eq, range_planeEmb, inf_eq_right.2 hA]
  rw [(Submodule.equivMapOfInjective _ (planeEmb_injective g) _).finrank_eq, h1]

theorem finrank_map_planeEmb (g : SU frobeniusF4 6) (A : Submodule F4 (Fin 3 → F4)) :
    Module.finrank F4 (A.map (planeEmb g)) = Module.finrank F4 A :=
  (Submodule.equivMapOfInjective _ (planeEmb_injective g) _).finrank_eq.symm

theorem map_planeEmb_le (g : SU frobeniusF4 6) (A : Submodule F4 (Fin 3 → F4)) :
    A.map (planeEmb g) ≤ smulSub g W0 := by
  rintro _ ⟨w, -, rfl⟩
  exact planeEmb_mem g w

theorem mem_planePts_iff_eW (g : SU frobeniusF4 6) (A : Submodule F4 UnitarySix.V)
    (p : planePts (smulSub g W0)) :
    (p : IsoPt) ∈ planePts A ↔ (eW g p).submodule ≤ A.comap (planeEmb g) := by
  set q : planePts W0 := shiftEquiv g W0 p with hq
  have hqv : (q : IsoPt) = g⁻¹ • (p : IsoPt) := rfl
  have he : eW g p = Projectivization.mk F4 (hypA (q : IsoPt).1.rep) (hypA_rep_ne_zero q.2) :=
    rfl
  rw [he, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_comap, planeEmb_apply, ← eq_lift3_of_mem_W0 q.2, hqv]
  obtain ⟨c, hc⟩ := rep_pt ((smul_ne_zero_iff_ne g⁻¹).mpr (rep_ne_zero p.1))
    (by rw [herm_smul_smul]; exact isIsoPt_of p.1)
  rw [smul_eq_pt g⁻¹ p.1, ← hc, Units.smul_def, smul_comm, smul_inv_smul, mem_planePts]
  exact (Submodule.smul_mem_iff A c.ne_zero).symm

theorem R_eq_rk (q : ℙ F4 (Fin 3 → F4)) : Plane.R q = rk q.rep := rfl

theorem isHerm_R (q : ℙ F4 (Fin 3 → F4)) : IsHerm (Plane.R q) := isHerm_rk _

@[expose] noncomputable def kerEquiv (g : SU frobeniusF4 6) :
    Multiplicative hermSub ≃* kerL (smulSub g W0) :=
  ((MonoidHom.ofInjective unipHom_injective).trans (MulEquiv.subgroupCongr range_unipHom)).trans
    (((kerL W0).equivMapOfInjective _ (MulAut.conj (g : ProjSU)).injective).trans
      (MulEquiv.subgroupCongr (kerL_smulSub g W0).symm))

theorem coe_kerEquiv (g : SU frobeniusF4 6) (x : Multiplicative hermSub) :
    ((kerEquiv g x : kerL _) : ProjSU) = MulAut.conj (g : ProjSU) (unipHom x) := rfl

theorem unipSU_congr {C C' : Matrix (Fin 3) (Fin 3) F4} (hC : IsHerm C) (hC' : IsHerm C')
    (h : C = C') : unipSU C hC = unipSU C' hC' := by
  subst h
  rfl

theorem tPt_eq_kerEquiv (g : SU frobeniusF4 6) (p : planePts (smulSub g W0)) :
    ((kerEquiv g (Multiplicative.ofAdd ⟨Plane.R (eW g p), isHerm_R _⟩) : kerL _) : ProjSU) =
      tPt p := by
  set q : planePts W0 := shiftEquiv g W0 p with hq
  obtain ⟨w, hw, hqw⟩ := planePts_W0_eq q.1 q.2
  have he : eW g p = Projectivization.mk F4 w (ne_zero_of_lift3 hw) := e0_eq_mk q w hw hqw
  have hR : Plane.R (eW g p) = rk w := by
    rw [he, Plane.R_mk]
    rfl
  have h1 : unipHom (Multiplicative.ofAdd ⟨Plane.R (eW g p), isHerm_R _⟩) = tPt q.1 := by
    rw [unipHom_apply, hqw, tPt_lift3]
    exact congrArg _ (unipSU_congr _ _ hR)
  rw [coe_kerEquiv, h1, ← tPt_smul]
  exact congrArg tPt (smul_inv_smul g p.1)

theorem kerEquiv_symm_tPt (g : SU frobeniusF4 6) (p : IsoPt) (hp : p ∈ planePts (smulSub g W0))
    (hp' : tPt p ∈ kerL (smulSub g W0)) :
    (kerEquiv g).symm ⟨tPt p, hp'⟩ =
      Multiplicative.ofAdd ⟨Plane.R (eW g ⟨p, hp⟩), isHerm_R _⟩ := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (tPt_eq_kerEquiv g ⟨p, hp⟩).symm

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem IsFischerSlice.closure_le_sliceStab (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) {u : V} (hu : u ∈ C) :
    Subgroup.closure (lab '' C) ≤ sliceStab act lab Y u := fun _ hx =>
  ⟨(hS.closure_le_ptStab hC.1.1 hC.1.2 hx).1, (hS.closure_le_ptStab hC.1.1 hC.1.2 hx).2 u hu⟩

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u) {C : Set V}

theorem mem_planePts_of_mem (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
    (z : (sliceGraph lab Y).neighborSet u) (hz : (z : V) ∈ C) :
    L.τ z ∈ planePts (smulSub g W0) := by
  rw [← hWe]
  exact (L.mem_img_iff C z).2 hz

@[expose] noncomputable def coordC (g : SU frobeniusF4 6)
    (hWe : L.img C = planePts (smulSub g W0)) (z : C) : ℙ F4 (Fin 3 → F4) :=
  open _root_.Classical in
  if h : (z : V) ∈ (sliceGraph lab Y).neighborSet u then
    eW g ⟨L.τ ⟨z, h⟩, L.mem_planePts_of_mem g hWe ⟨z, h⟩ z.2⟩
  else Classical.arbitrary _

theorem coordC_of_mem (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0)) (z : C)
    (h : (z : V) ∈ (sliceGraph lab Y).neighborSet u) :
    L.coordC g hWe z = eW g ⟨L.τ ⟨z, h⟩, L.mem_planePts_of_mem g hWe ⟨z, h⟩ z.2⟩ := by
  rw [coordC, dite_eq_left h]

theorem coordC_injOn (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0)) {z z' : C}
    (hz : (z : V) ∈ (sliceGraph lab Y).neighborSet u)
    (hz' : (z' : V) ∈ (sliceGraph lab Y).neighborSet u)
    (h : L.coordC g hWe z = L.coordC g hWe z') : z = z' := by
  rw [L.coordC_of_mem g hWe z hz, L.coordC_of_mem g hWe z' hz'] at h
  have h1 := congrArg Subtype.val ((eW g).injective h)
  exact Subtype.ext (congrArg (fun w : (sliceGraph lab Y).neighborSet u => (w : V))
    (L.τ.injective h1))

theorem exists_coordC_eq (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
    (q : ℙ F4 (Fin 3 → F4)) :
    ∃ (z : C) (_ : (z : V) ∈ (sliceGraph lab Y).neighborSet u), L.coordC g hWe z = q := by
  set p := (eW g).symm q
  have hp : (p : IsoPt) ∈ L.img C := by
    rw [hWe]
    exact p.2
  obtain ⟨z₀, hz₀, hz₀p⟩ := hp
  refine ⟨⟨z₀, hz₀⟩, z₀.2, ?_⟩
  rw [L.coordC_of_mem g hWe _ z₀.2]
  have e : (⟨L.τ ⟨((⟨z₀, hz₀⟩ : C) : V), z₀.2⟩,
      L.mem_planePts_of_mem g hWe ⟨_, z₀.2⟩ hz₀⟩ : planePts (smulSub g W0)) = p :=
    Subtype.ext hz₀p
  rw [e, Equiv.apply_symm_apply]

section Labels

variable (hS : IsFischerSlice act lab Y) (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C)
  (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
include hS hC hu

@[expose] noncomputable def kerHom : Subgroup.closure (lab '' C) →* kerL (smulSub g W0) :=
  (L.φ.comp (Subgroup.inclusion (hS.closure_le_sliceStab hC hu))).codRestrict _ fun r =>
    (L.mem_ptStab_iff hS hC hu hWe _).1 (hS.closure_le_ptStab hC.1.1 hC.1.2 r.2)

theorem coe_kerHom (r : Subgroup.closure (lab '' C)) :
    ((L.kerHom hS hC hu g hWe r : kerL _) : ProjSU) =
      L.φ ⟨r, hS.closure_le_sliceStab hC hu r.2⟩ := rfl

@[expose] noncomputable def labHerm :
    Additive (Subgroup.closure (lab '' C)) →+ Matrix (Fin 3) (Fin 3) F4 :=
  hermSub.subtype.comp (MonoidHom.toAdditiveLeft
    ((kerEquiv g).symm.toMonoidHom.comp (L.kerHom hS hC hu g hWe)))

theorem labHerm_apply (x : Additive (Subgroup.closure (lab '' C))) :
    L.labHerm hS hC hu g hWe x =
      (((kerEquiv g).symm (L.kerHom hS hC hu g hWe x.toMul)).toAdd : Matrix (Fin 3) (Fin 3) F4) :=
  rfl

theorem labHerm_eq_zero_iff (x : Additive (Subgroup.closure (lab '' C))) :
    L.labHerm hS hC hu g hWe x = 0 ↔ ((x.toMul : Subgroup.closure (lab '' C)) : S) ∈
      Subgroup.zpowers (lab u) := by
  rw [labHerm_apply, ← L.ker ⟨_, hS.closure_le_sliceStab hC hu (x.toMul).2⟩, ← coe_kerHom,
    ZeroMemClass.coe_eq_zero, toAdd_eq_zero, MulEquiv.map_eq_one_iff, OneMemClass.coe_eq_one]

theorem labHerm_gen (z : C) (hz : (z : V) ∈ (sliceGraph lab Y).neighborSet u) :
    L.labHerm hS hC hu g hWe (Additive.ofMul (cliqueGen z)) = Plane.R (L.coordC g hWe z) := by
  have hmem := L.mem_planePts_of_mem g hWe ⟨z, hz⟩ z.2
  have hφ : L.kerHom hS hC hu g hWe (cliqueGen z) =
      ⟨tPt (L.τ ⟨z, hz⟩), tPt_mem_kerL (isMaxIso_smulSub isMaxIso_W0 g).2 hmem⟩ :=
    Subtype.ext (L.lab_eq ⟨z, hz⟩ _ rfl)
  rw [labHerm_apply, toMul_ofMul, hφ, kerEquiv_symm_tPt g _ hmem, toAdd_ofAdd,
    L.coordC_of_mem g hWe z hz]

variable [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]

theorem sum_mem_zpowers_iff (T : Finset C) (hT : ∀ z ∈ T, (z : V) ≠ u) :
    (((∑ z ∈ T, Additive.ofMul (cliqueGen (lab := lab) z)).toMul :
        Subgroup.closure (lab '' C)) : S) ∈ Subgroup.zpowers (lab u) ↔
      ∑ z ∈ T, Plane.R (L.coordC g hWe z) = 0 := by
  rw [← L.labHerm_eq_zero_iff hS hC hu g hWe, map_sum]
  refine iff_of_eq (congrArg (· = 0) (Finset.sum_congr rfl fun z hzT => ?_))
  exact L.labHerm_gen hS hC hu g hWe z (mem_neighborSet_of_mem_clique hC.1.2 hu z.2 (hT z hzT))

end Labels

theorem sum_coordC_eq_zero_iff (hC : IsSliceMaxClique lab Y C) (hu : u ∈ C)
    (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0)) (T : Finset C)
    (hT : ∀ z ∈ T, (z : V) ≠ u) (h1 : 1 ≤ T.card) (h5 : T.card ≤ 5) :
    ∑ z ∈ T, Plane.R (L.coordC g hWe z) = 0 ↔ T.card = 5 ∧
      ∃ A : Submodule F4 UnitarySix.V, A ≤ smulSub g W0 ∧ Module.finrank F4 A = 2 ∧
        Subtype.val '' (T : Set C) = Subtype.val '' (L.τ ⁻¹' planePts A) := by
  classical
  have hn : ∀ z ∈ T, (z : V) ∈ (sliceGraph lab Y).neighborSet u := fun z hz =>
    mem_neighborSet_of_mem_clique hC.1.2 hu z.2 (hT z hz)
  set e := T.equivFin
  set p : Fin T.card → ℙ F4 (Fin 3 → F4) := fun i => L.coordC g hWe (e.symm i)
  have hp : Function.Injective p := fun i j hij =>
    e.symm.injective (Subtype.ext (L.coordC_injOn g hWe (hn _ (e.symm i).2) (hn _ (e.symm j).2)
      hij))
  have hsum : ∑ i, Plane.R (p i) = ∑ z ∈ T, Plane.R (L.coordC g hWe z) := by
    rw [← Finset.sum_coe_sort T]
    exact Equiv.sum_comp e.symm (fun z : T => Plane.R (L.coordC g hWe z))
  have hrange : ∀ q, q ∈ Set.range p ↔ ∃ z ∈ T, L.coordC g hWe z = q := by
    intro q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, (e.symm i).2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e ⟨z, hz⟩, by simp [p]⟩
  rw [← hsum, (Plane.rank_one_hermitian_small_dependencies.2 T.card p hp h1 h5)]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨A', hA', hA'q⟩
    refine ⟨A'.map (planeEmb g), map_planeEmb_le g A', by rw [finrank_map_planeEmb, hA'], ?_⟩
    ext v
    constructor
    · rintro ⟨z, hzT, rfl⟩
      refine ⟨⟨z, hn z hzT⟩, ?_, rfl⟩
      have h := (mem_planePts_iff_eW g (A'.map (planeEmb g))
        ⟨_, L.mem_planePts_of_mem g hWe ⟨z, hn z hzT⟩ z.2⟩).2
      rw [Submodule.comap_map_eq_of_injective (planeEmb_injective g)] at h
      refine h ?_
      rw [← L.coordC_of_mem g hWe z (hn z hzT)]
      exact (hA'q _).1 ((hrange _).2 ⟨z, hzT, rfl⟩)
    · rintro ⟨z₀, hz₀, rfl⟩
      have hz₀W : L.τ z₀ ∈ planePts (smulSub g W0) := planePts_mono (map_planeEmb_le g A') hz₀
      have hz₀C : (z₀ : V) ∈ C := (L.mem_img_iff C z₀).1 (by rw [hWe]; exact hz₀W)
      have hsub : (L.coordC g hWe ⟨z₀, hz₀C⟩).submodule ≤ A' := by
        rw [L.coordC_of_mem g hWe _ z₀.2, ← Submodule.comap_map_eq_of_injective
          (planeEmb_injective g) A', ← mem_planePts_iff_eW]
        exact hz₀
      obtain ⟨z', hz'T, hz'⟩ := (hrange _).1 ((hA'q _).2 hsub)
      have hzz := L.coordC_injOn g hWe (hn z' hz'T) z₀.2 hz'
      exact ⟨z', hz'T, by rw [hzz]⟩
  · rintro ⟨A, hAW, hA2, hTA⟩
    refine ⟨A.comap (planeEmb g), by rw [finrank_comap_planeEmb hAW, hA2], fun q => ?_⟩
    obtain ⟨z, hz, rfl⟩ := L.exists_coordC_eq g hWe q
    rw [hrange]
    have key : (L.coordC g hWe z).submodule ≤ A.comap (planeEmb g) ↔
        L.τ ⟨z, hz⟩ ∈ planePts A := by
      rw [L.coordC_of_mem g hWe z hz, ← mem_planePts_iff_eW]
    rw [key]
    constructor
    · rintro ⟨z', hz'T, hz'⟩
      have hzz := L.coordC_injOn g hWe (hn z' hz'T) hz hz'
      have h1 : (z : V) ∈ Subtype.val '' (T : Set C) := ⟨z, hzz ▸ hz'T, rfl⟩
      rw [hTA] at h1
      obtain ⟨z₁, hz₁, hz₁e⟩ := h1
      have : z₁ = ⟨z, hz⟩ := Subtype.ext hz₁e
      rw [← this]
      exact hz₁
    · intro h
      have h1 : (z : V) ∈ Subtype.val '' (L.τ ⁻¹' planePts A) := ⟨⟨z, hz⟩, h, rfl⟩
      rw [← hTA] at h1
      obtain ⟨z', hz'T, hz'e⟩ := h1
      exact ⟨z', hz'T, by rw [Subtype.ext hz'e]⟩

end LocalChart

end CFSG.Monster.B.TwoA.Fischer

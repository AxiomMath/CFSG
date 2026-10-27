module

public import CFSG.Monster.B.Cbar.FourGroupBar
public import CFSG.Monster.Triality
public import CFSG.Monster.Visible.SignCompat
public import CFSG.Monster.B.Cbar.LocalE

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.ScalarKernel CFSG.Monster.Lifts CFSG.Monster.VisQuot

theorem mem_zpowers_xbar_iff (c : Cbar) : c ∈ Subgroup.zpowers xbar ↔ c = 1 ∨ c = xbar :=
  Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar

theorem psiBar_eq_one_iff' {e : Cbar} (he : e ∈ Ebar) :
    psiBar ⟨e, he⟩ = 1 ↔ e ∈ Subgroup.zpowers xbar := by
  rw [psiBar_eq_one_iff, mem_zpowers_xbar_iff]
  exact or_congr Subtype.ext_iff Subtype.ext_iff

theorem center_Ebar_iff (hZE : (Subgroup.center Ebar).map Ebar.subtype = Subgroup.zpowers xbar)
    {q : Cbar} (hq : q ∈ Ebar) :
    (∀ x ∈ Ebar, x * q = q * x) ↔ q ∈ Subgroup.zpowers xbar := by
  rw [← hZE]
  constructor
  · intro h
    refine ⟨⟨q, hq⟩, Subgroup.mem_center_iff.2 fun x => Subtype.ext (h x x.2), rfl⟩
  · rintro ⟨q', hq', rfl⟩ x hx
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hq') ⟨x, hx⟩)

theorem comm_mem_zpowers_xbar {x y : Cbar} (hx : x ∈ Ebar) (hy : y ∈ Ebar) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers xbar := by
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ Ebar :=
    Ebar.mul_mem (Ebar.mul_mem (Ebar.mul_mem hx hy) (Ebar.inv_mem hx)) (Ebar.inv_mem hy)
  rw [← psiBar_eq_one_iff' hmem]
  have h2 : (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : Ebar) = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := rfl
  have h3 := congrArg psiBar h2
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
  rw [h3]
  have hc : psiBar ⟨x, hx⟩ * psiBar ⟨y, hy⟩ = psiBar ⟨y, hy⟩ * psiBar ⟨x, hx⟩ := mul_comm _ _
  rw [hc]
  group

theorem exists_Ebar_not_mem_zpowers (hW : Nontrivial (Wv (phi0 (coordOf rStar)))) :
    ∃ q ∈ Ebar, q ∉ Subgroup.zpowers xbar := by
  obtain ⟨w, hw⟩ := exists_ne (0 : Wv (phi0 (coordOf rStar)))
  obtain ⟨e, he⟩ := psiBar_surjective (Multiplicative.ofAdd w)
  refine ⟨e, e.2, fun h => hw ?_⟩
  have h1 := (psiBar_eq_one_iff' e.2).2 h
  exact ofAdd_eq_one.1 (he.symm.trans h1)

theorem isSimpleGroup_Jbar_quot (hsurj : Function.Surjective jbarToKv)
    [IsSimpleGroup (Kstab (phi0 (coordOf rStar)))] :
    IsSimpleGroup (Jbar ⧸ Ebar.subgroupOf Jbar) := by
  have e : Jbar ⧸ Ebar.subgroupOf Jbar ≃* Kstab (phi0 (coordOf rStar)) :=
    (QuotientGroup.quotientMulEquivOfEq ker_jbarToKv.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective jbarToKv hsurj)
  exact e.isSimpleGroup

theorem mem_Ebar_of_comm {h : Cbar} (hh : h ∈ Jbar)
    (hx : ∀ x ∈ Ebar, h * x * h⁻¹ * x⁻¹ ∈ Subgroup.zpowers xbar) : h ∈ Ebar := by
  have hh' : h⁻¹ ∈ Jbar := Jbar.inv_mem hh
  have key : h⁻¹ ∈ Ebar := by
    refine mem_Ebar_of_conj_trivial hh' fun e he => ?_
    have ha : h⁻¹⁻¹ * e * h⁻¹ * e⁻¹ ∈ Subgroup.zpowers xbar := by
      rw [inv_inv]
      exact hx e he
    have hmem : h⁻¹⁻¹ * e * h⁻¹ * e⁻¹ ∈ Ebar := Ebar.mul_mem (conj_mem_Ebar hh' he) (Ebar.inv_mem he)
    have h1 := (psiBar_eq_one_iff' hmem).2 ha
    have h2 : (⟨h⁻¹⁻¹ * e * h⁻¹ * e⁻¹, hmem⟩ : Ebar) =
        ⟨h⁻¹⁻¹ * e * h⁻¹, conj_mem_Ebar hh' he⟩ * ⟨e, he⟩⁻¹ := rfl
    have h3 := (congrArg psiBar h2).symm.trans h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    exact h3
  simpa using Ebar.inv_mem key

@[expose] noncomputable def psiSub (R : Subgroup Cbar) (hRE : R ≤ Ebar) :
    AddSubgroup (Wv (phi0 (coordOf rStar))) where
  carrier := {w | ∃ r, ∃ hr : r ∈ R, Multiplicative.toAdd (psiBar ⟨r, hRE hr⟩) = w}
  zero_mem' := ⟨1, R.one_mem, by
    rw [show (⟨1, hRE R.one_mem⟩ : Ebar) = 1 from rfl, map_one, toAdd_one]⟩
  add_mem' := by
    rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    refine ⟨r * s, R.mul_mem hr hs, ?_⟩
    rw [show (⟨r * s, hRE (R.mul_mem hr hs)⟩ : Ebar) = ⟨r, hRE hr⟩ * ⟨s, hRE hs⟩ from rfl,
      map_mul, toAdd_mul]
  neg_mem' := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨r⁻¹, R.inv_mem hr, ?_⟩
    rw [show (⟨r⁻¹, hRE (R.inv_mem hr)⟩ : Ebar) = (⟨r, hRE hr⟩ : Ebar)⁻¹ from rfl, map_inv,
      toAdd_inv]

theorem mem_psiSub {R : Subgroup Cbar} {hRE : R ≤ Ebar} {w : Wv (phi0 (coordOf rStar))} :
    w ∈ psiSub R hRE ↔ ∃ r, ∃ hr : r ∈ R, Multiplicative.toAdd (psiBar ⟨r, hRE hr⟩) = w :=
  Iff.rfl

theorem eq_of_invariant (hsurj : Function.Surjective jbarToKv)
    (hirr : ∀ U : Submodule (ZMod 2) (Wv (phi0 (coordOf rStar))),
      (∀ (k : Kstab (phi0 (coordOf rStar))) (w : Wv (phi0 (coordOf rStar))), w ∈ U →
        wAct (phi0 (coordOf rStar)) k w ∈ U) → U = ⊥ ∨ U = ⊤)
    (R : Subgroup Cbar) (hR : ∀ h ∈ Jbar, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hzR : Subgroup.zpowers xbar ≤ R) (hRE : R ≤ Ebar) :
    R = Subgroup.zpowers xbar ∨ R = Ebar := by
  set U := AddSubgroup.toZModSubmodule 2 (psiSub R hRE) with hU
  have hmemU : ∀ w, w ∈ U ↔ w ∈ psiSub R hRE := fun w => AddSubgroup.mem_toZModSubmodule 2
  have hinv : ∀ (k : Kstab (phi0 (coordOf rStar))) (w : Wv (phi0 (coordOf rStar))), w ∈ U →
      wAct (phi0 (coordOf rStar)) k w ∈ U := by
    intro k w hw
    rw [hmemU] at hw ⊢
    obtain ⟨r, hr, rfl⟩ := hw
    obtain ⟨g, rfl⟩ := hsurj k
    have hgr : (g : Cbar)⁻¹ * r * g ∈ R := by
      have := hR _ (Jbar.inv_mem g.2) r hr
      rwa [inv_inv] at this
    refine ⟨_, hgr, ?_⟩
    rw [psiBar_conj g.2 (hRE hr), toAdd_ofAdd]
  rcases hirr U hinv with h | h
  · left
    refine le_antisymm (fun r hr => ?_) hzR
    have hw : Multiplicative.toAdd (psiBar ⟨r, hRE hr⟩) ∈ U := (hmemU _).2 ⟨r, hr, rfl⟩
    rw [h, Submodule.mem_bot] at hw
    exact (psiBar_eq_one_iff' (hRE hr)).1 (toAdd_eq_zero.1 hw)
  · right
    refine le_antisymm hRE (fun e he => ?_)
    have hw : Multiplicative.toAdd (psiBar ⟨e, he⟩) ∈ U := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨r, hr, hre⟩ := (hmemU _).1 hw
    have hmem : r⁻¹ * e ∈ Ebar := Ebar.mul_mem (Ebar.inv_mem (hRE hr)) he
    have h1 : psiBar ⟨r⁻¹ * e, hmem⟩ = 1 := by
      have h2 : (⟨r⁻¹ * e, hmem⟩ : Ebar) = (⟨r, hRE hr⟩ : Ebar)⁻¹ * ⟨e, he⟩ := rfl
      rw [h2, map_mul, map_inv, inv_mul_eq_one]
      exact Multiplicative.toAdd.injective hre
    have h3 : r⁻¹ * e ∈ R := hzR ((psiBar_eq_one_iff' hmem).1 h1)
    have h4 := R.mul_mem hr h3
    rwa [mul_inv_cancel_left] at h4

theorem Vbar_le_Jbar (hC : Subgroup.centralizer {xbar} = Jbar) : Vbar ≤ Jbar := by
  intro c hc
  rw [← hC, Subgroup.mem_centralizer_singleton_iff]
  exact mul_comm_of_mem_Vbar hc xbar_mem_Vbar

theorem closure_insert_taubar_inv : Subgroup.closure (insert taubar⁻¹ (Jbar : Set Cbar)) = ⊤ := by
  set K := Subgroup.closure (insert taubar⁻¹ (Jbar : Set Cbar)) with hK
  have hτ : taubar ∈ K := by
    rw [← inv_inv taubar]
    exact K.inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))
  have hJ : ∀ c ∈ Jbar, c ∈ K := fun c hc => Subgroup.subset_closure (Set.mem_insert_of_mem _ hc)
  have hle : Cgen ≤ (K.comap kappa).map Cgen.subtype := by
    show Subgroup.closure (insert tauB (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB))) ≤ _
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact ⟨tauC, hτ, rfl⟩
    · exact ⟨⟨y, Jstar_le_Cgen hy⟩, hJ _ ⟨⟨y, Jstar_le_Cgen hy⟩, hy, rfl⟩, rfl⟩
  rw [eq_top_iff]
  intro c _
  obtain ⟨g, rfl⟩ := kappa_surjective c
  obtain ⟨g', hg', hgg'⟩ := hle g.2
  rw [← Subtype.ext hgg']
  exact hg'

@[expose] def dCode : C := ⟨g 0 + g 1, C.add_mem (g_mem_C 0) (g_mem_C 1)⟩

theorem dCode_apply_zero : (dCode : Fin 24 → ZMod 2) 0 = 1 := by
  change (g 0 + g 1) 0 = 1
  decide

theorem dCode_apply_one : (dCode : Fin 24 → ZMod 2) 1 = 1 := by
  change (g 0 + g 1) 1 = 1
  decide

theorem dCode_apply_eight : (dCode : Fin 24 → ZMod 2) 8 = 0 := by
  change (g 0 + g 1) 8 = 0
  decide

@[expose] noncomputable def xD : Q := XQ ⟨dCode, 0⟩

theorem coordOf_xD : coordOf xD = (dCode, thetaD dCode) := by
  rw [coordOf, xD, XQ_eq, MulEquiv.symm_apply_apply]

theorem xD_mem_centralizer : xD ∈ Subgroup.centralizer {rStar} := by
  rw [mem_centralizer_iff_bL, coordOf_rStar, coordOf_xD]
  refine (bL_phi0 0 dCode (deltaPair 0 1) (thetaD dCode)).trans ?_
  rw [pair_zero_left, zero_add, pair_deltaPair_zero_one, dCode_apply_zero, dCode_apply_one]
  rfl

@[expose] noncomputable def uBar : Cbar := kappa ⟨rhoEquiv xD, rhoEquiv_mem_Cgen xD_mem_centralizer⟩

theorem uBar_mem_Ebar : uBar ∈ Ebar := kappa_rho_mem_Ebar xD_mem_centralizer

@[expose] noncomputable def uTauC : Cgen :=
  tauC * ⟨rhoEquiv xD, rhoEquiv_mem_Cgen xD_mem_centralizer⟩ * tauC⁻¹

theorem coe_uTauC : (uTauC : SpaceB ≃ₗ[ℚ] SpaceB) = tauB * rhoEquiv xD * tauB⁻¹ := rfl

theorem uTauC_mem_Jstar : (uTauC : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar :=
  ⟨rhoEquiv_XQ_conj_mem_Hmat ⟨dCode, 0⟩, (Cgen_le uTauC.2).2⟩

theorem taubar_conj_uBar : (taubar⁻¹)⁻¹ * uBar * taubar⁻¹ = kappa uTauC := by
  rw [inv_inv, uTauC, map_mul, map_mul, map_inv]
  rfl

theorem gO_dCode_ne : ¬ (gO dCode = 1 ∨ gO dCode = negOneO) := by
  rintro (h | h)
  · have h1 : mat (gO dCode) 0 0 = mat 1 0 0 := by rw [h]
    rw [mat_gO, mat_one, gmat, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      dCode_apply_zero] at h1
    exact absurd h1 (by decide)
  · have h1 : mat (gO dCode) 8 8 = mat negOneO 8 8 := by rw [h]
    rw [mat_gO, mat_negOneO, gmat, Matrix.diagonal_apply_eq, Matrix.neg_apply,
      Matrix.one_apply_eq, dCode_apply_eight] at h1
    exact absurd h1 (by decide)

theorem kappa_uTauC_mem_Jbar : kappa uTauC ∈ Jbar := kappa_mem_Jbar uTauC_mem_Jstar

theorem kappa_uTauC_not_mem_Ebar : kappa uTauC ∉ Ebar := by
  intro h
  have hp : thetaEquiv (signLiftPair ⟨dCode, 0⟩) = (uTauC : SpaceB ≃ₗ[ℚ] SpaceB) :=
    thetaEquiv_signLiftPair ⟨dCode, 0⟩
  have hk := coe_jbarToKv_kappa uTauC_mem_Jstar hp
  have hker : (⟨kappa uTauC, kappa_mem_Jbar uTauC_mem_Jstar⟩ : Jbar) ∈ jbarToKv.ker := by
    rw [ker_jbarToKv]
    exact h
  rw [MonoidHom.mem_ker] at hker
  rw [hker] at hk
  have h1 : (QuotientGroup.mk (gO dCode) : OLq) = 1 := by
    have h2 : ((1 : Kstab (phi0 (coordOf rStar))) : OLq) = 1 := rfl
    rw [h2] at hk
    exact inv_eq_one.1 hk.symm
  rw [QuotientGroup.eq_one_iff, VisQuot.mem_zpowers_negOneO_iff] at h1
  exact gO_dCode_ne h1

@[expose] noncomputable def e0Cocode : Cocode := Submodule.Quotient.mk (Pi.single (0 : Fin 24) (1 : ZMod 2))

theorem coordOf_DQ (δ : Cocode) : coordOf (DQ δ) = (0, δ) := by
  rw [coordOf, DQ_eq, MulEquiv.symm_apply_apply]

theorem DQ_mem_centralizer (δ : Cocode) : DQ δ ∈ Subgroup.centralizer {rStar} := by
  rw [mem_centralizer_iff_bL, coordOf_rStar, coordOf_DQ]
  refine (bL_phi0 0 0 (deltaPair 0 1) δ).trans ?_
  rw [pair_zero_left, pair_zero_left, add_zero]

@[expose] noncomputable def hBar : Cbar :=
  kappa ⟨rhoEquiv (DQ e0Cocode), rhoEquiv_mem_Cgen (DQ_mem_centralizer e0Cocode)⟩

theorem hBar_mem_Jbar : hBar ∈ Jbar := Ebar_le_Jbar (kappa_rho_mem_Ebar (DQ_mem_centralizer _))

theorem hBar_rel : (taubar⁻¹)⁻¹ * hBar * taubar⁻¹ * hBar = taubar⁻¹ := by
  obtain ⟨-, hsq', hrel', hrel2', -⟩ :=
    odd_cocode_inverts_triality.1 _ odd_cocode_inverts_triality.2.1
  have hsq : rhoEquiv (DQ e0Cocode) * rhoEquiv (DQ e0Cocode) = 1 := hsq'
  have hrel : rhoEquiv (DQ e0Cocode) * tauB * rhoEquiv (DQ e0Cocode) = tauB⁻¹ := hrel'
  have hrel2 : rhoEquiv (DQ e0Cocode) * (tauB * rhoEquiv (DQ e0Cocode) * tauB⁻¹) = tauB := hrel2'
  have e1 : tauB * rhoEquiv (DQ e0Cocode) * tauB⁻¹ = rhoEquiv (DQ e0Cocode) * tauB := by
    calc tauB * rhoEquiv (DQ e0Cocode) * tauB⁻¹
        = (rhoEquiv (DQ e0Cocode) * rhoEquiv (DQ e0Cocode)) *
            (tauB * rhoEquiv (DQ e0Cocode) * tauB⁻¹) := by rw [hsq, one_mul]
      _ = rhoEquiv (DQ e0Cocode) *
            (rhoEquiv (DQ e0Cocode) * (tauB * rhoEquiv (DQ e0Cocode) * tauB⁻¹)) := by
          rw [mul_assoc]
      _ = rhoEquiv (DQ e0Cocode) * tauB := by rw [hrel2]
  have hS : tauB * rhoEquiv (DQ e0Cocode) * tauB⁻¹ * rhoEquiv (DQ e0Cocode) = tauB⁻¹ := by
    rw [e1]
    exact hrel
  have hC : tauC * ⟨rhoEquiv (DQ e0Cocode), rhoEquiv_mem_Cgen (DQ_mem_centralizer e0Cocode)⟩ *
      tauC⁻¹ * ⟨rhoEquiv (DQ e0Cocode), rhoEquiv_mem_Cgen (DQ_mem_centralizer e0Cocode)⟩ =
        tauC⁻¹ := Subtype.ext hS
  rw [inv_inv, hBar, taubar, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hC]

theorem simple_of_local (hC : Subgroup.centralizer {xbar} = Jbar)
    (hZE : (Subgroup.center Ebar).map Ebar.subtype = Subgroup.zpowers xbar)
    (hsurj : Function.Surjective jbarToKv) [IsSimpleGroup (Kstab (phi0 (coordOf rStar)))]
    (hW : Nontrivial (Wv (phi0 (coordOf rStar))))
    (hirr : ∀ U : Submodule (ZMod 2) (Wv (phi0 (coordOf rStar))),
      (∀ (k : Kstab (phi0 (coordOf rStar))) (w : Wv (phi0 (coordOf rStar))), w ∈ U →
        wAct (phi0 (coordOf rStar)) k w ∈ U) → U = ⊥ ∨ U = ⊤) :
    Nontrivial Cbar ∧ IsSimpleGroup Cbar :=
  isSimpleGroup_of_triality (H := Jbar) (Q := Ebar) Ebar_le_Jbar xbar_mem_Ebar orderOf_xbar
    (fun _ hq => center_Ebar_iff hZE hq) (fun _ hx _ hy => comm_mem_zpowers_xbar hx hy)
    (exists_Ebar_not_mem_zpowers hW) (isSimpleGroup_Jbar_quot hsurj)
    (fun _ hh hx => mem_Ebar_of_comm hh hx) (eq_of_invariant hsurj hirr) hC
    (E := Vbar) (Vbar_le_Jbar hC) natCard_Vbar (fun _ he => mul_self_of_mem_Vbar he)
    xbar_mem_Vbar (τ := taubar⁻¹)
    (fun e he => by rw [inv_inv]; exact taubar_conj_mem_Vbar he)
    (fun e he hne => by rw [inv_inv]; exact taubar_conj_ne he hne)
    closure_insert_taubar_inv (u := uBar) uBar_mem_Ebar
    (by rw [taubar_conj_uBar]; exact kappa_uTauC_mem_Jbar)
    (by rw [taubar_conj_uBar]; exact kappa_uTauC_not_mem_Ebar) (h := hBar) hBar_mem_Jbar hBar_rel

end CFSG.Monster.B

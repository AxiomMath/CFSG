module

public import CFSG.Monster.Griess.Grading
public import CFSG.Monster.VisCert.Delta
public import CFSG.Monster.VisQuot.Monomial
public import Mathlib.Combinatorics.SimpleGraph.Init

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Lifts CFSG.Monster.ScalarKernel CFSG.Monster.Visible
  CFSG.Monster.Visible.SignCompat CFSG.Monster.VisCert

@[expose] noncomputable def codeCoord : L2 →ₗ[ZMod 2] C :=
  (LinearMap.fst (ZMod 2) C Cocode) ∘ₗ phi0Equiv.symm.toLinearMap

@[expose] noncomputable def cocodeCoord : L2 →ₗ[ZMod 2] Cocode :=
  (LinearMap.snd (ZMod 2) C Cocode) ∘ₗ phi0Equiv.symm.toLinearMap

@[expose] noncomputable def parity : L2 →ₗ[ZMod 2] ZMod 2 := (pair Spin.ΩC) ∘ₗ cocodeCoord

@[expose] noncomputable def U1 : Submodule (ZMod 2) L2 :=
  ΩLine.comap codeCoord ⊓ LinearMap.ker parity

theorem phi0_codeCoord_cocodeCoord (x : L2) :
    phi0 (codeCoord x, cocodeCoord x) = x := by
  change phi0Equiv (phi0Equiv.symm x) = x
  exact phi0Equiv.apply_symm_apply x

theorem codeCoord_phi0 (a : C) (δ : Cocode) : codeCoord (phi0 (a, δ)) = a := by
  change (phi0Equiv.symm (phi0Equiv (a, δ))).1 = a
  rw [phi0Equiv.symm_apply_apply]

theorem cocodeCoord_phi0 (a : C) (δ : Cocode) : cocodeCoord (phi0 (a, δ)) = δ := by
  change (phi0Equiv.symm (phi0Equiv (a, δ))).2 = δ
  rw [phi0Equiv.symm_apply_apply]

theorem codeCoord_twoΩCls : codeCoord twoΩCls = VisQuot.ΩC := by
  rw [← SignCompat.phi0_ΩC_zero, codeCoord_phi0]
  rfl

theorem cocodeCoord_twoΩCls : cocodeCoord twoΩCls = 0 := by
  rw [← SignCompat.phi0_ΩC_zero, cocodeCoord_phi0]

theorem polarBilin_twoΩCls (x : L2) :
    QuadraticMap.polarBilin qL twoΩCls x = parity x := by
  conv_lhs => rw [← SignCompat.phi0_ΩC_zero, ← phi0_codeCoord_cocodeCoord x]
  rw [bL_phi0, pair_zero_right, add_zero]
  rfl

theorem twoΩCls_mem_U1 : twoΩCls ∈ U1 := by
  rw [U1, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap, codeCoord_twoΩCls]
    exact ΩC_mem_ΩLine
  · change pair Spin.ΩC (cocodeCoord twoΩCls) = 0
    rw [cocodeCoord_twoΩCls, map_zero]

theorem eq_zero_or_eq_twoΩCls_of_mem_U1 {x : L2} (hx : x ∈ U1)
    (h : cocodeCoord x = 0) : x = 0 ∨ x = twoΩCls := by
  rw [U1, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker] at hx
  rcases mem_ΩLine_iff.1 hx.1 with h0 | hΩ
  · left
    rw [← phi0_codeCoord_cocodeCoord x, h0, h]
    exact map_zero phi0
  · right
    rw [← phi0_codeCoord_cocodeCoord x, hΩ, h]
    exact SignCompat.phi0_ΩC_zero

theorem polarBilin_of_mem_U1 {x y : L2} (hx : x ∈ U1) (hy : parity y = 0) :
    QuadraticMap.polarBilin qL x y = pair (codeCoord y) (cocodeCoord x) := by
  have hx' : codeCoord x ∈ ΩLine := hx.1
  have hy' : pair Spin.ΩC (cocodeCoord y) = 0 := hy
  conv_lhs => rw [← phi0_codeCoord_cocodeCoord x, ← phi0_codeCoord_cocodeCoord y]
  rw [bL_phi0]
  have hzero : pair (codeCoord x) (cocodeCoord y) = 0 := by
    rcases mem_ΩLine_iff.1 hx' with h0 | hΩ
    · rw [h0, pair_zero_left]
    · rw [hΩ]
      exact hy'
  rw [hzero, zero_add]

private theorem lamX_add_lamCocode (x : L2) :
    x = lamX (codeCoord x) + lamCocode (thetaD (codeCoord x) + cocodeCoord x) := by
  conv_lhs => rw [← phi0_codeCoord_cocodeCoord x]
  rw [phi0_apply, lamT, map_add]
  abel

private theorem codeCoord_lamX (c : C) : codeCoord (lamX c) = c := by
  rw [← phi0_thetaD c, codeCoord_phi0]

private theorem cocodeCoord_lamX (c : C) : cocodeCoord (lamX c) = thetaD c := by
  rw [← phi0_thetaD c, cocodeCoord_phi0]

private theorem codeCoord_lamCocode (δ : Cocode) : codeCoord (lamCocode δ) = 0 := by
  rw [← phi0_zero_left δ, codeCoord_phi0]

private theorem cocodeCoord_lamCocode (δ : Cocode) : cocodeCoord (lamCocode δ) = δ := by
  rw [← phi0_zero_left δ, cocodeCoord_phi0]

private theorem codeCoord_lamVec (v : Fin 24 → ZMod 2) : codeCoord (lamVec v) = 0 := by
  rw [← lamCocode_mk v, codeCoord_lamCocode]

private theorem cocodeCoord_lamVec (v : Fin 24 → ZMod 2) :
    cocodeCoord (lamVec v) = Submodule.Quotient.mk v := by
  rw [← lamCocode_mk v, cocodeCoord_lamCocode]

private theorem pair_omega_mul (a c : C) :
    pair Spin.ΩC (Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * (c : Fin 24 → ZMod 2))) = 0 := by
  rw [Griess.pair_ΩC_mk, sum_eq_hammingNorm]
  exact (ZMod.natCast_eq_zero_iff _ _).2 (two_dvd_hammingNorm_mul a.2 c.2)

private theorem modTwoEnd_gO_decomp (a : C) (x : L2) :
    modTwoEnd (gO a) x =
      lamX (codeCoord x) +
        lamVec ((a : Fin 24 → ZMod 2) * (codeCoord x : Fin 24 → ZMod 2)) +
        K (a : Fin 24 → ZMod 2) (codeCoord x : Fin 24 → ZMod 2) • twoΩCls +
        (lamCocode (thetaD (codeCoord x) + cocodeCoord x) +
          pair Spin.ΩC (thetaD (codeCoord x) + cocodeCoord x) • lamX a +
          (pair Spin.ΩC (thetaD (codeCoord x) + cocodeCoord x) * P (a : Fin 24 → ZMod 2) +
            pair a (thetaD (codeCoord x) + cocodeCoord x)) • twoΩCls) := by
  conv_lhs => rw [lamX_add_lamCocode x]
  rw [map_add, modTwoEnd_gO_lamX, modTwoEnd_gO_lamCocode]

private theorem pair_omega_thetaD_add (x : L2) :
    pair Spin.ΩC (thetaD (codeCoord x) + cocodeCoord x) = parity x := by
  rw [map_add, pair_ΩC_thetaD, zero_add]
  rfl

theorem codeCoord_gO (a : C) (x : L2) : ∃ s : ZMod 2,
    codeCoord (modTwoEnd (gO a) x) = codeCoord x + parity x • a + s • VisQuot.ΩC := by
  refine ⟨K (a : Fin 24 → ZMod 2) (codeCoord x : Fin 24 → ZMod 2) +
    pair Spin.ΩC (thetaD (codeCoord x) + cocodeCoord x) * P (a : Fin 24 → ZMod 2) +
    pair a (thetaD (codeCoord x) + cocodeCoord x), ?_⟩
  rw [modTwoEnd_gO_decomp a x, pair_omega_thetaD_add x]
  simp only [map_add, map_smul, codeCoord_lamX, codeCoord_lamVec, codeCoord_lamCocode,
    codeCoord_twoΩCls, add_smul]
  abel

theorem cocodeCoord_gO (a : C) (x : L2) :
    cocodeCoord (modTwoEnd (gO a) x) = cocodeCoord x +
      Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * (codeCoord x : Fin 24 → ZMod 2)) +
      parity x • thetaD a := by
  rw [modTwoEnd_gO_decomp a x, pair_omega_thetaD_add x]
  simp only [map_add, map_smul, cocodeCoord_lamX, cocodeCoord_lamVec, cocodeCoord_lamCocode,
    cocodeCoord_twoΩCls, smul_zero, add_zero]
  have hself : thetaD (codeCoord x) + thetaD (codeCoord x) = 0 := Spin.add_self_cocode _
  calc
    thetaD (codeCoord x) +
        Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * (codeCoord x : Fin 24 → ZMod 2)) +
        (thetaD (codeCoord x) + cocodeCoord x + parity x • thetaD a) =
      (thetaD (codeCoord x) + thetaD (codeCoord x)) +
        (Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * (codeCoord x : Fin 24 → ZMod 2)) +
          cocodeCoord x) + parity x • thetaD a := by abel
    _ = cocodeCoord x +
        Submodule.Quotient.mk ((a : Fin 24 → ZMod 2) * (codeCoord x : Fin 24 → ZMod 2)) +
        parity x • thetaD a := by rw [hself]; abel

theorem parity_gO (a : C) (x : L2) : parity (modTwoEnd (gO a) x) = parity x := by
  change pair Spin.ΩC (cocodeCoord (modTwoEnd (gO a) x)) = pair Spin.ΩC (cocodeCoord x)
  rw [cocodeCoord_gO a x]
  simp only [map_add, map_smul, pair_omega_mul a (codeCoord x), pair_ΩC_thetaD, smul_zero,
    add_zero]

theorem modTwoEnd_gO_of_mem_U1 (a : C) {x : L2} (hx : x ∈ U1) :
    modTwoEnd (gO a) x = x + pair a (cocodeCoord x) • twoΩCls := by
  rw [U1, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_ker] at hx
  have hpar : pair Spin.ΩC (cocodeCoord x) = 0 := hx.2
  rcases mem_ΩLine_iff.1 hx.1 with hc | hc
  · have hx0 : x = lamCocode (cocodeCoord x) := by
      conv_lhs => rw [← phi0_codeCoord_cocodeCoord x]
      rw [hc, phi0_zero_left]
    rw [hx0, modTwoEnd_gO_lamCocode, hpar]
    simp [cocodeCoord_lamCocode]
  · have hx1 : x = twoΩCls + lamCocode (cocodeCoord x) := by
      conv_lhs => rw [← phi0_codeCoord_cocodeCoord x]
      rw [hc, ← SignCompat.phi0_ΩC_zero, ← phi0_zero_left]
      rw [show ((VisQuot.ΩC, cocodeCoord x) : C × Cocode) =
        (VisQuot.ΩC, 0) + (0, cocodeCoord x) by simp]
      rw [map_add]
      rfl
    have hf : modTwoEnd (gO a) twoΩCls = twoΩCls := by
      simpa [twoΩCls_eq_frameClass] using modTwoEnd_gO_frameClass a
    have hcδ : cocodeCoord (twoΩCls + lamCocode (cocodeCoord x)) = cocodeCoord x := by
      rw [map_add, cocodeCoord_twoΩCls, cocodeCoord_lamCocode, zero_add]
    rw [hx1, map_add, hf, modTwoEnd_gO_lamCocode, hpar, hcδ]
    simp only [zero_smul, zero_mul, add_zero]
    abel_nf

theorem modTwoEnd_gO_mem_U1 (a : C) {x : L2} (hx : x ∈ U1) :
    modTwoEnd (gO a) x ∈ U1 := by
  rw [U1, Submodule.mem_inf] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap]
    obtain ⟨s, hs⟩ := codeCoord_gO a x
    rw [hs, hx.2, zero_smul, add_zero]
    exact ΩLine.add_mem hx.1 (ΩLine.smul_mem s ΩC_mem_ΩLine)
  · rw [LinearMap.mem_ker, parity_gO]
    exact hx.2

theorem codeCoord_PO (p : AutPerm) (x : L2) :
    codeCoord (modTwoEnd (PO p) x) = permC p (codeCoord x) := by
  conv_lhs => rw [lamX_add_lamCocode x]
  rw [map_add, modTwoEnd_PO_lamX, modTwoEnd_PO_lamCocode]
  simp only [map_add, codeCoord_lamX, codeCoord_lamCocode, add_zero]

theorem cocodeCoord_PO (p : AutPerm) (x : L2) :
    cocodeCoord (modTwoEnd (PO p) x) =
      permD p (cocodeCoord x) + permD p (thetaD (codeCoord x)) +
        thetaD (permC p (codeCoord x)) := by
  conv_lhs => rw [lamX_add_lamCocode x]
  rw [map_add, modTwoEnd_PO_lamX, modTwoEnd_PO_lamCocode]
  simp only [map_add, cocodeCoord_lamX, cocodeCoord_lamCocode]
  abel

theorem cocodeCoord_PO_of_mem_U1 (p : AutPerm) {x : L2} (hx : x ∈ U1) :
    cocodeCoord (modTwoEnd (PO p) x) = permD p (cocodeCoord x) := by
  rw [U1, Submodule.mem_inf, Submodule.mem_comap] at hx
  rw [cocodeCoord_PO p x]
  rcases mem_ΩLine_iff.1 hx.1 with h0 | hΩ
  · rw [h0, map_zero, thetaD_zero, map_zero, add_zero, add_zero]
  · have hθ : thetaD (VisQuot.ΩC : C) = 0 := thetaD_ΩC
    have hpΩ : permC p (VisQuot.ΩC : C) = VisQuot.ΩC := permC_ΩC p
    rw [hΩ, hθ, hpΩ, hθ, map_zero, add_zero, add_zero]

theorem parity_PO (p : AutPerm) (x : L2) : parity (modTwoEnd (PO p) x) = parity x := by
  change pair Spin.ΩC (cocodeCoord (modTwoEnd (PO p) x)) = pair Spin.ΩC (cocodeCoord x)
  rw [cocodeCoord_PO p x, map_add, map_add]
  have h1 : pair Spin.ΩC (permD p (cocodeCoord x)) = pair Spin.ΩC (cocodeCoord x) := by
    have h := pair_permC_permD p Spin.ΩC (cocodeCoord x)
    rwa [show permC p (Spin.ΩC) = Spin.ΩC from permC_ΩC p] at h
  have h2 : pair Spin.ΩC (permD p (thetaD (codeCoord x))) = 0 := by
    have h := pair_permC_permD p Spin.ΩC (thetaD (codeCoord x))
    rw [show permC p (Spin.ΩC) = Spin.ΩC from permC_ΩC p, pair_ΩC_thetaD] at h
    exact h
  have h3 : pair Spin.ΩC (thetaD (permC p (codeCoord x))) = 0 := pair_ΩC_thetaD _
  simp only [h1, h2, h3, add_zero]

theorem modTwoEnd_PO_mem_U1 (p : AutPerm) {x : L2} (hx : x ∈ U1) :
    modTwoEnd (PO p) x ∈ U1 := by
  rw [U1, Submodule.mem_inf] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap, codeCoord_PO]
    rcases mem_ΩLine_iff.1 hx.1 with h0 | hΩ
    · rw [h0, map_zero]
      exact ΩLine.zero_mem
    · rw [hΩ, permC_ΩC]
      exact ΩC_mem_ΩLine
  · rw [LinearMap.mem_ker, parity_PO]
    exact hx.2

@[expose] noncomputable def cocodeAnn (S : Submodule (ZMod 2) C) : Submodule (ZMod 2) Cocode :=
  ⨅ c ∈ S, LinearMap.ker (pair c)

theorem mem_cocodeAnn {S : Submodule (ZMod 2) C} {δ : Cocode} :
    δ ∈ cocodeAnn S ↔ ∀ c ∈ S, pair c δ = 0 := by
  simp [cocodeAnn, LinearMap.mem_ker]

theorem finrank_cocodeAnn_add (S : Submodule (ZMod 2) C) :
    Module.finrank (ZMod 2) (cocodeAnn S) + Module.finrank (ZMod 2) S = 12 := by
  have hmap : (cocodeAnn S).map (cocodeDual : Cocode →ₗ[ZMod 2] Module.Dual (ZMod 2) C) =
      S.dualAnnihilator := by
    ext f
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro c hc
      exact (cocodeDual_apply δ c).trans ((mem_cocodeAnn.1 hδ) c hc)
    · intro hf
      obtain ⟨δ, hδ⟩ := cocodeDual.surjective f
      refine Submodule.mem_map.2 ⟨δ, ?_, hδ⟩
      rw [mem_cocodeAnn]
      intro c hc
      have hfc : f c = 0 := (Submodule.mem_dualAnnihilator f).1 hf c hc
      rw [← hδ] at hfc
      rwa [cocodeDual_apply] at hfc
  calc Module.finrank (ZMod 2) (cocodeAnn S) + Module.finrank (ZMod 2) S
      = Module.finrank (ZMod 2) ((cocodeAnn S).map
          (cocodeDual : Cocode →ₗ[ZMod 2] Module.Dual (ZMod 2) C)) +
          Module.finrank (ZMod 2) S := by rw [LinearEquiv.finrank_map_eq]
    _ = Module.finrank (ZMod 2) S.dualAnnihilator + Module.finrank (ZMod 2) S := by rw [hmap]
    _ = Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) S.dualAnnihilator := add_comm _ _
    _ = Module.finrank (ZMod 2) C := Subspace.finrank_add_finrank_dualAnnihilator_eq S
    _ = 12 := finrank_C

theorem finrank_map_add_finrank_inf_ker {K V W : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : V →ₗ[K] W) (E : Submodule K V) :
    Module.finrank K (E.map f) + Module.finrank K ↥(E ⊓ LinearMap.ker f) =
      Module.finrank K E := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict E)
  have hrange : LinearMap.range (f.domRestrict E) = E.map f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Submodule.mem_map_of_mem y.2
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : Module.finrank K ↥(LinearMap.ker (f.domRestrict E)) =
      Module.finrank K ↥(E ⊓ LinearMap.ker f) := by
    rw [LinearMap.ker_domRestrict]
    rw [← Submodule.finrank_map_subtype_eq E ((LinearMap.ker f).comap E.subtype)]
    rw [Submodule.map_comap_subtype]
  rw [hrange, hker] at h
  exact h

theorem finrank_add_finrank_sup_le {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {X Y : Submodule K V} (hXY : X ≤ Y) (W : Submodule K V) :
    Module.finrank K X + Module.finrank K ↥(W ⊔ Y) ≤
      Module.finrank K Y + Module.finrank K ↥(W ⊔ X) := by
  have hsup : Module.finrank K ↥((W ⊔ X) ⊔ Y) + Module.finrank K ↥((W ⊔ X) ⊓ Y) =
      Module.finrank K ↥(W ⊔ X) + Module.finrank K Y :=
    Submodule.finrank_sup_add_finrank_inf_eq (W ⊔ X) Y
  have h1 : (W ⊔ X) ⊔ Y = W ⊔ Y := by
    rw [sup_assoc, sup_eq_right.mpr hXY]
  have h2 : X ≤ (W ⊔ X) ⊓ Y := le_inf le_sup_right hXY
  have hmono : Module.finrank K X ≤ Module.finrank K ↥((W ⊔ X) ⊓ Y) :=
    Submodule.finrank_mono h2
  rw [h1] at hsup
  omega

theorem finrank_le_of_singular {D : Submodule (ZMod 2) L2} (hD : ∀ x ∈ D, qL x = 0) :
    Module.finrank (ZMod 2) D ≤
      Module.finrank (ZMod 2) ((D ⊓ U1).map cocodeCoord) +
      Module.finrank (ZMod 2) ↥((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine) := by
  have hbD : ∀ x ∈ D, ∀ y ∈ D, QuadraticMap.polarBilin qL x y = 0 := by
    intro x hx y hy
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hD (x + y) (D.add_mem hx hy),
      hD x hx, hD y hy]
    simp
  have hBker : (D ⊓ LinearMap.ker parity) ⊓
      LinearMap.ker (ΩLine.mkQ ∘ₗ codeCoord) = D ⊓ U1 := by
    ext x
    constructor
    · rintro ⟨⟨hxD, hpx⟩, hxq⟩
      refine ⟨hxD, ?_⟩
      rw [U1]
      refine ⟨?_, hpx⟩
      change codeCoord x ∈ ΩLine
      change (Submodule.Quotient.mk (codeCoord x) : C ⧸ ΩLine) = 0 at hxq
      exact (Submodule.Quotient.mk_eq_zero _).1 hxq
    · rintro ⟨hxD, hxU⟩
      rw [U1] at hxU
      refine ⟨⟨hxD, hxU.2⟩, ?_⟩
      change (Submodule.Quotient.mk (codeCoord x) : C ⧸ ΩLine) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 hxU.1
  have hpar : Module.finrank (ZMod 2) D =
      Module.finrank (ZMod 2) (D.map parity) +
        Module.finrank (ZMod 2) ↥(D ⊓ LinearMap.ker parity) :=
    (finrank_map_add_finrank_inf_ker parity D).symm
  have hcode : Module.finrank (ZMod 2) ↥(D ⊓ LinearMap.ker parity) =
      Module.finrank (ZMod 2) ((D ⊓ LinearMap.ker parity).map
        (ΩLine.mkQ ∘ₗ codeCoord)) +
        Module.finrank (ZMod 2) ↥(D ⊓ U1) := by
    have h := finrank_map_add_finrank_inf_ker (ΩLine.mkQ ∘ₗ codeCoord)
      (D ⊓ LinearMap.ker parity)
    rw [hBker] at h
    exact h.symm
  have hquot : Module.finrank (ZMod 2)
      ↥((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine) =
      Module.finrank (ZMod 2) ((D ⊓ LinearMap.ker parity).map
        (ΩLine.mkQ ∘ₗ codeCoord)) + 1 := by
    have hmap : ((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine).map ΩLine.mkQ =
        (D ⊓ LinearMap.ker parity).map (ΩLine.mkQ ∘ₗ codeCoord) := by
      have hΩ : ΩLine.map ΩLine.mkQ = ⊥ :=
        (LinearMap.le_ker_iff_map).1 (by rw [Submodule.ker_mkQ])
      rw [Submodule.map_sup, ← Submodule.map_comp, hΩ]
      simp
    have hker : ((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine) ⊓
        LinearMap.ker ΩLine.mkQ = ΩLine := by
      rw [Submodule.ker_mkQ]
      exact inf_eq_right.mpr le_sup_right
    have hrn := finrank_map_add_finrank_inf_ker ΩLine.mkQ
      ((D ⊓ LinearMap.ker parity).map codeCoord ⊔ ΩLine)
    rw [hmap, hker, finrank_ΩLine] at hrn
    omega
  have hdelta : Module.finrank (ZMod 2) ((D ⊓ U1).map cocodeCoord) +
      Module.finrank (ZMod 2) ↥((D ⊓ U1) ⊓ LinearMap.ker cocodeCoord) =
      Module.finrank (ZMod 2) ↥(D ⊓ U1) :=
    finrank_map_add_finrank_inf_ker cocodeCoord (D ⊓ U1)
  have hker_le : (D ⊓ U1) ⊓ LinearMap.ker cocodeCoord ≤
      Submodule.span (ZMod 2) {twoΩCls} := by
    intro x hx
    have hxU : x ∈ U1 := hx.1.2
    have hxδ : cocodeCoord x = 0 := hx.2
    rcases eq_zero_or_eq_twoΩCls_of_mem_U1 hxU hxδ with h0 | hf
    · rw [h0]
      exact Submodule.zero_mem _
    · rw [hf]
      exact Submodule.mem_span_singleton_self _
  have htwoΩ_ne : twoΩCls ≠ 0 := twoΩCls_mem_frameDelta.1
  have hle1 : Module.finrank (ZMod 2) ↥((D ⊓ U1) ⊓ LinearMap.ker cocodeCoord) ≤ 1 := by
    have h := Submodule.finrank_mono hker_le
    rwa [finrank_span_singleton htwoΩ_ne] at h
  have hPle : Module.finrank (ZMod 2) (D.map parity) ≤ 1 := by
    have h := Submodule.finrank_mono (le_top : D.map parity ≤ ⊤)
    simpa [Module.finrank_self] using h
  rcases (show Module.finrank (ZMod 2) (D.map parity) = 0 ∨
      Module.finrank (ZMod 2) (D.map parity) = 1 by omega) with hP0 | hP1
  · have hD0 : Module.finrank (ZMod 2) D =
        Module.finrank (ZMod 2) ↥(D ⊓ LinearMap.ker parity) := by omega
    have hBle : Module.finrank (ZMod 2) ↥(D ⊓ U1) ≤
        Module.finrank (ZMod 2) ((D ⊓ U1).map cocodeCoord) + 1 := by omega
    omega
  · have hPne : D.map parity ≠ ⊥ := by
      intro hbot
      rw [hbot] at hP1
      simp at hP1
    have hex : ∃ x ∈ D, parity x ≠ 0 := by
      by_contra h
      apply hPne
      rw [Submodule.eq_bot_iff]
      intro y hy
      obtain ⟨x, hxD, rfl⟩ := Submodule.mem_map.1 hy
      by_contra hx0
      exact h ⟨x, hxD, hx0⟩
    obtain ⟨x₀, hx₀D, hx₀ne⟩ := hex
    have hx₀1 : parity x₀ = 1 := by
      have hlt : (parity x₀).val < 2 := ZMod.val_lt _
      rcases (show (parity x₀).val = 0 ∨ (parity x₀).val = 1 by omega) with h0 | h1
      · rw [ZMod.val_eq_zero] at h0
        exact absurd h0 hx₀ne
      · exact (ZMod.val_eq_one (by norm_num) (parity x₀)).1 h1
    have hfD : twoΩCls ∉ D := by
      intro hfD
      have hzero := hbD twoΩCls hfD x₀ hx₀D
      rw [polarBilin_twoΩCls, hx₀1] at hzero
      norm_num at hzero
    have hBbot : (D ⊓ U1) ⊓ LinearMap.ker cocodeCoord = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxspan : x ∈ Submodule.span (ZMod 2) {twoΩCls} := hker_le hx
      change x ∈ ZMod 2 ∙ twoΩCls at hxspan
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxspan
      rw [smul_eq_zero]
      have hlt : c.val < 2 := ZMod.val_lt c
      rcases (show c.val = 0 ∨ c.val = 1 by omega) with hc | hc
      · left
        exact (ZMod.val_eq_zero c).1 hc
      · right
        have hc1 : c = 1 := (ZMod.val_eq_one (by norm_num) c).1 hc
        rw [hc1, one_smul] at hx
        exact absurd hx.1.1 hfD
    have hBexact : Module.finrank (ZMod 2) ↥(D ⊓ U1) =
        Module.finrank (ZMod 2) ((D ⊓ U1).map cocodeCoord) := by
      have h := hdelta
      rw [hBbot] at h
      simp at h
      omega
    have hD1 : Module.finrank (ZMod 2) D =
        Module.finrank (ZMod 2) ↥(D ⊓ LinearMap.ker parity) + 1 := by omega
    omega

end CFSG.Monster.VisQuot

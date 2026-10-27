module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4Psi
public import CFSG.Quasithin.Vol2.KGFactC31J4M4KW3
public import CFSG.Quasithin.Vol2.KGFactC31J4Off

public section

namespace CFSG.Quasithin.KGC31.J4M4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31
open CFSG.Quasithin.KGC31.J4 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

@[expose] noncomputable def phi (u : Fin 5 → ZMod 2) : Row := kwRow (ptIdx u)

@[expose] noncomputable def pairPt : Subgroup (G₀ × ↥(StatedSL 5 (ZMod 2))) where
  carrier := {q | ∀ u : Fin 5 → ZMod 2, u ≠ 0 → q.1 • phi u = phi (mat q.2 *ᵥ u)}
  one_mem' := fun u _ => by
    show (1 : G₀) • phi u = phi (mat 1 *ᵥ u)
    rw [one_smul, B5.Ln.mat_one, Matrix.one_mulVec]
  mul_mem' := fun {q q'} hq hq' u hu => by
    have hu' : mat q'.2 *ᵥ u ≠ 0 := fun h0 => hu (by
      rw [← B5.Ln.mulVec_inv_mulVec q'.2 u, h0, Matrix.mulVec_zero])
    show (q.1 * q'.1) • phi u = phi (mat (q.2 * q'.2) *ᵥ u)
    rw [mul_smul, hq' u hu, hq _ hu', B5.Ln.mat_mul, Matrix.mulVec_mulVec]
  inv_mem' := fun {q} hq u hu => by
    have hu' : mat q.2⁻¹ *ᵥ u ≠ 0 := fun h0 => hu (by
      rw [← B5.Ln.mulVec_mulVec_inv q.2 u, h0, Matrix.mulVec_zero])
    have e := hq _ hu'
    rw [B5.Ln.mulVec_mulVec_inv] at e
    show q.1⁻¹ • phi u = phi (mat q.2⁻¹ *ᵥ u)
    rw [← e, inv_smul_smul]

@[expose] noncomputable def pairD : Subgroup (G₀ × ↥(StatedSL 5 (ZMod 2))) :=
  Subgroup.closure {(CFSG.Quasithin.KGJ4.w1, gam 0), (CFSG.Quasithin.KGJ4.w2, gam 1)}

theorem map_fst_pairD : pairD.map (MonoidHom.fst G₀ ↥(StatedSL 5 (ZMod 2))) =
    CFSG.Quasithin.KGJ4.M4 := by
  rw [pairD, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_snd_pairD : pairD.map (MonoidHom.snd G₀ ↥(StatedSL 5 (ZMod 2))) = ⊤ := by
  rw [pairD, MonoidHom.map_closure, Set.image_pair]
  exact closure_gam_eq_top

theorem exists_pair (x : ↥CFSG.Quasithin.KGJ4.M4) : ∃ γ, ((x : G₀), γ) ∈ pairD := by
  have h : (x : G₀) ∈ pairD.map (MonoidHom.fst G₀ ↥(StatedSL 5 (ZMod 2))) := by
    rw [map_fst_pairD]
    exact x.2
  obtain ⟨q, hq, hqx⟩ := h
  refine ⟨q.2, ?_⟩
  rw [← hqx]
  exact hq

theorem fst_mem_M4 {q : G₀ × ↥(StatedSL 5 (ZMod 2))} (hq : q ∈ pairD) :
    q.1 ∈ CFSG.Quasithin.KGJ4.M4 := by
  rw [← map_fst_pairD]
  exact ⟨q, hq, rfl⟩

section Pairs

variable (hM : MatFacts) (hc : chkF () = true)
include hM hc

@[expose] noncomputable def pairF : Subgroup (G₀ × ↥(StatedSL 5 (ZMod 2))) where
  carrier := {q | ∃ h : q.1 ∈ eNorm (fJ_basis hM hc), eGL (fJ_basis hM hc) ⟨q.1, h⟩ = psi q.2}
  one_mem' := ⟨Subgroup.one_mem _, by
    show eGL (fJ_basis hM hc) 1 = psi 1
    rw [map_one, map_one]⟩
  mul_mem' := fun {q q'} ⟨h, e⟩ ⟨h', e'⟩ => ⟨Subgroup.mul_mem _ h h', by
    show eGL (fJ_basis hM hc) (⟨q.1, h⟩ * ⟨q'.1, h'⟩) = psi (q.2 * q'.2)
    rw [map_mul, map_mul, e, e']⟩
  inv_mem' := fun {q} ⟨h, e⟩ => ⟨Subgroup.inv_mem _ h, by
    show eGL (fJ_basis hM hc) (⟨q.1, h⟩⁻¹) = psi q.2⁻¹
    rw [map_inv, map_inv, e]⟩

theorem gen_pairF {w : ℕ} (hw : w < 2) : (m4gen w, gam w) ∈ pairF hM hc := by
  refine ⟨M4_le_eNorm hM hc (m4gen_mem w), Units.ext ?_⟩
  rw [eGL_coe, psi_coe]
  refine eMat_eq _ _ _ fun i => ?_
  rw [conj_fJ hM hc hw i, psiMat_gam_col hw i]

theorem pairD_le_pairF : pairD ≤ pairF hM hc := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro q (rfl | rfl)
  · exact gen_pairF hM hc (w := 0) (by norm_num)
  · exact gen_pairF hM hc (w := 1) (by norm_num)

theorem pair_unique {x : G₀} {γ γ' : ↥(StatedSL 5 (ZMod 2))} (h : (x, γ) ∈ pairD)
    (h' : (x, γ') ∈ pairD) : γ = γ' := by
  have h1 : ((x, γ)⁻¹ * (x, γ') : G₀ × ↥(StatedSL 5 (ZMod 2))) ∈ pairD :=
    pairD.mul_mem (pairD.inv_mem h) h'
  obtain ⟨hn, e⟩ := pairD_le_pairF hM hc h1
  have h2 : (⟨((x, γ)⁻¹ * (x, γ') : G₀ × ↥(StatedSL 5 (ZMod 2))).1, hn⟩ :
      ↥(eNorm (fJ_basis hM hc))) = 1 :=
    Subtype.ext (show x⁻¹ * x = 1 from inv_mul_cancel x)
  rw [h2, map_one] at e
  have h3 : γ⁻¹ * γ' = 1 := psi_injective (by rw [map_one]; exact e.symm)
  rw [← inv_mul_eq_one, h3]

omit hM hc in
theorem pair_mul_mem {x y : ↥CFSG.Quasithin.KGJ4.M4} {γ δ : ↥(StatedSL 5 (ZMod 2))}
    (hx : ((x : G₀), γ) ∈ pairD) (hy : ((y : G₀), δ) ∈ pairD) :
    (((x * y : ↥CFSG.Quasithin.KGJ4.M4) : G₀), γ * δ) ∈ pairD := by
  have h := pairD.mul_mem hx hy
  rw [Prod.mk_mul_mk] at h
  rw [Subgroup.coe_mul]
  exact h

@[expose] noncomputable def piM4 : ↥CFSG.Quasithin.KGJ4.M4 →* ↥(StatedSL 5 (ZMod 2)) :=
  MonoidHom.mk' (fun x => (exists_pair x).choose) fun x y =>
    pair_unique hM hc (exists_pair (x * y)).choose_spec
      (pair_mul_mem (exists_pair x).choose_spec (exists_pair y).choose_spec)

theorem piM4_mem (x : ↥CFSG.Quasithin.KGJ4.M4) : ((x : G₀), piM4 hM hc x) ∈ pairD :=
  (exists_pair x).choose_spec

theorem piM4_eq {x : ↥CFSG.Quasithin.KGJ4.M4} {γ : ↥(StatedSL 5 (ZMod 2))}
    (h : ((x : G₀), γ) ∈ pairD) : piM4 hM hc x = γ :=
  pair_unique hM hc (piM4_mem hM hc x) h

theorem piM4_surjective : Function.Surjective (piM4 hM hc) := by
  intro γ
  have h : γ ∈ pairD.map (MonoidHom.snd G₀ ↥(StatedSL 5 (ZMod 2))) := by
    rw [map_snd_pairD]
    exact Subgroup.mem_top γ
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨⟨q.1, fst_mem_M4 hq⟩, piM4_eq hM hc hq⟩

theorem piM4_pairF (x : ↥CFSG.Quasithin.KGJ4.M4) :
    ∃ h : (x : G₀) ∈ eNorm (fJ_basis hM hc),
      eGL (fJ_basis hM hc) ⟨(x : G₀), h⟩ = psi (piM4 hM hc x) := by
  obtain ⟨h, e⟩ := pairD_le_pairF hM hc (piM4_mem hM hc x)
  exact ⟨h, e⟩

theorem piM4_conj (x : ↥CFSG.Quasithin.KGJ4.M4) (c : Fin 10 → ZMod 2) :
    (x : G₀) * eElt fJ c * (x : G₀)⁻¹ = eElt fJ (psiMat (piM4 hM hc x) *ᵥ c) := by
  obtain ⟨h, e⟩ := piM4_pairF hM hc x
  have e' := congrArg (fun g : GL (Fin 10) (ZMod 2) => (g : Matrix (Fin 10) (Fin 10) (ZMod 2))) e
  simp only [eGL_coe, psi_coe] at e'
  rw [← e', ← conj_eq_eElt_mulVec (fJ_basis hM hc) ⟨(x : G₀), h⟩ c]

end Pairs

section Points

variable (hM : MatFacts) (hk : chkKW () = true)
include hM hk

theorem gen_pairPt {l : ℕ} (hl : l < 2) : (m4gen l, gam l) ∈ pairPt := by
  intro u hu
  obtain ⟨hk31, hu'⟩ := ptIdx_spec hu
  show m4gen l • phi u = phi (mat (gam l) *ᵥ u)
  conv_rhs => rw [← hu']
  rw [gam_ptCodes hl hk31, phi, phi, ptIdx_vec5 (kwSig_lt l hl _ hk31)]
  exact m4gen_smul_kwRow hk hM hl hk31

theorem pairD_le_pairPt : pairD ≤ pairPt := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro q (rfl | rfl)
  · exact gen_pairPt hM hk (l := 0) (by norm_num)
  · exact gen_pairPt hM hk (l := 1) (by norm_num)

theorem piM4_smul (hc : chkF () = true) (x : ↥CFSG.Quasithin.KGJ4.M4)
    {u : Fin 5 → ZMod 2} (hu : u ≠ 0) :
    (x : G₀) • phi u = phi (mat (piM4 hM hc x) *ᵥ u) :=
  pairD_le_pairPt hM hk (piM4_mem hM hc x) u hu

end Points

theorem kw3 (hF : J4Facts) (hc : chkF () = true) (hk : chkKW () = true)
    {x : ↥CFSG.Quasithin.KGJ4.M4} (hx : piM4 hF.mat hc x ∈ Off5.stab0) :
    gJ * (x : G₀) * gJ⁻¹ ∈ Hj := by
  apply QT2.mem_Hj_of_smul_root hF
  have hv1 : vec5 (ptCodes.getD 0 0) = Pi.single 0 1 := by decide
  have h1 : mat (piM4 hF.mat hc x) *ᵥ vec5 (ptCodes.getD 0 0) = vec5 (ptCodes.getD 0 0) := by
    rw [hv1]
    funext i
    have := (Off5.mem_stab0.mp hx) i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [this]
  have h2 := piM4_smul hF.mat hk hc x (vec5_ne_zero (k := 0) (by norm_num))
  rw [h1, phi, ptIdx_vec5 (k := 0) (by norm_num), kwRow_zero hk hF.mat] at h2
  rw [mul_smul, mul_smul, h2, smul_inv_smul]

end CFSG.Quasithin.KGC31.J4M4

end

module

public import CFSG.Sporadic.Co1Patterson.GraphAdj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)


theorem orbOK_orbE : orbOK brayArr brayInvArr eRows orbE = true := by
  have := exact_orbE
  unfold exactOK at this
  simp only [Bool.and_eq_true] at this
  exact this.1.1

theorem size_orbE : orbE.c.pts.size = 12600 := by
  have := exact_orbE
  unfold exactOK at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

theorem exists_hE (k : ℕ) (hk : k < orbE.c.pts.size) :
    ∃ g ∈ Subgroup.closure (brayNC '' {l | l < brayArr.size}),
      matHom g = rowsMatrix 24 orbE.hs[k]! ∧ matHom g⁻¹ = rowsMatrix 24 orbE.his[k]! ∧
      matHom (g * (vE : NativeSporadic.Co1) * g⁻¹) = rowsMatrix 24 orbE.c.pts[k]! :=
  orbOK_sound matHom orbOK_orbE brayNC (fun l hl => nrep_brayArr l hl) vE nrep_eRows k hk

noncomputable irreducible_def hE
    (k : ℕ) : NativeSporadic.Co1 :=
  if hk : k < orbE.c.pts.size then Classical.choose (exists_hE k hk) else 1

theorem hE_spec {k : ℕ} (hk : k < orbE.c.pts.size) :
    hE k ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ∧ NRep orbE.hs[k]! (hE k) ∧
      NRep orbE.his[k]! (hE k)⁻¹ ∧
      NRep orbE.c.pts[k]! (hE k * (vE : NativeSporadic.Co1) * (hE k)⁻¹) := by
  have h := Classical.choose_spec (exists_hE k hk)
  rw [show hE k = Classical.choose (exists_hE k hk) by rw [hE_def, dif_pos hk]]
  refine ⟨closure_brayArr ▸ h.1, h.2.1, h.2.2.1, h.2.2.2⟩

@[expose] noncomputable def xE (k : ℕ) : NativeSporadic.Co1 := hE k * gElt (repJ 1)

@[expose] noncomputable def cV (k : ℕ) : Vt := xE k • vA

theorem cV_eq (k : ℕ) : cV k = hE k • vE := by
  unfold cV xE
  rw [mul_smul]
  rfl

theorem nrep_xE {k : ℕ} (hk : k < orbE.c.pts.size) : NRep (xeK orbE k) (xE k) :=
  (hE_spec hk).2.1.mul (nrep_repX dagOK_true 1)

theorem nrep_xEinv {k : ℕ} (hk : k < orbE.c.pts.size) : NRep (xeiK orbE k) (xE k)⁻¹ := by
  unfold xE
  rw [_root_.mul_inv_rev]
  exact (nrep_repXi dagOK_true (by norm_num)).mul (hE_spec hk).2.2.1

theorem nrep_cV {k : ℕ} (hk : k < orbE.c.pts.size) :
    NRep orbE.c.pts[k]! (cV k : NativeSporadic.Co1) := by
  rw [cV_eq, coe_smul_conjVert]
  exact (hE_spec hk).2.2.2

theorem valid_pts {k : ℕ} (hk : k < orbE.c.pts.size) :
    CFSG.Sporadic.Co1.InvNative.validRows orbE.c.pts[k]! = true :=
  ((orbOK_parts orbOK_orbE).2.2.2.2.2.2.2.1 k hk).1

theorem valid_xeK {k : ℕ} (hk : k < orbE.c.pts.size) :
    CFSG.Sporadic.Co1.InvNative.validRows (xeK orbE k) = true :=
  validRows_mul ((orbOK_parts orbOK_orbE).2.2.2.2.2.2.2.1 k hk).2.1
    ((dagOK_parts dagOK_true).2 _ (repJ_mem (by norm_num)).1 (repJ_mem (by norm_num)).2).1

theorem valid_xeiK {k : ℕ} (hk : k < orbE.c.pts.size) :
    CFSG.Sporadic.Co1.InvNative.validRows (xeiK orbE k) = true :=
  validRows_mul ((dagOK_parts dagOK_true).2 _ (repJ_mem (by norm_num)).1
    (repJ_mem (by norm_num)).2).2.1 ((orbOK_parts orbOK_orbE).2.2.2.2.2.2.2.1 k hk).2.2.1

theorem adj_vA_cV {k : ℕ} (hk : k < orbE.c.pts.size) : (a2Graph aNC).Adj vA (cV k) := by
  rw [a2_adj_vA_iff, cV_eq]
  exact ⟨hE k, (hE_spec hk).1, rfl⟩

theorem exists_cV {v : Vt} (h : (a2Graph aNC).Adj vA v) :
    ∃ k < orbE.c.pts.size, v = cV k := by
  rw [a2_adj_vA_iff] at h
  obtain ⟨i, hi, hv⟩ := (mem_cOrb_iff_of_exactOK exact_orbE vE nrep_eRows v).1 h
  exact ⟨i, hi, Subtype.ext (NRep.unique hv (nrep_cV hi))⟩

theorem adj_iff_adjC {X Xi V : Native.Rows} {x : NativeSporadic.Co1} {v : Vt} (hX : NRep X x)
    (hXi : NRep Xi x⁻¹) (hV : NRep V v)
    (hXv : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (hXiv : CFSG.Sporadic.Co1.InvNative.validRows Xi = true)
    (hVv : CFSG.Sporadic.Co1.InvNative.validRows V = true) :
    (a2Graph aNC).Adj (x • vA) v ↔ adjC (ptSet orbE) X Xi V = true :=
  adj_iff_contains hX hXi hV (validRows_mul (validRows_mul hXiv hVv) hXv)

theorem adj_cV_iff {k : ℕ} (hk : k < orbE.c.pts.size) {V : Native.Rows} {v : Vt} (hV : NRep V v)
    (hVv : CFSG.Sporadic.Co1.InvNative.validRows V = true) :
    (a2Graph aNC).Adj (cV k) v ↔ adjK orbE (ptSet orbE) V k = true :=
  adj_iff_adjC (nrep_xE hk) (nrep_xEinv hk) hV (valid_xeK hk) (valid_xeiK hk) hVv

@[expose] noncomputable def nbrV (x : NativeSporadic.Co1) (k : ℕ) : Vt := (x * xE k) • vA

theorem nbrV_eq (x : NativeSporadic.Co1) (k : ℕ) : nbrV x k = x • cV k := by
  unfold nbrV cV
  rw [mul_smul]

theorem adj_nbrV (x : NativeSporadic.Co1) {k : ℕ} (hk : k < orbE.c.pts.size) :
    (a2Graph aNC).Adj (x • vA) (nbrV x k) := by
  rw [nbrV_eq]
  exact a2Graph_adj_smul x (adj_vA_cV hk)

theorem exists_nbrV {x : NativeSporadic.Co1} {w : Vt} (h : (a2Graph aNC).Adj (x • vA) w) :
    ∃ k < orbE.c.pts.size, w = nbrV x k := by
  have h' : (a2Graph aNC).Adj vA (x⁻¹ • w) := by
    have := a2Graph_adj_smul x⁻¹ h
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk, hkw⟩ := exists_cV h'
  refine ⟨k, hk, ?_⟩
  rw [nbrV_eq, ← hkw, smul_inv_smul]

theorem nrep_nbrX {X Xi : Native.Rows} {x : NativeSporadic.Co1} (hX : NRep X x)
    (hXi : NRep Xi x⁻¹) {k : ℕ} (hk : k < orbE.c.pts.size) :
    NRep (nbrX orbE (X, Xi) k).1 (x * xE k) ∧ NRep (nbrX orbE (X, Xi) k).2 (x * xE k)⁻¹ := by
  refine ⟨hX.mul (nrep_xE hk), ?_⟩
  show NRep (Native.mul (xeiK orbE k) Xi) (x * xE k)⁻¹
  rw [_root_.mul_inv_rev]
  exact (nrep_xEinv hk).mul hXi

theorem valid_nbrX {X Xi : Native.Rows} (hXv : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (hXiv : CFSG.Sporadic.Co1.InvNative.validRows Xi = true) {k : ℕ}
    (hk : k < orbE.c.pts.size) :
    CFSG.Sporadic.Co1.InvNative.validRows (nbrX orbE (X, Xi) k).1 = true ∧
      CFSG.Sporadic.Co1.InvNative.validRows (nbrX orbE (X, Xi) k).2 = true :=
  ⟨validRows_mul hXv (valid_xeK hk), validRows_mul (valid_xeiK hk) hXiv⟩

theorem nrep_vtxR {X Xi : Native.Rows} {x : NativeSporadic.Co1} (hX : NRep X x)
    (hXi : NRep Xi x⁻¹) : NRep (vtxR X Xi) ((x • vA : Vt) : NativeSporadic.Co1) :=
  nrep_conjA hX hXi

theorem valid_vtxR {X Xi : Native.Rows} (hXv : CFSG.Sporadic.Co1.InvNative.validRows X = true)
    (hXiv : CFSG.Sporadic.Co1.InvNative.validRows Xi = true) :
    CFSG.Sporadic.Co1.InvNative.validRows (vtxR X Xi) = true :=
  validRows_mul (validRows_mul hXv twoA_misc_parts.2.2.2.2.2.1) hXiv

end CFSG.Sporadic.Co1Patterson

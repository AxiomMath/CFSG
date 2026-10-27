module

public import Certificates.Certificate7245
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4EOrbit

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.Native Matrix
open CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9
open scoped commutatorElement

@[expose] noncomputable def nJ : J :=
  (wordProd xJ nWordL)⁻¹ * pathElt (repPaths.getD 5 []) * (wordProd xJ nWordR)⁻¹

@[expose] noncomputable def gPt (c : ℕ) : J := eta uJ 11 c * nJ

@[expose] noncomputable def pJ (i : ℕ) : J :=
  if i < 6 then eta uJ 11 (extraMasks.getD i 0) else wordProd xJ (sWords.getD (i - 6) [])

@[expose] noncomputable def xM : J := wordProd xJ xWord

@[expose] noncomputable def qJ (i : ℕ) : J := ⁅pJ i, xM⁆

@[expose] noncomputable def cJ : J := wordProd xJ cWord

theorem nWordL_letters : ∀ ℓ ∈ nWordL, ℓ ∈ letters := by decide +kernel

theorem nWordR_letters : ∀ ℓ ∈ nWordR, ℓ ∈ letters := by decide +kernel

theorem sWords_letters : ∀ i < 6, ∀ ℓ ∈ sWords.getD i [], ℓ ∈ letters := by decide +kernel

theorem xWord_letters : ∀ ℓ ∈ xWord, ℓ ∈ letters := by decide +kernel

theorem cWord_letters : ∀ ℓ ∈ cWord, ℓ ∈ letters := by decide +kernel

theorem u5_letters : ∀ l ∈ repPaths.getD 5 [], l = 1 ∨ l = 2 := repPaths_letters 5 (by norm_num)

noncomputable abbrev T₀ : Array (Array V2) := uTab (locMats ()) (locInvs ())

theorem eq_of_eqRows' {g g' : J} {X Y : Array V2} (hg : Mx g = rowsMatrix X)
    (hg' : Mx g' = rowsMatrix Y) (h : eqRows X Y = true) : g = g' :=
  Mx_injective (by rw [hg, hg', rowsMatrix_eq_of_eqRows h])

theorem smul_eq_of_frApply {y : J} {P : Array V2} (hy : Mx y = rowsMatrix P) {v w : V2}
    (h : (frApply (frTable P) v).beq w = true) : y • toRow w.toVec = toRow v.toVec := by
  have h1 : y⁻¹ • toRow v.toVec = toRow w.toVec := by
    rw [← ofRow_inj, inv_smul_row, ← Mx_apply, hy]
    show v.toVec ᵥ* rowsMatrix P = w.toVec
    rw [← frApply_toVec_eq_vecMul, V2.beq_iff.mp h]
  rw [← h1, smul_inv_smul]

theorem rowsMatrix_commRows (P Pi X Xi : Array V2) :
    rowsMatrix (commRows P Pi X Xi) =
      rowsMatrix P * rowsMatrix X * rowsMatrix Pi * rowsMatrix Xi := by
  rw [commRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem rowsMatrix_ne_of_rowsDiffer {A B : Array V2} (h : rowsDiffer A B = true) :
    rowsMatrix A ≠ rowsMatrix B := by
  unfold rowsDiffer at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hd⟩ := h
  intro e
  apply differs_toVec hd
  funext j
  have := congrFun (congrFun e ⟨i, hi⟩) j
  rwa [rowsMatrix_apply, rowsMatrix_apply] at this

section Mat

variable (hM : MatFacts)
include hM

theorem Mx_eta' (c : ℕ) : Mx (eta uJ 11 c) = rowsMatrix (eR T₀ c) := Mx_eta hM 11 le_rfl c

theorem Mx_wordProd_inv {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    Mx (wordProd xJ w)⁻¹ = rowsMatrix (wordRows (locMats ()) (locInvs ()) (invWord w)) := by
  rw [← wordProd_invWord w hw, Mx_wordProd hM]

theorem Mx_u5 : Mx (pathElt (repPaths.getD 5 [])) = rowsMatrix (u5Rows ()) :=
  Mx_pathElt hM _ u5_letters

theorem Mx_u5_inv :
    Mx (pathElt (repPaths.getD 5 []))⁻¹ = rowsMatrix (u5Inv ()) := by
  have h1 : rowsMatrix (u5Rows ()) * rowsMatrix (u5Inv ()) = 1 := by
    rw [← rowsMatrix_mulRows, rowsMatrix_eq_of_eqRows Certificates.certificate7245.1,
      rowsMatrix_idRows]
  have h2 : Mx (pathElt (repPaths.getD 5 []))⁻¹ * Mx (pathElt (repPaths.getD 5 [])) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [Mx_u5 hM] at h2
  calc Mx (pathElt (repPaths.getD 5 []))⁻¹
      = Mx (pathElt (repPaths.getD 5 []))⁻¹ * (rowsMatrix (u5Rows ()) * rowsMatrix (u5Inv ())) := by
        rw [h1, Matrix.mul_one]
    _ = rowsMatrix (u5Inv ()) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem Mx_nJ :
    Mx nJ = rowsMatrix (nRows (locMats ()) (locInvs ())) := by
  rw [nJ, map_mul, map_mul, Mx_wordProd_inv hM nWordL_letters, Mx_u5 hM,
    Mx_wordProd_inv hM nWordR_letters, nRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem Mx_nJ_inv :
    Mx nJ⁻¹ = rowsMatrix (nInvRows (locMats ()) (locInvs ())) := by
  have e : nJ⁻¹ = wordProd xJ nWordR * (pathElt (repPaths.getD 5 []))⁻¹ * wordProd xJ nWordL := by
    rw [nJ]; group
  rw [e, map_mul, map_mul, Mx_wordProd hM, Mx_u5_inv hM, Mx_wordProd hM, nInvRows,
    rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem Mx_pJ (i : ℕ) : Mx (pJ i) = rowsMatrix (pRows (locMats ()) (locInvs ()) T₀ i) := by
  unfold pJ pRows
  split_ifs
  · exact Mx_eta' hM _
  · exact Mx_wordProd hM _

theorem Mx_pJ_inv (i : ℕ) (hi : i < 12) :
    Mx (pJ i)⁻¹ = rowsMatrix (pInvRows (locMats ()) (locInvs ()) T₀ i) := by
  unfold pJ pInvRows
  split_ifs with h
  · rw [eta_inv hM]
    exact Mx_eta' hM _
  · exact Mx_wordProd_inv hM (sWords_letters (i - 6) (by omega))

theorem Mx_xM : Mx xM = rowsMatrix (wordRows (locMats ()) (locInvs ()) xWord) := Mx_wordProd hM _

theorem Mx_xM_inv :
    Mx xM⁻¹ = rowsMatrix (wordRows (locMats ()) (locInvs ()) (invWord xWord)) :=
  Mx_wordProd_inv hM xWord_letters

theorem Mx_qJ (i : ℕ) (hi : i < 12) :
    Mx (qJ i) = rowsMatrix (commRows (pRows (locMats ()) (locInvs ()) T₀ i)
      (pInvRows (locMats ()) (locInvs ()) T₀ i) (wordRows (locMats ()) (locInvs ()) xWord)
      (wordRows (locMats ()) (locInvs ()) (invWord xWord))) := by
  rw [qJ, commutatorElement_def, map_mul, map_mul, map_mul, Mx_pJ hM i, Mx_xM hM,
    Mx_pJ_inv hM i hi, Mx_xM_inv hM, commRows, rowsMatrix_mulRows, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

theorem Mx_qJ_inv (i : ℕ) (hi : i < 12) :
    Mx (qJ i)⁻¹ = rowsMatrix (commRows (wordRows (locMats ()) (locInvs ()) xWord)
      (wordRows (locMats ()) (locInvs ()) (invWord xWord)) (pRows (locMats ()) (locInvs ()) T₀ i)
      (pInvRows (locMats ()) (locInvs ()) T₀ i)) := by
  have e : (qJ i)⁻¹ = xM * pJ i * xM⁻¹ * (pJ i)⁻¹ := by
    rw [qJ, commutatorElement_def]; group
  rw [e, map_mul, map_mul, map_mul, Mx_pJ hM i, Mx_xM hM, Mx_pJ_inv hM i hi, Mx_xM_inv hM,
    commRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows]

theorem Mx_cJ : Mx cJ = rowsMatrix (wordRows (locMats ()) (locInvs ()) cWord) := Mx_wordProd hM _

theorem ofRow_gPt (c : ℕ) :
    ofRow (gPt c • w₀) = (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c).toVec := by
  have e : (gPt c)⁻¹ = nJ⁻¹ * eta uJ 11 c := by rw [gPt, _root_.mul_inv_rev, eta_inv hM]
  rw [smul_row, ← Mx_apply, e, map_mul, Mx_nJ_inv hM, Mx_eta' hM, ← rowsMatrix_mulRows, ptVec,
    frApply_toVec_eq_vecMul]
  rfl

theorem gPt_row (c : ℕ) :
    gPt c • w₀ = toRow (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c).toVec := by
  rw [← ofRow_inj, ofRow_gPt hM]; rfl

end Mat

theorem chkNWith_spec {T : Array (Array V2)} {N Ni : Array V2} (h : chkNWith T N Ni = true) :
    ∀ c ∈ v0Gens, ∃ d ∈ v0Masks, eqRows (mulRows (mulRows N (eR T c)) Ni) (eR T d) = true := by
  unfold chkNWith at h
  simpa only [List.all_eq_true, List.any_eq_true] using h

theorem chkPtsWith_spec {Ni : Array V2} {T : Array (Array V2)} (h : chkPtsWith Ni T = true) :
    (∀ c ∈ ptMasks, differs (ptVec Ni T c) rootV = true) ∧
      ∀ c ∈ ptMasks, ∀ d ∈ ptMasks, c ≠ d → differs (ptVec Ni T c) (ptVec Ni T d) = true := by
  unfold chkPtsWith at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun c hc d hd hcd => ?_⟩
  rcases h.2 c hc d hd with h' | h'
  · exact absurd h' hcd
  · exact h'

theorem chkPWith_spec {loc inv T : Array (Array V2)} {Ni X Xi : Array V2}
    (h : chkPWith loc inv T Ni X Xi = true) :
    (∀ i < 12, (∀ c ∈ ptMasks,
      (frApply (frTable (pRows loc inv T i)) (ptVec Ni T c)).beq (ptVec Ni T c) = true) ∧
      ∀ c ∈ v0Gens, eqRows (mulRows (pRows loc inv T i) (eR T c))
        (mulRows (eR T c) (pRows loc inv T i)) = true) ∧
    (∀ c ∈ ptMasks, (frApply (frTable X) (ptVec Ni T c)).beq (ptVec Ni T c) = true) ∧
    (∀ c ∈ v0Gens, ∃ d ∈ v0Masks, eqRows (mulRows (mulRows X (eR T c)) Xi) (eR T d) = true) ∧
    rowsDiffer (mulRows (mulRows X (eR T 1131)) Xi) (eR T 1131) = true := by
  unfold chkPWith fixesPts centV0 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem chkQWith_spec {loc inv T : Array (Array V2)} {X Xi : Array V2}
    (h : chkQWith loc inv T X Xi = true) : ∀ i < 12,
    eqRows (mulRows (commRows (pRows loc inv T i) (pInvRows loc inv T i) X Xi)
      (commRows (pRows loc inv T i) (pInvRows loc inv T i) X Xi)) (eR T (sqTab.getD i 0)) = true ∧
    ∀ j < 12, eqRows (commRows (commRows (pRows loc inv T i) (pInvRows loc inv T i) X Xi)
      (commRows X Xi (pRows loc inv T i) (pInvRows loc inv T i))
      (commRows (pRows loc inv T j) (pInvRows loc inv T j) X Xi)
      (commRows X Xi (pRows loc inv T j) (pInvRows loc inv T j)))
      (eR T ((commTab.getD i []).getD j 0)) = true := by
  unfold chkQWith at h
  simpa only [Bool.and_eq_true, List.all_eq_true, List.mem_range] using h

theorem chkCWith_spec {Ni : Array V2} {T : Array (Array V2)} {C : Array V2}
    (h : chkCWith Ni T C = true) :
    (∀ c ∈ v0Gens, eqRows (mulRows C (eR T c)) (mulRows (eR T c) C) = true) ∧
    (frApply (frTable C) (ptVec Ni T 0)).beq (ptVec Ni T 0) = true ∧
    (frApply (frTable C) (ptVec Ni T 1)).beq (ptVec Ni T 1) = true ∧
    (frApply (frTable C) (ptVec Ni T 16)).beq (ptVec Ni T 17) = true ∧
    (frApply (frTable C) (ptVec Ni T 17)).beq (ptVec Ni T 16) = true := by
  unfold chkCWith centV0 at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

section Facts


theorem mem_V0_of_mem_v0Masks {d : ℕ} (hd : d ∈ v0Masks) : eta uJ 11 d ∈ V0 := by
  have hM := j4Facts.mat
  have h1 : eta uJ 11 422 ∈ V0 := Subgroup.subset_closure (by simp)
  have h2 : eta uJ 11 553 ∈ V0 := Subgroup.subset_closure (by simp)
  have h3 : eta uJ 11 1131 ∈ V0 := Subgroup.subset_closure (by simp)
  have e12 : eta uJ 11 911 = eta uJ 11 422 * eta uJ 11 553 := by rw [eta_mul_eta hM]; rfl
  have e13 : eta uJ 11 1485 = eta uJ 11 422 * eta uJ 11 1131 := by rw [eta_mul_eta hM]; rfl
  have e23 : eta uJ 11 1602 = eta uJ 11 553 * eta uJ 11 1131 := by rw [eta_mul_eta hM]; rfl
  have e123 : eta uJ 11 2020 = eta uJ 11 911 * eta uJ 11 1131 := by rw [eta_mul_eta hM]; rfl
  simp only [v0Masks, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [eta_zero]; exact V0.one_mem
  · exact h1
  · exact h2
  · rw [e12]; exact V0.mul_mem h1 h2
  · exact h3
  · rw [e13]; exact V0.mul_mem h1 h3
  · rw [e23]; exact V0.mul_mem h2 h3
  · rw [e123, e12]; exact V0.mul_mem (V0.mul_mem h1 h2) h3

theorem mem_normalizer_V0_of_conj {y : J}
    (h : ∀ c ∈ v0Gens, ∃ d ∈ v0Masks, y * eta uJ 11 c * y⁻¹ = eta uJ 11 d) :
    y ∈ Subgroup.normalizer (V0 : Set J) := by
  refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun k hk => ?_
  have hle : V0 ≤ V0.comap (MulAut.conj y).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hc : ∀ c ∈ v0Gens, eta uJ 11 c ∈ V0.comap (MulAut.conj y).toMonoidHom := by
      intro c hc
      obtain ⟨d, hd, e⟩ := h c hc
      show y * eta uJ 11 c * y⁻¹ ∈ V0
      rw [e]
      exact mem_V0_of_mem_v0Masks hd
    rcases hg with rfl | rfl | rfl
    · exact hc 422 (by simp [v0Gens])
    · exact hc 553 (by simp [v0Gens])
    · exact hc 1131 (by simp [v0Gens])
  have hk' := Subgroup.mem_comap.mp (hle hk)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk'

theorem smul_coset_of_smul_row {y g g' : J} (h : y • (g • w₀) = g' • w₀) :
    y • (g • basePt) = g' • basePt := by
  rw [smul_smul, smul_basePt_eq_iff]
  apply mem_Hj_of_smul_root j4Facts
  calc (g'⁻¹ * (y * g)) • w₀ = g'⁻¹ • (y • (g • w₀)) := by rw [mul_smul, mul_smul]
    _ = w₀ := by rw [h, inv_smul_smul]

theorem nJ_mem_normalizer :
    nJ ∈ Subgroup.normalizer (V0 : Set J) := by
  have hM := j4Facts.mat
  refine mem_normalizer_V0_of_conj fun c hc => ?_
  have h := Certificates.certificate7245.2.1
  dsimp only [chkN] at h
  obtain ⟨d, hd, hcd⟩ := chkNWith_spec h c hc
  refine ⟨d, hd, eq_of_eqRows' ?_ (Mx_eta' hM d) hcd⟩
  rw [map_mul, map_mul, Mx_nJ hM, Mx_eta' hM, Mx_nJ_inv hM, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

theorem ptVec_facts :
    (∀ c ∈ ptMasks, differs (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c) rootV = true) ∧
      ∀ c ∈ ptMasks, ∀ d ∈ ptMasks, c ≠ d →
        differs (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c)
          (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ d) = true  := by
  have h := Certificates.certificate7245.2.2.1
  dsimp only [chkPts] at h
  exact chkPtsWith_spec h

theorem gPt_ne_basePt
    {c : ℕ} (hc : c ∈ ptMasks) : gPt c • basePt ≠ basePt := by
  have hM := j4Facts.mat
  intro h
  have hH : gPt c ∈ Hj := smul_basePt_eq_self_iff.mp h
  have h1 := smul_root_of_mem_Hj hM hH
  apply differs_toVec (ptVec_facts.1 c hc)
  rw [← ofRow_gPt hM, h1]
  rfl

theorem gPt_inj {c d : ℕ} (hc : c ∈ ptMasks) (hd : d ∈ ptMasks)
    (h : gPt c • basePt = gPt d • basePt) : c = d := by
  have hM := j4Facts.mat
  by_contra hcd
  have hH : (gPt d)⁻¹ * gPt c ∈ Hj := smul_basePt_eq_iff.mp h
  have h1 := smul_root_of_mem_Hj hM hH
  have h2 : gPt c • w₀ = gPt d • w₀ := by
    calc gPt c • w₀ = gPt d • (((gPt d)⁻¹ * gPt c) • w₀) := by rw [smul_smul, mul_inv_cancel_left]
      _ = gPt d • w₀ := by rw [h1]
  apply differs_toVec (ptVec_facts.2 c hc d hd hcd)
  rw [← ofRow_gPt hM, ← ofRow_gPt hM, h2]

theorem chkP_facts :
    (∀ i < 12, (∀ c ∈ ptMasks,
      (frApply (frTable (pRows (locMats ()) (locInvs ()) T₀ i))
        (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c)).beq
        (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c) = true) ∧
      ∀ c ∈ v0Gens, eqRows (mulRows (pRows (locMats ()) (locInvs ()) T₀ i) (eR T₀ c))
        (mulRows (eR T₀ c) (pRows (locMats ()) (locInvs ()) T₀ i)) = true) ∧
    (∀ c ∈ ptMasks,
      (frApply (frTable (wordRows (locMats ()) (locInvs ()) xWord))
        (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c)).beq
        (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ c) = true) ∧
    (∀ c ∈ v0Gens, ∃ d ∈ v0Masks,
      eqRows (mulRows (mulRows (wordRows (locMats ()) (locInvs ()) xWord) (eR T₀ c))
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))) (eR T₀ d) = true) ∧
    rowsDiffer (mulRows (mulRows (wordRows (locMats ()) (locInvs ()) xWord) (eR T₀ 1131))
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))) (eR T₀ 1131) = true := by
  have h := Certificates.certificate7245.2.2.2.1
  dsimp only [chkP] at h
  exact chkPWith_spec h

theorem pJ_commute {i : ℕ} (hi : i < 12) {c : ℕ} (hc : c ∈ v0Gens) :
    pJ i * eta uJ 11 c = eta uJ 11 c * pJ i := by
  have hM := j4Facts.mat
  refine eq_of_eqRows' ?_ ?_ ((chkP_facts.1 i hi).2 c hc)
  · rw [map_mul, Mx_pJ hM i, Mx_eta' hM, rowsMatrix_mulRows]
  · rw [map_mul, Mx_pJ hM i, Mx_eta' hM, rowsMatrix_mulRows]

theorem pJ_fix {i : ℕ} (hi : i < 12) {c : ℕ} (hc : c ∈ ptMasks) :
    pJ i • (gPt c • basePt) = gPt c • basePt := by
  have hM := j4Facts.mat
  refine smul_coset_of_smul_row ?_
  rw [gPt_row hM]
  exact smul_eq_of_frApply (Mx_pJ hM i) ((chkP_facts.1 i hi).1 c hc)

theorem xM_fix
    {c : ℕ} (hc : c ∈ ptMasks) : xM • (gPt c • basePt) = gPt c • basePt := by
  have hM := j4Facts.mat
  refine smul_coset_of_smul_row ?_
  rw [gPt_row hM]
  exact smul_eq_of_frApply (Mx_xM hM) (chkP_facts.2.1 c hc)

theorem xM_mem_normalizer :
    xM ∈ Subgroup.normalizer (V0 : Set J) := by
  have hM := j4Facts.mat
  refine mem_normalizer_V0_of_conj fun c hc => ?_
  obtain ⟨d, hd, hcd⟩ := chkP_facts.2.2.1 c hc
  refine ⟨d, hd, eq_of_eqRows' ?_ (Mx_eta' hM d) hcd⟩
  rw [map_mul, map_mul, Mx_xM hM, Mx_eta' hM, Mx_xM_inv hM, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

theorem xM_ne : xM * z0 * xM⁻¹ ≠ z0 := by
  have hM := j4Facts.mat
  intro h
  have ez : Mx z0 = rowsMatrix (eR T₀ 1131) := Mx_eta' hM 1131
  have e1 : Mx (xM * z0 * xM⁻¹) = rowsMatrix (mulRows (mulRows
      (wordRows (locMats ()) (locInvs ()) xWord) (eR T₀ 1131))
      (wordRows (locMats ()) (locInvs ()) (invWord xWord))) := by
    rw [map_mul, map_mul, Mx_xM hM, ez, Mx_xM_inv hM, rowsMatrix_mulRows, rowsMatrix_mulRows]
  apply rowsMatrix_ne_of_rowsDiffer chkP_facts.2.2.2
  rw [← e1, ← ez, h]

theorem chkQ_facts : ∀ i < 12,
    eqRows (mulRows (commRows (pRows (locMats ()) (locInvs ()) T₀ i)
        (pInvRows (locMats ()) (locInvs ()) T₀ i) (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord)))
      (commRows (pRows (locMats ()) (locInvs ()) T₀ i)
        (pInvRows (locMats ()) (locInvs ()) T₀ i) (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord)))) (eR T₀ (sqTab.getD i 0)) = true ∧
    ∀ j < 12, eqRows (commRows
      (commRows (pRows (locMats ()) (locInvs ()) T₀ i)
        (pInvRows (locMats ()) (locInvs ()) T₀ i) (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord)))
      (commRows (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))
        (pRows (locMats ()) (locInvs ()) T₀ i) (pInvRows (locMats ()) (locInvs ()) T₀ i))
      (commRows (pRows (locMats ()) (locInvs ()) T₀ j)
        (pInvRows (locMats ()) (locInvs ()) T₀ j) (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord)))
      (commRows (wordRows (locMats ()) (locInvs ()) xWord)
        (wordRows (locMats ()) (locInvs ()) (invWord xWord))
        (pRows (locMats ()) (locInvs ()) T₀ j) (pInvRows (locMats ()) (locInvs ()) T₀ j)))
      (eR T₀ ((commTab.getD i []).getD j 0)) = true := by
  have h := Certificates.certificate7245.2.2.2.2.1
  dsimp only [chkQ] at h
  exact chkQWith_spec h

theorem qJ_sq
    {i : ℕ} (hi : i < 12) : qJ i * qJ i = eta uJ 11 (sqTab.getD i 0) := by
  have hM := j4Facts.mat
  refine eq_of_eqRows' ?_ (Mx_eta' hM _) (chkQ_facts i hi).1
  rw [map_mul, Mx_qJ hM i hi, rowsMatrix_mulRows]

theorem qJ_comm {i j : ℕ} (hi : i < 12) (hj : j < 12) :
    ⁅qJ i, qJ j⁆ = eta uJ 11 ((commTab.getD i []).getD j 0) := by
  have hM := j4Facts.mat
  refine eq_of_eqRows' ?_ (Mx_eta' hM _) ((chkQ_facts i hi).2 j hj)
  rw [commutatorElement_def, map_mul, map_mul, map_mul, Mx_qJ hM i hi, Mx_qJ hM j hj,
    Mx_qJ_inv hM i hi, Mx_qJ_inv hM j hj]
  simp only [rowsMatrix_commRows, Matrix.mul_assoc]

theorem chkC_facts :
    (∀ c ∈ v0Gens, eqRows (mulRows (wordRows (locMats ()) (locInvs ()) cWord) (eR T₀ c))
      (mulRows (eR T₀ c) (wordRows (locMats ()) (locInvs ()) cWord)) = true) ∧
    (frApply (frTable (wordRows (locMats ()) (locInvs ()) cWord))
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 0)).beq
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 0) = true ∧
    (frApply (frTable (wordRows (locMats ()) (locInvs ()) cWord))
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 1)).beq
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 1) = true ∧
    (frApply (frTable (wordRows (locMats ()) (locInvs ()) cWord))
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 16)).beq
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 17) = true ∧
    (frApply (frTable (wordRows (locMats ()) (locInvs ()) cWord))
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 17)).beq
      (ptVec (nInvRows (locMats ()) (locInvs ())) T₀ 16) = true := by
  have h := Certificates.certificate7245.2.2.2.2.2
  dsimp only [chkC] at h
  exact chkCWith_spec h

theorem cJ_commute
    {c : ℕ} (hc : c ∈ v0Gens) : cJ * eta uJ 11 c = eta uJ 11 c * cJ := by
  have hM := j4Facts.mat
  refine eq_of_eqRows' ?_ ?_ (chkC_facts.1 c hc)
  · rw [map_mul, Mx_cJ hM, Mx_eta' hM, rowsMatrix_mulRows]
  · rw [map_mul, Mx_cJ hM, Mx_eta' hM, rowsMatrix_mulRows]

theorem cJ_points : cJ • (gPt 0 • basePt) = gPt 0 • basePt ∧
    cJ • (gPt 1 • basePt) = gPt 1 • basePt ∧ cJ • (gPt 16 • basePt) = gPt 17 • basePt ∧
    cJ • (gPt 17 • basePt) = gPt 16 • basePt := by
  have hM := j4Facts.mat
  obtain ⟨-, h0, h1, h16, h17⟩ := chkC_facts
  refine ⟨smul_coset_of_smul_row ?_, smul_coset_of_smul_row ?_, smul_coset_of_smul_row ?_,
    smul_coset_of_smul_row ?_⟩
  · rw [gPt_row hM]; exact smul_eq_of_frApply (Mx_cJ hM) h0
  · rw [gPt_row hM]; exact smul_eq_of_frApply (Mx_cJ hM) h1
  · rw [gPt_row hM, gPt_row hM]; exact smul_eq_of_frApply (Mx_cJ hM) h17
  · rw [gPt_row hM, gPt_row hM]; exact smul_eq_of_frApply (Mx_cJ hM) h16

end Facts

end CFSG.Quasithin.J4M3

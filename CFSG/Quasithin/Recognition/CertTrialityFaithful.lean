module

public import CFSG.Quasithin.Recognition.CertTrialityModel

public section

open scoped Matrix

namespace CFSG.Quasithin

theorem exists_eigen_of_fixed_line {F : Type*} [Field F] (g : GL (Fin 8) F) (v : Fin 8 → F)
    (hv : v ≠ 0) (h : g • Projectivization.mk F v hv = Projectivization.mk F v hv) :
    ∃ c : F, (g : Matrix (Fin 8) (Fin 8) F) *ᵥ v = c • v := by
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨(a : F), ha.symm⟩

theorem eq_of_edge {F : Type*} [Field F] {M : Matrix (Fin 8) (Fin 8) F} {x y : Fin 8 → F}
    {c c' d : F} (p q : Fin 8) (hx : M *ᵥ x = c • x) (hy : M *ᵥ y = c' • y)
    (hxy : M *ᵥ (x + y) = d • (x + y)) (hxp : x p = 1) (hyp : y p = 0) (hxq : x q = 0)
    (hyq : y q = 1) : c = c' := by
  rw [Matrix.mulVec_add, hx, hy] at hxy
  have h1 := congrFun hxy p
  have h2 := congrFun hxy q
  simp [hxp, hyp, hxq, hyq] at h1 h2
  rw [h1, h2]

private theorem det_quasithinRootElt_upper {K : Type*} [CommRing K] (pos : List (Fin 8 × Fin 8))
    (hpos : ∀ p ∈ pos, p.1 < p.2) (t : K) : (CFSG.Open.quasithinRootElt pos t).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have : (i, i) ∉ pos := fun h => lt_irrefl _ (hpos _ h)
    simp [CFSG.Open.quasithinRootElt, this]
  · intro i j hij
    simp only [id] at hij
    have h1 : i ≠ j := ne_of_gt hij
    have h2 : (i, j) ∉ pos := fun h => absurd (hpos _ h) (not_lt.mpr hij.le)
    simp [CFSG.Open.quasithinRootElt, h1, h2]

private theorem det_quasithinRootElt_lower {K : Type*} [CommRing K] (pos : List (Fin 8 × Fin 8))
    (hpos : ∀ p ∈ pos, p.2 < p.1) (t : K) : (CFSG.Open.quasithinRootElt pos t).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    have : (i, i) ∉ pos := fun h => lt_irrefl _ (hpos _ h)
    simp [CFSG.Open.quasithinRootElt, this]
  · intro i j hij
    have hij' : i < j := hij
    have h1 : i ≠ j := ne_of_lt hij'
    have h2 : (i, j) ∉ pos := fun h => absurd (hpos _ h) (not_lt.mpr hij'.le)
    simp [CFSG.Open.quasithinRootElt, h1, h2]

private theorem d4Root_true (i : Fin 4) : ∀ p ∈ CFSG.Open.quasithinD4Root i true, p.1 < p.2 := by
  revert i
  decide

private theorem d4Root_false (i : Fin 4) : ∀ p ∈ CFSG.Open.quasithinD4Root i false, p.2 < p.1 := by
  revert i
  decide

private theorem det_quasithinRootElt_d4 {K : Type*} [CommRing K] (i : Fin 4) (s : Bool) (t : K) :
    (CFSG.Open.quasithinRootElt (CFSG.Open.quasithinD4Root i s) t).det = 1 := by
  cases s
  · exact det_quasithinRootElt_lower _ (d4Root_false i) t
  · exact det_quasithinRootElt_upper _ (d4Root_true i) t

theorem det_trialityElt (a : GF8) (s : Bool) : (trialityElt a s).det = 1 := by
  unfold trialityElt
  rw [Matrix.det_mul, Matrix.det_mul, det_quasithinRootElt_d4, det_quasithinRootElt_d4,
    det_quasithinRootElt_d4, one_mul, one_mul]

theorem det_trialityMid (s : Bool) : (trialityMid s).det = 1 :=
  det_quasithinRootElt_d4 1 s 1

theorem det_eq_one_of_mem_trialityGroup8 {g : GL (Fin 8) GF8} (hg : g ∈ trialityGroup8) :
    (g : Matrix (Fin 8) (Fin 8) GF8).det = 1 := by
  have hle : trialityGroup8 ≤ (Matrix.GeneralLinearGroup.det (n := Fin 8) (R := GF8)).ker := by
    refine (Subgroup.closure_le _).mpr fun A hA => ?_
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    rcases hA with ⟨a, s, hs⟩ | ⟨s, hs⟩
    · rw [hs]; exact det_trialityElt a s
    · rw [hs]; exact det_trialityMid s
  have := hle hg
  rw [MonoidHom.mem_ker] at this
  have h2 := congrArg Units.val this
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2

@[expose] def faithDigits : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 1, 2, 4, 3, 0, 0],
    [1, 1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0],
    [1, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 1], [1, 0, 1, 1, 1, 1, 0, 0],
    [0, 1, 1, 2, 4, 3, 0, 0]]

@[expose] def wv (t : Fin 15) : Fin 8 → GF8 := fun j => GF8.ofNat' ((faithDigits.getD t []).getD j 0)

@[expose] def wBasis : Matrix (Fin 8) (Fin 8) GF8 := Matrix.of fun i k => wv ⟨k, by omega⟩ i

@[expose] def wBinv : Matrix (Fin 8) (Fin 8) GF8 :=
  Matrix.of fun i k => GF8.ofNat' ((([[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 4, 5, 0, 0, 0], [0, 0, 0, 2, 3, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 7, 6, 0, 0, 0], [0, 0, 0, 3, 3, 0, 0, 0]] :
      List (List ℕ)).getD i []).getD k 0)

theorem wBasis_mul_wBinv : wBasis * wBinv = 1 := by decide +kernel

theorem exists_scalar_of_fixed_lines (M : Matrix (Fin 8) (Fin 8) GF8)
    (h : ∀ t : Fin 15, ∃ c : GF8, M *ᵥ wv t = c • wv t) : ∃ c : GF8, M = c • 1 := by
  choose c hc using h
  have edge : ∀ (j k e : Fin 15) (p q : Fin 8), wv e = wv j + wv k → wv j p = 1 → wv k p = 0 →
      wv j q = 0 → wv k q = 1 → c j = c k := by
    intro j k e p q hsum h1 h2 h3 h4
    have hjk := hc e
    rw [hsum] at hjk
    exact eq_of_edge p q (hc j) (hc k) hjk h1 h2 h3 h4
  have e1 : c 0 = c 1 := edge 0 1 8 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e2 : c 0 = c 2 := edge 0 2 9 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e3 : c 0 = c 3 := edge 0 3 10 0 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e4 : c 0 = c 4 := edge 0 4 11 0 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e5 : c 1 = c 5 := edge 1 5 12 1 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e6 : c 6 = c 0 := edge 6 0 13 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have e7 : c 7 = c 1 := edge 7 1 14 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hall : ∀ k : Fin 8, c ⟨k, by omega⟩ = c 0 := by
    intro k
    fin_cases k
    · rfl
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm
    · exact e4.symm
    · exact (e1.trans e5).symm
    · exact e6
    · exact e7.trans e1.symm
  have hMB : M * wBasis = c 0 • wBasis := by
    ext i k
    have := congrFun (hc ⟨k, by omega⟩) i
    rw [hall k] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, wBasis] using this
  refine ⟨c 0, ?_⟩
  calc M = M * (wBasis * wBinv) := by rw [wBasis_mul_wBinv, mul_one]
    _ = (M * wBasis) * wBinv := (Matrix.mul_assoc _ _ _).symm
    _ = (c 0 • wBasis) * wBinv := by rw [hMB]
    _ = c 0 • (wBasis * wBinv) := Matrix.smul_mul _ _ _
    _ = c 0 • 1 := by rw [wBasis_mul_wBinv]

theorem eq_one_of_fixes_wv {g : GL (Fin 8) GF8} (hg : g ∈ trialityGroup8)
    (h : ∀ t : Fin 15, ∃ c : GF8, (g : Matrix (Fin 8) (Fin 8) GF8) *ᵥ wv t = c • wv t) : g = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_fixed_lines _ h
  have hdet := det_eq_one_of_mem_trialityGroup8 hg
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc1 : c = 1 := by
    have h8 : ∀ x : GF8, x ^ 8 = x := by decide
    rw [← h8 c]
    exact hdet
  apply Units.ext
  rw [hc, hc1, one_smul]
  rfl

end CFSG.Quasithin


module

public import CFSG.Sporadic.J4.QT2LocCheck
public import CFSG.Sporadic.J4.QTProof

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.Th Matrix

section Mat

variable (hM : MatFacts)
include hM

theorem Mx_b : Mx b = rowsMatrix rowsB := by
  rw [Mx_apply, b_coe, gB_val hM, rowsMatrix_rowsB]

theorem Mx_letterElt {l : ℕ} (hl : l = 1 ∨ l = 2) :
    Mx (letterElt l) = rowsMatrix (baseMats[l - 1]?.getD idRows) := by
  rcases hl with rfl | rfl
  · rw [letterElt_one, Mx_a hM]
    rfl
  · rw [letterElt_two, Mx_b hM]
    rfl

theorem Mx_pathElt : ∀ path : List ℕ, (∀ l ∈ path, l = 1 ∨ l = 2) →
    Mx (pathElt path) = rowsMatrix (pathRows path)
  | [], _ => by simp [pathElt, pathRows, rowsMatrix_idRows]
  | l :: ls, hp => by
    rw [pathElt, map_mul, pathRows, rowsMatrix_mulRows,
      Mx_letterElt hM (hp l (List.mem_cons_self ..)),
      Mx_pathElt ls fun x hx => hp x (List.mem_cons_of_mem _ hx)]

end Mat

theorem pathVecFrom_toVec : ∀ (path : List ℕ) (v : V2),
    (pathVecFrom path v).toVec = v.toVec ᵥ* rowsMatrix (pathRows path)
  | [], v => by simp [pathVecFrom, pathRows, rowsMatrix_idRows]
  | l :: ls, v => by
    rw [pathVecFrom, pathVecFrom_toVec ls, frApply_toVec_eq_vecMul, pathRows,
      rowsMatrix_mulRows, Matrix.vecMul_vecMul]

theorem subReps_get {ℓ : ℕ} (hℓ : ℓ < 7) : subReps[ℓ]! = subReps[ℓ]?.getD 0 := by
  interval_cases ℓ <;> rfl

theorem subReps_lt {ℓ : ℕ} (hℓ : ℓ < 7) : subReps[ℓ]?.getD 0 < nPts := by
  interval_cases ℓ <;> decide

@[expose] def tSet : Set J := {x | ∃ c ∈ tMasks, x = eta uJ 11 c}

theorem mem_tMasks_act {ℓ : ℤ} (hℓ : ℓ ∈ letters) {c : ℕ} (hc : c ∈ tMasks) :
    act ℓ c ∈ tMasks := by
  have h := tClosed_true
  unfold chkTClosed at h
  simp only [List.all_eq_true] at h
  have := h c hc ℓ hℓ
  simpa using this

theorem tSet_conj_letter (hM : MatFacts) {ℓ : ℤ} (hℓ : ℓ ∈ letters) {x : J} (hx : x ∈ tSet) :
    XJ ℓ * x * (XJ ℓ)⁻¹ ∈ tSet := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨act ℓ c, mem_tMasks_act hℓ hc, hX_all hM hℓ c⟩

theorem tSet_conj (hM : MatFacts) :
    ∀ h ∈ Hj, (∀ x ∈ tSet, h * x * h⁻¹ ∈ tSet) ∧ (∀ x ∈ tSet, h⁻¹ * x * h ∈ tSet) := by
  have hmem : ∀ h ∈ Subgroup.closure (XJ '' {ℓ | ℓ ∈ letters}),
      (∀ x ∈ tSet, h * x * h⁻¹ ∈ tSet) ∧ (∀ x ∈ tSet, h⁻¹ * x * h ∈ tSet) := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨ℓ, hℓ, rfl⟩ := hy
      refine ⟨fun x hx => tSet_conj_letter hM hℓ hx, fun x hx => ?_⟩
      obtain ⟨hℓ', hinv⟩ := XJ_inv hℓ
      have := tSet_conj_letter hM hℓ' hx
      rwa [hinv, inv_inv] at this
    | one => simp
    | mul x y _ _ hx hy =>
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · have := hx.1 _ (hy.1 t ht)
        simpa [mul_assoc] using this
      · have := hy.2 _ (hx.2 t ht)
        simpa [mul_assoc] using this
    | inv x _ hx =>
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · simpa using hx.2 t ht
      · simpa using hx.1 t ht
  exact fun h hh => hmem h (Hj_le_closure hh)

theorem not_mem_Eg_conj (hM : MatFacts) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ6 : ℓ ≤ 6) {x : J}
    (hx : x ∈ tSet) :
    pathElt (repPaths.getD ℓ []) * x * (pathElt (repPaths.getD ℓ []))⁻¹ ∉ Eg uJ 11 := by
  have hD := chkD_true
  unfold chkD at hD
  simp only [List.all_eq_true, Bool.and_eq_true] at hD
  obtain ⟨c, hc, rfl⟩ := hx
  have hℓmem : ℓ ∈ List.range' 1 6 := by
    rw [List.mem_range'_1]
    omega
  obtain ⟨hinv, hall⟩ := hD ℓ hℓmem
  set M := pathRows (repPaths.getD ℓ []) with hMdef
  set Mi := invRows M with hMidef
  intro hmem
  obtain ⟨c'', hc'', he⟩ := (mem_Eg_iff (elem_uJ hM)).1 hmem
  have hMx : Mx (pathElt (repPaths.getD ℓ [])) = rowsMatrix M :=
    Mx_pathElt hM _ (repPaths_letters ℓ (by omega))
  have h1 : rowsMatrix M * rowsMatrix Mi = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 hinv)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hMxi : Mx (pathElt (repPaths.getD ℓ []))⁻¹ = rowsMatrix Mi := by
    have h2 : Mx (pathElt (repPaths.getD ℓ []))⁻¹ * Mx (pathElt (repPaths.getD ℓ [])) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    calc Mx (pathElt (repPaths.getD ℓ []))⁻¹
        = Mx (pathElt (repPaths.getD ℓ []))⁻¹ * (rowsMatrix M * rowsMatrix Mi) := by
          rw [h1, mul_one]
      _ = (Mx (pathElt (repPaths.getD ℓ []))⁻¹ * Mx (pathElt (repPaths.getD ℓ []))) *
          rowsMatrix Mi := by rw [hMx, mul_assoc]
      _ = rowsMatrix Mi := by rw [h2, one_mul]
  have hc2 : Mx (eta uJ 11 c) = rowsMatrix (etaRows (uTab (locMats ()) (locInvs ())) 11 c) :=
    Mx_eta hM 11 le_rfl c
  have h3 := congrArg Mx he
  rw [map_mul, map_mul, hMx, hMxi, hc2, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows] at h3
  have h4 := hall c hc (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c'')
    (List.mem_map.2 ⟨c'', List.mem_range.2 (by simpa using hc''), rfl⟩)
  apply differs_toVec h4
  rw [frApply_toVec_eq_vecMul, h3, etaVec_toVec hM 11 le_rfl]

theorem comm_of_mem_centralizer {G : Type*} [Group G] {y q : G}
    (h : q ∈ Subgroup.centralizer ({y} : Set G)) : q * y = y * q :=
  Subgroup.mem_centralizer_singleton_iff.mp h

theorem constrained_of_centralizer_le {G : Type*} [Group G] (H E : Subgroup G) (y : G)
    (hE2 : IsPGroup 2 ↥E) (hab : ∀ x ∈ E, ∀ e ∈ E, x * e = e * x) (hy : y ∈ E)
    (hHE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E) (hself : ∀ h ∈ H, (∀ e ∈ E, h * e = e * h) → h ∈ E)
    (hcent : ∀ q ∈ Subgroup.centralizer ({y} : Set G), q ∈ H) :
    ∃ N : Subgroup G, N ≤ Subgroup.centralizer ({y} : Set G) ∧
      (∀ q ∈ Subgroup.centralizer ({y} : Set G), ∀ e ∈ N, q * e * q⁻¹ ∈ N) ∧ IsPGroup 2 ↥N ∧
      ∀ q ∈ Subgroup.centralizer ({y} : Set G), (∀ e ∈ N, q * e = e * q) → q ∈ N := by
  refine ⟨E, ?_, fun q hq e he => hHE q (hcent q hq) e he, hE2,
    fun q hq hc => hself q (hcent q hq) hc⟩
  intro e he
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hab e he y hy

end CFSG.Sporadic.J4.QT2

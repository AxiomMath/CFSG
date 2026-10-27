module

public import CFSG.ClassicalInvolution.Phan.Defs
import CFSG.ClassicalInvolution.Phan.Frames.Action

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem bsv_isUnitaryInvolution (hK : Nat.card K = 4) :
    IsUnitaryInvolution (unitaryInvolution K 2 1) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  exact isUnitaryInvolution_unitaryInvolution (K := K) (p := 2) (f := 1) hK'

private theorem bsv_linearIndependent_of_orthonormal {m : ℕ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] {v : ι → Fin m → K}
    (hv : ∀ i j, herm (unitaryInvolution K 2 1) (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (hermL (unitaryInvolution K 2 1) (v j)) hc
  simp only [map_sum, map_smul, hermL_apply, smul_eq_mul, map_zero] at h
  simpa only [hv j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] using h

private theorem bsv_disjoint_span_orthonormal {m k d r : ℕ} {s : Fin k → Fin m → K}
    (hdk : d ≤ k) (hs : ∀ i j : Fin k, (i : ℕ) < d → (j : ℕ) < d →
      herm (unitaryInvolution K 2 1) (s i) (s j) = if i = j then 1 else 0)
    {Z : Submodule K (Fin m → K)} (hZf : ∀ z ∈ Z, ∀ i, herm (unitaryInvolution K 2 1)
      (s i) z = 0) {b : Fin r → Fin m → K}
    (hb_span : Submodule.span K (Set.range b) = Z) :
    Disjoint (Submodule.span K (Set.range b))
      (Submodule.span K (Set.range fun j : Fin d => s (Fin.castLE hdk j))) := by
  let s' : Fin d → Fin m → K := fun j => s (Fin.castLE hdk j)
  change Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range s'))
  rw [Submodule.disjoint_def]
  intro x hxb hxs
  rw [hb_span] at hxb
  rw [Submodule.mem_span_range_iff_exists_fun] at hxs
  obtain ⟨c, hc⟩ := hxs
  have hx0 : ∀ l : Fin d, c l = 0 := by
    intro l
    have h0 := hZf x hxb (Fin.castLE hdk l)
    rw [← hc] at h0
    have hlin : herm (unitaryInvolution K 2 1) (s (Fin.castLE hdk l))
        (∑ j : Fin d, c j • s' j) = ∑ j : Fin d, c j *
        herm (unitaryInvolution K 2 1) (s (Fin.castLE hdk l)) (s' j) := by
      change hermL (unitaryInvolution K 2 1) (s (Fin.castLE hdk l))
          (∑ j : Fin d, c j • s' j) = ∑ j : Fin d, c j *
        hermL (unitaryInvolution K 2 1) (s (Fin.castLE hdk l)) (s' j)
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    rw [hlin] at h0
    have hsum : (∑ j : Fin d, c j * (if l = j then 1 else 0)) =
        ∑ j : Fin d, c j * herm (unitaryInvolution K 2 1) (s (Fin.castLE hdk l)) (s' j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hs (Fin.castLE hdk l) (Fin.castLE hdk j) (by simp) (by simp)]
      simp [Fin.castLE_inj]
    have hpm : (∑ j : Fin d, c j * (if l = j then 1 else 0)) = 0 := by
      rw [hsum, h0]
    simpa using hpm
  rw [← hc]
  simp only [hx0, zero_smul, Finset.sum_const_zero]

private theorem bsv_linearIndependent_append {m k d r : ℕ} {s : Fin k → Fin m → K}
    (hdk : d ≤ k) (hs : ∀ i j : Fin k, (i : ℕ) < d → (j : ℕ) < d →
      herm (unitaryInvolution K 2 1) (s i) (s j) = if i = j then 1 else 0)
    {Z : Submodule K (Fin m → K)} (hZf : ∀ z ∈ Z, ∀ i, herm (unitaryInvolution K 2 1)
      (s i) z = 0) {b : Fin r → Fin m → K} (hb_li : LinearIndependent K b)
    (hb_span : Submodule.span K (Set.range b) = Z) :
    LinearIndependent K (Sum.elim b (fun j : Fin d => s (Fin.castLE hdk j))) := by
  have hs' : LinearIndependent K (fun j : Fin d => s (Fin.castLE hdk j)) := by
    refine bsv_linearIndependent_of_orthonormal fun i j => ?_
    have h0 := hs (Fin.castLE hdk i) (Fin.castLE hdk j) (by simp) (by simp)
    simpa [Fin.castLE_inj] using h0
  exact LinearIndependent.sum_type hb_li hs'
    (bsv_disjoint_span_orthonormal hdk hs hZf hb_span)

private theorem bsv_two_mul_finrank_add_le {m k d : ℕ}
    (hσ : IsUnitaryInvolution (unitaryInvolution K 2 1))
    (F : ReflForm K (Fin m → K)) (hF : ∀ x y, F.β x y =
      herm (unitaryInvolution K 2 1) x y) {s : Fin k → Fin m → K} (hdk : d ≤ k)
    (hs : ∀ i j : Fin k, (i : ℕ) < d → (j : ℕ) < d →
      herm (unitaryInvolution K 2 1) (s i) (s j) = if i = j then 1 else 0)
    (Z : Submodule K (Fin m → K))
    (hZf : ∀ z ∈ Z, ∀ i, herm (unitaryInvolution K 2 1) (s i) z = 0)
    (hZtot : ∀ z ∈ Z, herm (unitaryInvolution K 2 1) z z = 0) :
    2 * Module.finrank K Z + d ≤ m := by
  classical
  set r : ℕ := Module.finrank K Z with hrdef
  let b : Fin r → Fin m → K := fun i => ((Module.finBasis K Z) i : Fin m → K)
  have hcomp : (⇑Z.subtype ∘ ⇑(Module.finBasis K Z)) =
      (fun i => ((Module.finBasis K Z) i : Fin m → K)) := rfl
  have hb_li : LinearIndependent K b := by
    have h := (Module.finBasis K Z).linearIndependent
    have h' := h.map' (Submodule.subtype Z) (Submodule.ker_subtype Z)
    rw [hcomp] at h'
    simpa only [b] using h'
  have hb_span : Submodule.span K (Set.range b) = Z := by
    have h1 : Submodule.map (Submodule.subtype Z)
        (Submodule.span K (Set.range (Module.finBasis K Z))) = Z := by
      rw [Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp, hcomp] at h1
    simpa only [b] using h1
  have hcomb : LinearIndependent K
      (Sum.elim b (fun j : Fin d => s (Fin.castLE hdk j))) :=
    bsv_linearIndependent_append hdk hs hZf hb_li hb_span
  let C : Submodule K (Fin m → K) :=
    Submodule.span K (Set.range (Sum.elim b (fun j : Fin d => s (Fin.castLE hdk j))))
  have hCdim : Module.finrank K C = r + d := by
    dsimp only [C]
    rw [finrank_span_eq_card hcomb, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have hCle : C ≤ F.perp Z := by
    dsimp only [C]
    rw [Submodule.span_le]
    rintro y ⟨x, hx⟩
    rcases x with i | j
    · rw [← hx]
      refine F.mem_perp.mpr fun z hz => ?_
      rw [hF]
      exact herm_eq_zero_of_forall_isotropic hσ hZtot hz (Module.finBasis K Z i).2
    · rw [← hx]
      refine F.mem_perp.mpr fun z hz => ?_
      rw [hF]
      exact herm_eq_zero_comm _ hσ.invol (hZf z hz (Fin.castLE hdk j))
  have hCZ : Module.finrank K C ≤ Module.finrank K (F.perp Z) := Submodule.finrank_mono hCle
  have hperpb := F.finrank_perp Z
  rw [Module.finrank_fin_fun] at hperpb
  omega

private theorem bsv_exists_aniso_perp (hK : Nat.card K = 4) {m k d : ℕ} (hdk : d ≤ k)
    (hkm : 2 * k < m + d) (s : Fin k → Fin m → K)
    (hs : ∀ i j : Fin k, (i : ℕ) < d → (j : ℕ) < d →
      herm (unitaryInvolution K 2 1) (s i) (s j) = if i = j then 1 else 0) :
    ∃ z : Fin m → K, (∀ i, herm (unitaryInvolution K 2 1) (s i) z = 0) ∧
      herm (unitaryInvolution K 2 1) z z ≠ 0 := by
  classical
  have hσ := bsv_isUnitaryInvolution (K := K) hK
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let F : ReflForm K (Fin m → K) := unitaryForm (K := K) (p := 2) (f := 1) hK' m
  have hFβ : ∀ x y, F.β x y = herm (unitaryInvolution K 2 1) x y := by
    intro x y
    dsimp only [F]
    exact unitaryForm_β hK' x y
  by_contra h
  push Not at h
  set W : Submodule K (Fin m → K) := Submodule.span K (Set.range s) with hWdef
  set Z : Submodule K (Fin m → K) := F.perp W with hZdef
  have hWk : Module.finrank K W ≤ k := by
    have h1 := finrank_span_le_card (R := K) (Set.range s)
    rw [Set.toFinset_card] at h1
    have h2 : Fintype.card (Set.range s) ≤ k := by
      simpa using Fintype.card_range_le (f := s)
    dsimp only [W]
    exact le_trans h1 h2
  have hdim : Module.finrank K Z + Module.finrank K W = m := by
    have h := F.finrank_perp W
    rw [Module.finrank_fin_fun] at h
    rwa [← hZdef] at h
  have hr : m - k ≤ Module.finrank K Z := by omega
  have hZf : ∀ z ∈ Z, ∀ i, herm (unitaryInvolution K 2 1) (s i) z = 0 := by
    intro z hz i
    have hz' : z ∈ F.perp W := hz
    have h0 := (F.mem_perp.mp hz') (s i) (Submodule.subset_span (Set.mem_range_self i))
    rwa [hFβ] at h0
  have hZtot : ∀ z ∈ Z, herm (unitaryInvolution K 2 1) z z = 0 := by
    intro z hz
    exact h z (hZf z hz)
  have hbound := bsv_two_mul_finrank_add_le hσ F hFβ hdk hs Z hZf hZtot
  omega

theorem exists_herm_self_eq_one_of_orthonormal (hK : Nat.card K = 4) {m k d : ℕ} (hdk : d ≤ k)
    (hkm : 2 * k < m + d) (s : Fin k → Fin m → K)
    (hs : ∀ i j : Fin k, (i : ℕ) < d → (j : ℕ) < d →
      herm (unitaryInvolution K 2 1) (s i) (s j) = if i = j then 1 else 0) :
    ∃ z : Fin m → K, herm (unitaryInvolution K 2 1) z z = 1 ∧
      ∀ i, herm (unitaryInvolution K 2 1) (s i) z = 0 := by
  obtain ⟨z, hz, hz1⟩ := bsv_exists_aniso_perp (K := K) hK hdk hkm s hs
  have hσ := bsv_isUnitaryInvolution (K := K) hK
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hz1
  exact ⟨c • z, hc, fun i => by rw [herm_smul_right, hz i, mul_zero]⟩

private theorem bsv_orthonormal_snoc (hσ : IsUnitaryInvolution (unitaryInvolution K 2 1)) {m n : ℕ}
    {u : Fin n → Fin m → K} {w : Fin m → K}
    (hu : ∀ i j, herm (unitaryInvolution K 2 1) (u i) (u j) = if i = j then 1 else 0)
    (hw : ∀ i, herm (unitaryInvolution K 2 1) (u i) w = 0)
    (hww : herm (unitaryInvolution K 2 1) w w = 1) :
    ∀ i j, herm (unitaryInvolution K 2 1)
      ((Fin.snoc u w : Fin (n + 1) → Fin m → K) i)
      ((Fin.snoc u w : Fin (n + 1) → Fin m → K) j) = if i = j then 1 else 0 := by
  have hne : ∀ j : Fin n, (Fin.last n : Fin (n + 1)) ≠ Fin.castSucc j := by
    intro j h
    have := congrArg Fin.val h
    simp at this
    omega
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [Fin.snoc_last] using hww
    · have h0 : herm (unitaryInvolution K 2 1) w (u j) = 0 := by
        rw [herm_conj _ hσ.invol, hw j, map_zero]
      simpa [Fin.snoc_last, Fin.snoc_castSucc, if_neg (hne j)] using h0
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · have hne' : (Fin.castSucc i : Fin (n + 1)) ≠ Fin.last n := fun h => hne i h.symm
      have h0 : herm (unitaryInvolution K 2 1) (u i) w = 0 := hw i
      simpa [Fin.snoc_last, Fin.snoc_castSucc, if_neg hne'] using h0
    · have h0 : herm (unitaryInvolution K 2 1) (u i) (u j) = if i = j then 1 else 0 := hu i j
      simpa [Fin.snoc_castSucc, Fin.castSucc_inj] using h0

private theorem bsv_exists_orthonormal_snoc (hK : Nat.card K = 4) {m n : ℕ} (hn : n < m)
    {u : Fin n → Fin m → K}
    (hu : ∀ i j, herm (unitaryInvolution K 2 1) (u i) (u j) = if i = j then 1 else 0) :
    ∃ w : Fin m → K, (∀ i, herm (unitaryInvolution K 2 1) (u i) w = 0) ∧
      herm (unitaryInvolution K 2 1) w w = 1 := by
  obtain ⟨w, hw1, hw2⟩ := exists_herm_self_eq_one_of_orthonormal (K := K) hK
    (d := n) (k := n) le_rfl (by omega) u (fun i j _ _ => hu i j)
  exact ⟨w, hw2, hw1⟩

private theorem bsv_exists_orthonormal_extend (hK : Nat.card K = 4) {m k : ℕ} (hk : k ≤ m)
    {u : Fin k → Fin m → K}
    (hu : ∀ i j, herm (unitaryInvolution K 2 1) (u i) (u j) = if i = j then 1 else 0) :
    ∃ U : Fin m → Fin m → K,
      (∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0) ∧
        ∀ i : Fin k, U (Fin.castLE hk i) = u i := by
  have hσ := bsv_isUnitaryInvolution (K := K) hK
  let P : ∀ n, k ≤ n → Prop := fun n hn => n ≤ m → ∃ U : Fin n → Fin m → K,
    (∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0) ∧
      ∀ i : Fin k, U (Fin.castLE hn i) = u i
  have base : P k (le_refl k) := fun _ => ⟨u, hu, fun i => by simp⟩
  have step : ∀ n (hkn : k ≤ n), P n hkn → P (n + 1) (Nat.le_succ_of_le hkn) := by
    intro n hkn ih hnm
    obtain ⟨U, hU, hUu⟩ := ih (by omega)
    obtain ⟨w, hw, hww⟩ := bsv_exists_orthonormal_snoc (K := K) hK (m := m) (by omega) hU
    refine ⟨Fin.snoc U w, bsv_orthonormal_snoc hσ hU hw hww, fun i => ?_⟩
    have hcast : (Fin.castLE (Nat.le_succ_of_le hkn) i : Fin (n + 1)) =
        Fin.castSucc (Fin.castLE hkn i) := Fin.ext rfl
    rw [hcast, Fin.snoc_castSucc]
    exact hUu i
  exact Nat.le_induction (m := k) (P := P) base step m hk (le_refl m)

private noncomputable def bsvc {m : ℕ} (U V : Fin m → Fin m → K) : K :=
  (colMat U).det * ((colMat V).det)⁻¹

private noncomputable def bsvd {m : ℕ} (U V : Fin m → Fin m → K) (last : Fin m) : Fin m → K :=
  fun j => if j = last then bsvc U V else 1

private noncomputable def bsvD {m : ℕ} (U V : Fin m → Fin m → K) (last : Fin m) :
    Matrix (Fin m) (Fin m) K :=
  Matrix.diagonal (bsvd U V last)

private noncomputable def bsvM {m : ℕ} (U V : Fin m → Fin m → K) (last : Fin m) :
    Matrix (Fin m) (Fin m) K :=
  colMat V * bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U)

private theorem bsvc_norm {m : ℕ} {U V : Fin m → Fin m → K}
    (hU : ∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0)
    (hV : ∀ i j, herm (unitaryInvolution K 2 1) (V i) (V j) = if i = j then 1 else 0) :
    unitaryInvolution K 2 1 (bsvc U V) * bsvc U V = 1 := by
  have hdetU := norm_det_colMat hU
  have hdetV := norm_det_colMat hV
  have hV0 : (colMat V).det ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hdetV
    exact zero_ne_one hdetV
  have hVinv : unitaryInvolution K 2 1 ((colMat V).det)⁻¹ * ((colMat V).det)⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hdetV, inv_one]
  calc unitaryInvolution K 2 1 (bsvc U V) * bsvc U V
      = (unitaryInvolution K 2 1 (colMat U).det *
          unitaryInvolution K 2 1 ((colMat V).det)⁻¹) *
        ((colMat U).det * ((colMat V).det)⁻¹) := by
        dsimp only [bsvc]
        rw [map_mul, map_inv₀]
    _ = (unitaryInvolution K 2 1 (colMat U).det * (colMat U).det) *
        (unitaryInvolution K 2 1 ((colMat V).det)⁻¹ * ((colMat V).det)⁻¹) := by ring
    _ = 1 * 1 := by rw [hdetU, hVinv]
    _ = 1 := one_mul 1

private theorem bsvd_norm {m : ℕ} {U V : Fin m → Fin m → K}
    (hU : ∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0)
    (hV : ∀ i j, herm (unitaryInvolution K 2 1) (V i) (V j) = if i = j then 1 else 0)
    (last : Fin m) :
    ∀ j, unitaryInvolution K 2 1 (bsvd U V last j) * bsvd U V last j = 1 := by
  intro j
  dsimp only [bsvd]
  by_cases hj : j = last
  · rw [if_pos hj]
    exact bsvc_norm hU hV
  · rw [if_neg hj, map_one, one_mul]

omit [Finite K] [CharP K 2] in
private theorem bsvd_prod {m : ℕ} (U V : Fin m → Fin m → K) (last : Fin m) :
    (∏ j : Fin m, bsvd U V last j) = bsvc U V := by
  dsimp only [bsvd]
  exact Fintype.prod_ite_eq' last (fun _ => bsvc U V)

private theorem bsvM_det {m : ℕ} {U V : Fin m → Fin m → K}
    (hU : ∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0)
    (hV : ∀ i j, herm (unitaryInvolution K 2 1) (V i) (V j) = if i = j then 1 else 0)
    (last : Fin m) : (bsvM U V last).det = 1 := by
  have hdetU := norm_det_colMat hU
  have hdetV := norm_det_colMat hV
  have hV0 : (colMat V).det ≠ 0 := by
    intro h
    rw [h, map_zero, zero_mul] at hdetV
    exact zero_ne_one hdetV
  have hdetcU : (conjTr (unitaryInvolution K 2 1) (colMat U)).det =
      unitaryInvolution K 2 1 (colMat U).det := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det (unitaryInvolution K 2 1 : K →+* K) (colMat U)).symm
  dsimp only [bsvM, bsvD]
  rw [Matrix.det_mul, Matrix.det_mul, hdetcU, Matrix.det_diagonal, bsvd_prod]
  dsimp only [bsvc]
  have hc_eq : (colMat V).det * ((colMat U).det * ((colMat V).det)⁻¹) *
      unitaryInvolution K 2 1 (colMat U).det =
      ((colMat V).det * ((colMat V).det)⁻¹) *
        ((colMat U).det * unitaryInvolution K 2 1 (colMat U).det) := by ring
  rw [hc_eq, mul_inv_cancel₀ hV0, ← mul_comm (unitaryInvolution K 2 1 (colMat U).det)
    (colMat U).det, hdetU, one_mul]

private theorem bsvM_unitary (hK : Nat.card K = 4) {m : ℕ} {U V : Fin m → Fin m → K}
    (hU : ∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0)
    (hV : ∀ i j, herm (unitaryInvolution K 2 1) (V i) (V j) = if i = j then 1 else 0)
    (last : Fin m) :
    conjTr (unitaryInvolution K 2 1) (bsvM U V last) * bsvM U V last = 1 := by
  have hV1 : conjTr (unitaryInvolution K 2 1) (colMat V) * colMat V = 1 :=
    conjTr_colMat_mul_colMat hV
  have hU2 : colMat U * conjTr (unitaryInvolution K 2 1) (colMat U) = 1 :=
    colMat_mul_conjTr_colMat hU
  have hhU : conjTr (unitaryInvolution K 2 1)
      (conjTr (unitaryInvolution K 2 1) (colMat U)) = colMat U := by
    ext i j
    exact (bsv_isUnitaryInvolution (K := K) hK).invol (colMat U i j)
  have hD : conjTr (unitaryInvolution K 2 1) (bsvD U V last) * bsvD U V last = 1 := by
    dsimp only [bsvD]
    rw [conjTr_diagonal, Matrix.diagonal_mul_diagonal]
    rw [show (fun j => unitaryInvolution K 2 1 (bsvd U V last j) * bsvd U V last j) =
      (fun _ => 1) from funext (bsvd_norm hU hV last)]
    exact Matrix.diagonal_one
  dsimp only [bsvM]
  have hconj : conjTr (unitaryInvolution K 2 1)
      (colMat V * bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U)) =
      colMat U * (conjTr (unitaryInvolution K 2 1) (bsvD U V last) *
        conjTr (unitaryInvolution K 2 1) (colMat V)) := by
    rw [conjTr_mul, conjTr_mul, hhU]
  rw [hconj]
  calc colMat U * (conjTr (unitaryInvolution K 2 1) (bsvD U V last) *
        conjTr (unitaryInvolution K 2 1) (colMat V)) *
        (colMat V * bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U))
      = colMat U * (conjTr (unitaryInvolution K 2 1) (bsvD U V last) *
          (conjTr (unitaryInvolution K 2 1) (colMat V) * (colMat V *
            (bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U))))) := by
        simp only [Matrix.mul_assoc]
    _ = colMat U * (conjTr (unitaryInvolution K 2 1) (bsvD U V last) *
          (1 * (bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U)))) := by
        rw [← Matrix.mul_assoc (conjTr (unitaryInvolution K 2 1) (colMat V)) (colMat V)
          (bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U)), hV1]
    _ = colMat U * (conjTr (unitaryInvolution K 2 1) (bsvD U V last) *
          (bsvD U V last * conjTr (unitaryInvolution K 2 1) (colMat U))) := by
        rw [Matrix.one_mul]
    _ = colMat U * ((conjTr (unitaryInvolution K 2 1) (bsvD U V last) * bsvD U V last) *
          conjTr (unitaryInvolution K 2 1) (colMat U)) := by rw [Matrix.mul_assoc]
    _ = colMat U * (1 * conjTr (unitaryInvolution K 2 1) (colMat U)) := by rw [hD]
    _ = colMat U * conjTr (unitaryInvolution K 2 1) (colMat U) := by rw [Matrix.one_mul]
    _ = 1 := hU2

private theorem bsvM_action {m : ℕ} {U V : Fin m → Fin m → K}
    (hU : ∀ i j, herm (unitaryInvolution K 2 1) (U i) (U j) = if i = j then 1 else 0)
    {last : Fin m} {j : Fin m} (hj : j ≠ last) : bsvM U V last *ᵥ U j = V j := by
  have hU1 : conjTr (unitaryInvolution K 2 1) (colMat U) * colMat U = 1 :=
    conjTr_colMat_mul_colMat hU
  have hd : bsvd U V last j = 1 := by
    dsimp only [bsvd]
    rw [if_neg hj]
  have hcolU : colMat U *ᵥ (Pi.single j 1 : Fin m → K) = U j := by
    ext a
    simp [colMat, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcolV : colMat V *ᵥ (Pi.single j 1 : Fin m → K) = V j := by
    ext a
    simp [colMat, Matrix.mulVec, dotProduct, Pi.single_apply]
  calc bsvM U V last *ᵥ U j
      = bsvM U V last *ᵥ (colMat U *ᵥ Pi.single j 1) := by rw [hcolU]
    _ = (bsvM U V last * colMat U) *ᵥ Pi.single j 1 := by rw [Matrix.mulVec_mulVec]
    _ = (colMat V * bsvD U V last) *ᵥ Pi.single j 1 := by
        dsimp only [bsvM]
        rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
    _ = colMat V *ᵥ (bsvD U V last *ᵥ Pi.single j 1) := by rw [Matrix.mulVec_mulVec]
    _ = colMat V *ᵥ Pi.single j (bsvd U V last j * 1) := by
        dsimp only [bsvD]
        rw [Matrix.diagonal_mulVec_single]
    _ = colMat V *ᵥ Pi.single j 1 := by rw [mul_one, hd]
    _ = V j := hcolV

theorem exists_smul_eq_of_orthonormal (hK : Nat.card K = 4) {m k : ℕ} (hkm : k < m)
    {u v : Fin k → Fin m → K}
    (hu : ∀ i j, herm (unitaryInvolution K 2 1) (u i) (u j) = if i = j then 1 else 0)
    (hv : ∀ i j, herm (unitaryInvolution K 2 1) (v i) (v j) = if i = j then 1 else 0) :
    ∃ g : Su K 2 1 m, ∀ i, g • u i = v i := by
  classical
  obtain ⟨U, hU, hUu⟩ := bsv_exists_orthonormal_extend (K := K) hK (k := k) hkm.le (u := u) hu
  obtain ⟨V, hV, hVv⟩ := bsv_exists_orthonormal_extend (K := K) hK (k := k) hkm.le (u := v) hv
  have hm0 : 0 < m := by omega
  let last : Fin m := ⟨m - 1, by omega⟩
  have hlast : ∀ i : Fin k, (Fin.castLE hkm.le i : Fin m) ≠ last := by
    intro i h
    have := congrArg Fin.val h
    simp [last] at this
    omega
  have hdetM := bsvM_det hU hV last
  have hunitM := bsvM_unitary hK hU hV last
  have hiso : ∀ x y, herm (unitaryInvolution K 2 1) (bsvM U V last *ᵥ x)
      (bsvM U V last *ᵥ y) = herm (unitaryInvolution K 2 1) x y := by
    intro x y
    rw [herm_mulVec, hunitM, Matrix.one_mulVec]
  refine ⟨mkSU (unitaryInvolution K 2 1) (bsvM U V last) hdetM hiso, fun i => ?_⟩
  rw [mkSU_smul]
  calc bsvM U V last *ᵥ u i
      = bsvM U V last *ᵥ U (Fin.castLE hkm.le i) := by rw [hUu i]
    _ = V (Fin.castLE hkm.le i) := bsvM_action hU (hlast i)
    _ = v i := hVv i

end CFSG.StandardType.QTwo

end

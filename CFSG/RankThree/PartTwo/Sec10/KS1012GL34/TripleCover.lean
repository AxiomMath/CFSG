module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.ChecksT7
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Stab
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public meta import CFSG.Fischer.F4
import CFSG.Fischer.F4
public meta import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34

open CFSG.Fischer
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge

theorem t7V_mul_inv : ∀ i : Fin 6, t7V i * t7Vinv i = 1 := by
  decide +kernel

theorem Omega_iff_pt : ∀ (i : Fin 6) (v : Fin 3 → F4),
    v ∈ Omega i ↔ ∃ j : Fin 6, t7Pt i j = v := by
  decide +kernel

theorem mem_Omega_iff (i : Fin 6) (v : Fin 3 → F4) :
    v ∈ Omega i ↔ ∃ j : Fin 6, t7Pt i j = v :=
  Omega_iff_pt i v

theorem t7Pt_unique : ∀ (i a b : Fin 6) (c d : F4), c ≠ 0 → d ≠ 0 →
    c • t7Pt i a = d • t7Pt i b → a = b := by
  decide +kernel

theorem t7Scal_iff : ∀ c : F4, c ≠ 0 ↔ c ∈ t7Scal := by
  decide +kernel

theorem t7Vinv_mul_V_all : ∀ j : Fin 6, t7Vinv j * t7V j = 1 := by
  decide +kernel

theorem t7Vinv_mul_V (i : Fin 6) : t7Vinv i * t7V i = 1 :=
  t7Vinv_mul_V_all i

theorem t7Pt_has_one : ∀ (i a : Fin 6), ∃ r : Fin 3, t7Pt i a r = 1 := by
  decide +kernel

theorem t7Mm_eq (A B : Matrix (Fin 3) (Fin 3) F4) : t7Mm A B = A * B := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [t7Mm, Matrix.mul_apply, Fin.sum_univ_three]

theorem t7Mv_eq (M : Matrix (Fin 3) (Fin 3) F4) (v : Fin 3 → F4) :
    t7Mv M v = Matrix.mulVec M v := by
  funext r
  fin_cases r <;> simp [t7Mv, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem t7M_eq (i : Fin 6) (q : (Fin 3 → Fin 6) × (Fin 3 → F4)) :
    t7M i q = cols (fun k => q.2 k • t7Pt i (q.1 k)) * t7Vinv i :=
  t7Mm_eq _ _

theorem t7Adj_eq (A : Matrix (Fin 3) (Fin 3) F4) : t7Adj A = Matrix.adjugate A := by
  rw [Matrix.adjugate_fin_three]
  rfl

theorem t7Stab_iff (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) :
    t7Stab i M ↔ stabilizes i M := by
  constructor
  · intro h v hv
    obtain ⟨k, rfl⟩ := (mem_Omega_iff i v).mp hv
    obtain ⟨j, c, hc, h'⟩ := h k
    refine ⟨t7Pt i j, (mem_Omega_iff i _).mpr ⟨j, rfl⟩, c, (t7Scal_iff c).mpr hc, ?_⟩
    rw [← t7Mv_eq]
    funext r
    simpa using congrFun h' r
  · intro h k
    obtain ⟨u, hu, c, hc, h'⟩ := h (t7Pt i k) ((mem_Omega_iff i _).mpr ⟨k, rfl⟩)
    obtain ⟨j, rfl⟩ := (mem_Omega_iff i u).mp hu
    refine ⟨j, c, (t7Scal_iff c).mp hc, ?_⟩
    rw [t7Mv_eq]
    exact h'

theorem t7Idx_spec {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (hM : stabilizes i M) (k : Fin 6) :
    ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec M (t7Pt i k) = c • t7Pt i (t7Idx i M k) := by
  have hk : ∃ j : Fin 6, ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec M (t7Pt i k) = c • t7Pt i j := by
    obtain ⟨u, hu, c, hc, h⟩ := hM (t7Pt i k) ((mem_Omega_iff i _).mpr ⟨k, rfl⟩)
    obtain ⟨j, rfl⟩ := (mem_Omega_iff i u).mp hu
    exact ⟨j, c, hc, h⟩
  obtain ⟨j, c, hc, hj⟩ := hk
  have hex : ∃ x ∈ List.finRange 6, decide (∃ c : F4, c ≠ 0 ∧
      Matrix.mulVec M (t7Pt i k) = c • t7Pt i x) = true :=
    ⟨j, List.mem_finRange j, by simpa using ⟨c, hc, hj⟩⟩
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
  have hpa := List.find?_some ha
  have hidx : t7Idx i M k = a := by
    unfold t7Idx
    rw [ha]
    rfl
  rw [hidx]
  simpa using hpa

theorem t7Idx_one (i : Fin 6) (k : Fin 6) : t7Idx i 1 k = k := by
  obtain ⟨c, hc, h⟩ := t7Idx_spec (stabilizes_one i) k
  rw [Matrix.one_mulVec] at h
  have h' : (1 : F4) • t7Pt i k = c • t7Pt i (t7Idx i 1 k) := by
    rw [one_smul]
    exact h
  exact (t7Pt_unique i k (t7Idx i 1 k) 1 c one_ne_zero hc h').symm

theorem t7Idx_mul {i : Fin 6} {M N : Matrix (Fin 3) (Fin 3) F4} (hM : stabilizes i M)
    (hN : stabilizes i N) (k : Fin 6) :
    t7Idx i (M * N) k = t7Idx i M (t7Idx i N k) := by
  obtain ⟨c, hc, hN'⟩ := t7Idx_spec hN k
  obtain ⟨d, hd, hM'⟩ := t7Idx_spec hM (t7Idx i N k)
  obtain ⟨e, he, hMN⟩ := t7Idx_spec (stabilizes_mul hM hN) k
  have h : (c * d) • t7Pt i (t7Idx i M (t7Idx i N k)) = e • t7Pt i (t7Idx i (M * N) k) := by
    rw [← smul_smul, ← hM', ← Matrix.mulVec_smul, ← hN', Matrix.mulVec_mulVec]
    exact hMN
  exact (t7Pt_unique i _ _ _ _ (mul_ne_zero hc hd) he h).symm

theorem stabilizes_adj {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (hdet : M.det = 1)
    (hM : stabilizes i M) : stabilizes i (Matrix.adjugate M) := by
  let u : Matrix.GeneralLinearGroup (Fin 3) F4 :=
    Units.mk M (Matrix.adjugate M) (by rw [Matrix.mul_adjugate, hdet, one_smul])
      (by rw [Matrix.adjugate_mul, hdet, one_smul])
  have h : Matrix.adjugate M = M ^ (orderOf u - 1) := coe_inv_eq_pow u
  rw [h]
  exact stabilizes_pow hM _

theorem perm_cond {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (hdet : M.det = 1)
    (hM : stabilizes i M) :
    (∀ k, t7Idx i (t7Adj M) (t7Idx i M k) = k) ∧
      (∀ k, t7Idx i M (t7Idx i (t7Adj M) k) = k) := by
  have hA : stabilizes i (t7Adj M) := by
    rw [t7Adj_eq]
    exact stabilizes_adj hdet hM
  have h1 : Matrix.adjugate M * M = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
  have h2 : M * Matrix.adjugate M = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  constructor
  · intro k
    rw [← t7Idx_mul hA hM k, t7Adj_eq, h1, t7Idx_one]
  · intro k
    rw [← t7Idx_mul hM hA k, t7Adj_eq, h2, t7Idx_one]

theorem t7Perm_apply {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (hdet : M.det = 1)
    (hM : stabilizes i M) (k : Fin 6) : t7Perm i M k = t7Idx i M k := by
  unfold t7Perm t7PermOf
  rw [dif_pos (perm_cond hdet hM)]
  rfl

theorem t7Det_eq (M : Matrix (Fin 3) (Fin 3) F4) : t7Det M = M.det := by
  rw [Matrix.det_fin_three]
  unfold t7Det
  ring

theorem mul_t7V_eq (M : Matrix (Fin 3) (Fin 3) F4) (i : Fin 6) (f : Fin 3 → Fin 3 → F4)
    (hf : ∀ k, Matrix.mulVec M (t7Base i k) = f k) :
    M * t7V i = cols f := by
  ext r k
  show (M * t7V i) r k = f k r
  rw [← congrFun (hf k) r]
  simp [t7V, cols, Matrix.mul_apply, Matrix.mulVec, dotProduct, t7Base]

theorem mem_t7Tup {i : Fin 6} {q : (Fin 3 → Fin 6) × (Fin 3 → F4)} :
    q ∈ t7Tup i ↔ t7Det (t7M i q) = 1 ∧ stabilizes i (t7M i q) := by
  unfold t7Tup
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, t7Stab_iff]

theorem t7M_surj {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (hdet : M.det = 1)
    (hM : stabilizes i M) : ∃ q ∈ t7Tup i, t7M i q = M := by
  have hk : ∀ k : Fin 3, ∃ j : Fin 6, ∃ c : F4, c ≠ 0 ∧
      Matrix.mulVec M (t7Base i k) = c • t7Pt i j := by
    intro k
    obtain ⟨u, hu, c, hc, h⟩ :=
      hM (t7Base i k) ((mem_Omega_iff i _).mpr ⟨Fin.castLE (by decide) k, rfl⟩)
    obtain ⟨j, rfl⟩ := (mem_Omega_iff i u).mp hu
    exact ⟨j, c, hc, h⟩
  choose J C hC using hk
  have hMV : M * t7V i = cols (fun k => C k • t7Pt i (J k)) :=
    mul_t7V_eq M i _ (fun k => (hC k).2)
  have hq : t7M i (J, C) = M := by
    rw [t7M_eq]
    show cols (fun k => C k • t7Pt i (J k)) * t7Vinv i = M
    rw [← hMV, Matrix.mul_assoc, t7V_mul_inv i, Matrix.mul_one]
  have hdet' : t7Det (t7M i (J, C)) = 1 := by
    rw [hq, t7Det_eq, hdet]
  have hstab' : stabilizes i (t7M i (J, C)) := by
    rw [hq]
    exact hM
  have hmem : (J, C) ∈ t7Tup i := mem_t7Tup.mpr ⟨hdet', hstab'⟩
  exact ⟨(J, C), hmem, hq⟩

theorem t7_det_V_ne_zero (i : Fin 6) : (t7V i).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (t7V_mul_inv i)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem t7M_mul_V (i : Fin 6) (q : (Fin 3 → Fin 6) × (Fin 3 → F4)) :
    t7M i q * t7V i = cols (fun k => q.2 k • t7Pt i (q.1 k)) := by
  rw [t7M_eq, Matrix.mul_assoc, t7Vinv_mul_V, Matrix.mul_one]

theorem t7M_base (i : Fin 6) (q : (Fin 3 → Fin 6) × (Fin 3 → F4)) (k : Fin 3) :
    Matrix.mulVec (t7M i q) (t7Base i k) = q.2 k • t7Pt i (q.1 k) := by
  funext r
  have h := congrFun (congrFun (t7M_mul_V i q) r) k
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, t7V, cols] using h

theorem t7_coef_ne_zero {i : Fin 6} {q : (Fin 3 → Fin 6) × (Fin 3 → F4)} (hq : q ∈ t7Tup i)
    (k : Fin 3) : q.2 k ≠ 0 := by
  intro hk
  have hdet : (t7M i q).det = 1 := by
    have h := (mem_t7Tup.mp hq).1
    rw [t7Det_eq] at h
    exact h
  have h0 : (cols (fun k => q.2 k • t7Pt i (q.1 k))).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero k
    intro r
    simp [cols, hk]
  have h1 : (cols (fun k => q.2 k • t7Pt i (q.1 k))).det = (t7V i).det := by
    rw [← t7M_mul_V, Matrix.det_mul, hdet, one_mul]
  exact t7_det_V_ne_zero i (h1.symm.trans h0)

theorem t7M_injOn {i : Fin 6} {q q' : (Fin 3 → Fin 6) × (Fin 3 → F4)} (hq : q ∈ t7Tup i)
    (hq' : q' ∈ t7Tup i) (h : t7M i q = t7M i q') : q = q' := by
  have hpt : ∀ k : Fin 3, q.2 k • t7Pt i (q.1 k) = q'.2 k • t7Pt i (q'.1 k) := by
    intro k
    rw [← t7M_base i q k, ← t7M_base i q' k, h]
  have hJ : q.1 = q'.1 := by
    funext k
    exact t7Pt_unique i _ _ _ _ (t7_coef_ne_zero hq k) (t7_coef_ne_zero hq' k) (hpt k)
  have hC : q.2 = q'.2 := by
    funext k
    have hab : q.1 k = q'.1 k := congrFun hJ k
    obtain ⟨r, hr⟩ := t7Pt_has_one i (q'.1 k)
    have h2 := congrFun (hpt k) r
    rw [hab] at h2
    simpa [hr] using h2
  exact Prod.ext hJ hC

@[expose] def t7U (M : Matrix (Fin 3) (Fin 3) F4) (hM : M.det = 1) :
    Matrix.GeneralLinearGroup (Fin 3) F4 :=
  Units.mk M (Matrix.adjugate M) (by rw [Matrix.mul_adjugate, hM, one_smul])
    (by rw [Matrix.adjugate_mul, hM, one_smul])

theorem t7M_det {i : Fin 6} {q : (Fin 3 → Fin 6) × (Fin 3 → F4)} (hq : q ∈ t7Tup i) :
    (t7M i q).det = 1 := by
  rw [← t7Det_eq]
  exact (mem_t7Tup.mp hq).1

@[expose] def t7Elt (i : Fin 6) (q : {q // q ∈ t7Tup i}) : P i :=
  ⟨t7U (t7M i q.1) (t7M_det q.2), mem_P.mpr ⟨t7M_det q.2, (mem_t7Tup.mp q.2).2⟩⟩

theorem t7Elt_injective (i : Fin 6) : Function.Injective (t7Elt i) := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩ h
  have h' : t7M i q = t7M i r :=
    congrArg (fun x : P i => ((x.1 : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4)) h
  exact Subtype.ext (t7M_injOn hq hr h')

theorem t7Elt_surjective (i : Fin 6) : Function.Surjective (t7Elt i) := by
  intro x
  obtain ⟨hdet, hstab⟩ := mem_P.mp x.2
  obtain ⟨q, hq, hM⟩ := t7M_surj hdet hstab
  exact ⟨⟨q, hq⟩, Subtype.ext (Units.ext hM)⟩

theorem vec3_ptL (i k : Fin 6) : vec3 (ptL i k) = t7Pt i k := by
  funext r
  fin_cases r <;> rfl

theorem isMultL_decide (i k j : Fin 6) (A : M3) :
    decide (∃ c : F4, c ≠ 0 ∧ Matrix.mulVec (toMat A) (t7Pt i k) = c • t7Pt i j) =
      isMultL (mulV A (ptL i k)) (ptL i j) := by
  rw [← vec3_ptL i k, ← vec3_ptL i j, toMat_mulV]
  unfold isMultL
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true, NZL_iff, smul_vec3, vec3_inj]

theorem t7Idx_toMat (i : Fin 6) (A : M3) (k : Fin 6) : t7Idx i (toMat A) k = idxL i A k := by
  unfold t7Idx idxL
  simp only [isMultL_decide]

theorem toMat_adjL (A : M3) : toMat (adjL A) = t7Adj (toMat A) := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [toMat, adjL, t7Adj]

theorem permLOf_eq (i : Fin 6) (A : M3) : permLOf i A = t7Perm i (toMat A) := by
  unfold permLOf t7Perm
  have h1 : t7Idx i (toMat A) = idxL i A := funext (t7Idx_toMat i A)
  have h2 : t7Idx i (t7Adj (toMat A)) = idxL i (adjL A) := by
    rw [← toMat_adjL]
    exact funext (t7Idx_toMat i (adjL A))
  rw [h1, h2]

theorem t7Perm_eq_permLOf (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) :
    t7Perm i M = permLOf i (ofMat M) := by
  rw [permLOf_eq, toMat_ofMat]

theorem toMat_scalMatL (c : F4) : toMat (scalMatL c) = c • (1 : Matrix (Fin 3) (Fin 3) F4) := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [toMat, scalMatL, Matrix.one_apply]

theorem mem_piL (i : Fin 6) (A : M3) : A ∈ piL i ↔ detL A = 1 ∧ stabilizes i (toMat A) := by
  unfold piL piLS slL
  simp [List.mem_filter, mem_allM3L, stab_iff]
  exact and_comm

theorem mem_piL_ofMat {i : Fin 6} {M : Matrix (Fin 3) (Fin 3) F4} (h : M.det = 1 ∧
    stabilizes i M) : ofMat M ∈ piL i :=
  (mem_piL i _).mpr ⟨by rw [detL_ofMat]; exact h.1, by rw [toMat_ofMat]; exact h.2⟩

theorem tup_iff_piL (i : Fin 6) (b : Matrix (Fin 3) (Fin 3) F4) :
    (∃ A ∈ piL i, toMat A = b) ↔ ∃ q ∈ t7Tup i, t7M i q = b := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_piL i A).mp hA
    exact t7M_surj (by rw [det_toMat]; exact h1) h2
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h1, h2⟩ := mem_t7Tup.mp hq
    refine ⟨ofMat (t7M i q), mem_piL_ofMat ⟨t7M_det hq, h2⟩, toMat_ofMat _⟩

theorem mem_tupL (i : Fin 6) (b : Matrix (Fin 3) (Fin 3) F4) :
    b ∈ (piL i).map toMat ↔ ∃ q ∈ t7Tup i, t7M i q = b := by
  rw [List.mem_map, tup_iff_piL]

theorem t7Ker_mem {i : Fin 6} {q : (Fin 3 → Fin 6) × (Fin 3 → F4)} :
    q ∈ t7Ker i ↔ q ∈ t7Tup i ∧ t7Perm i (t7M i q) = 1 := by
  unfold t7Ker
  rw [Finset.mem_filter]

theorem ker_iff_KL (i : Fin 6) (b : Matrix (Fin 3) (Fin 3) F4) :
    (∃ A ∈ (piL i).filter (fun A => decide (permLOf i A = 1)), toMat A = b) ↔
      ∃ q ∈ t7Ker i, t7M i q = b := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    rw [List.mem_filter, decide_eq_true_eq] at hA
    obtain ⟨q, hq, hqA⟩ := (tup_iff_piL i (toMat A)).mp ⟨A, hA.1, rfl⟩
    refine ⟨q, t7Ker_mem.mpr ⟨hq, ?_⟩, hqA⟩
    rw [hqA, ← permLOf_eq]
    exact hA.2
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hq1, hq2⟩ := t7Ker_mem.mp hq
    obtain ⟨A, hA, hAq⟩ := (tup_iff_piL i (t7M i q)).mpr ⟨q, hq1, rfl⟩
    refine ⟨A, List.mem_filter.mpr ⟨hA, decide_eq_true ?_⟩, hAq⟩
    rw [permLOf_eq, hAq]
    exact hq2

theorem mem_kerL (i : Fin 6) (b : Matrix (Fin 3) (Fin 3) F4) :
    b ∈ ((piL i).filter (fun A => decide (permLOf i A = 1))).map toMat ↔
      ∃ q ∈ t7Ker i, t7M i q = b :=
  (List.mem_map).trans (ker_iff_KL i b)

theorem card_eq_length_of_iff {α β : Type*} [DecidableEq β] (T : Finset α) (f : α → β)
    (L : List β) (hT : Set.InjOn f T) (hL : L.Nodup) (hmem : ∀ b, b ∈ L ↔ ∃ a ∈ T, f a = b) :
    T.card = L.length := by
  have h1 : T.image f = L.toFinset := by
    ext b
    rw [Finset.mem_image, List.mem_toFinset, hmem]
  rw [← Finset.card_image_of_injOn hT, h1, List.toFinset_card_of_nodup hL]

theorem injOn_t7Tup (i : Fin 6) : Set.InjOn (t7M i) (t7Tup i : Set _) :=
  fun _ hq _ hq' h => t7M_injOn (Finset.mem_coe.mp hq) (Finset.mem_coe.mp hq') h

theorem injOn_t7Ker (i : Fin 6) : Set.InjOn (t7M i) (t7Ker i : Set _) :=
  fun _ hq _ hq' h => t7M_injOn (t7Ker_mem.mp (Finset.mem_coe.mp hq)).1
    (t7Ker_mem.mp (Finset.mem_coe.mp hq')).1 h

theorem nodup_KL_toMat {i : Fin 6} (hnd : (piL i).Nodup) :
    (((piL i).filter (fun A => decide (permLOf i A = 1))).map toMat).Nodup :=
  List.Nodup.map toMat_injective (List.Nodup.filter _ hnd)

theorem scal_of_scalL {M : Matrix (Fin 3) (Fin 3) F4} (h : scalL (ofMat M) = true) :
    ∃ c ∈ t7Scal, M = c • (1 : Matrix (Fin 3) (Fin 3) F4) := by
  unfold scalL at h
  obtain ⟨c, hc, hcA⟩ := List.any_eq_true.mp h
  have hc' : c ≠ 0 := (NZL_iff c).mp hc
  have hM : ofMat M = scalMatL c := of_decide_eq_true hcA
  refine ⟨c, (t7Scal_iff c).mp hc', ?_⟩
  rw [← toMat_ofMat M, hM, toMat_scalMatL]

theorem t7CheckAt_sound (i : Fin 6) (h : t7CheckAt i = true) :
    (piL i).Nodup ∧ (piL i).length = 1080 ∧ (∀ A ∈ piL i, Equiv.Perm.sign (permLOf i A) = 1) ∧
      ((piL i).filter (fun A => decide (permLOf i A = 1))).length = 3 ∧
      ∀ A ∈ (piL i).filter (fun A => decide (permLOf i A = 1)), scalL A = true := by
  unfold t7CheckAt t7CheckAtS at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem t7CheckAtS_of_checkAll {S : List M3} (h : t7CheckAll S = true) :
    ∀ i : Fin 6, t7CheckAtS S i = true :=
  of_decide_eq_true h

theorem t7Check_sound (h : t7Check () = true) :
    (∀ i : Fin 6, (t7Tup i).card = 1080) ∧
      (∀ i : Fin 6, ∀ q ∈ t7Tup i, Equiv.Perm.sign (t7Perm i (t7M i q)) = 1) ∧
      (∀ i : Fin 6, (t7Ker i).card = 3) ∧
      (∀ i : Fin 6, ∀ q ∈ t7Ker i,
        ∃ c ∈ t7Scal, t7M i q = c • (1 : Matrix (Fin 3) (Fin 3) F4)) := by
  have hall : ∀ i : Fin 6, t7CheckAt i = true := t7CheckAtS_of_checkAll h
  have key := fun i : Fin 6 => t7CheckAt_sound i (hall i)
  refine ⟨fun i => ?_, fun i q hq => ?_, fun i => ?_, fun i q hq => ?_⟩
  · rw [card_eq_length_of_iff (t7Tup i) (t7M i) ((piL i).map toMat) (injOn_t7Tup i)
      (List.Nodup.map toMat_injective (key i).1) (mem_tupL i), List.length_map, (key i).2.1]
  · rw [t7Perm_eq_permLOf]
    exact (key i).2.2.1 (ofMat (t7M i q))
      (mem_piL_ofMat ⟨t7M_det hq, (mem_t7Tup.mp hq).2⟩)
  · rw [card_eq_length_of_iff (t7Ker i) (t7M i)
      (((piL i).filter (fun A => decide (permLOf i A = 1))).map toMat) (injOn_t7Ker i)
      (nodup_KL_toMat (key i).1) (mem_kerL i), List.length_map, (key i).2.2.2.1]
  · have hq' := t7Ker_mem.mp hq
    have hperm : permLOf i (ofMat (t7M i q)) = 1 := by
      rw [← t7Perm_eq_permLOf]
      exact hq'.2
    have hmemKL : ofMat (t7M i q) ∈ (piL i).filter (fun A => decide (permLOf i A = 1)) :=
      List.mem_filter.mpr ⟨mem_piL_ofMat ⟨t7M_det hq'.1, (mem_t7Tup.mp hq'.1).2⟩,
        decide_eq_true hperm⟩
    exact scal_of_scalL ((key i).2.2.2.2 (ofMat (t7M i q)) hmemKL)

theorem card_P (hcheck : t7Check () = true) (i : Fin 6) : Nat.card (P i) = 1080 := by
  have h := Nat.card_eq_of_bijective (t7Elt i) ⟨t7Elt_injective i, t7Elt_surjective i⟩
  rw [Nat.card_eq_finsetCard, (t7Check_sound hcheck).1 i] at h
  exact h.symm

theorem t7Perm_mul {i : Fin 6} {M N : Matrix (Fin 3) (Fin 3) F4} (hM : M.det = 1)
    (hN : N.det = 1) (hMs : stabilizes i M) (hNs : stabilizes i N) :
    t7Perm i (M * N) = t7Perm i M * t7Perm i N := by
  have hMN : (M * N).det = 1 := by rw [Matrix.det_mul, hM, hN, one_mul]
  ext k
  rw [Equiv.Perm.mul_apply, t7Perm_apply hN hNs k, t7Perm_apply hM hMs,
    t7Perm_apply hMN (stabilizes_mul hMs hNs) k, t7Idx_mul hMs hNs k]

theorem t7Perm_one (i : Fin 6) : t7Perm i 1 = 1 := by
  ext k
  rw [t7Perm_apply Matrix.det_one (stabilizes_one i) k, t7Idx_one, Equiv.Perm.one_apply]

@[expose] def t7Hom (i : Fin 6) : P i →* Equiv.Perm (Fin 6) where
  toFun g := t7Perm i ((g : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
  map_one' := by
    show t7Perm i ((1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = 1
    rw [Units.val_one]
    exact t7Perm_one i
  map_mul' a b := by
    obtain ⟨ha1, ha2⟩ := mem_P.mp a.2
    obtain ⟨hb1, hb2⟩ := mem_P.mp b.2
    show t7Perm i ((a.1 * b.1 : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4) = t7Perm i (a.1 : Matrix (Fin 3) (Fin 3) F4) *
        t7Perm i (b.1 : Matrix (Fin 3) (Fin 3) F4)
    rw [Units.val_mul]
    exact t7Perm_mul ha1 hb1 ha2 hb2

theorem t7_sign_of_check (hcheck : t7Check () = true) (i : Fin 6)
    (q : (Fin 3 → Fin 6) × (Fin 3 → F4)) (hq : q ∈ t7Tup i) :
    Equiv.Perm.sign (t7Perm i (t7M i q)) = 1 :=
  (t7Check_sound hcheck).2.1 i q hq

theorem t7Hom_range_le (hcheck : t7Check () = true) (i : Fin 6) :
    (t7Hom i).range ≤ alternatingGroup (Fin 6) := by
  intro σ hσ
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hσ
  obtain ⟨q, hq, hM⟩ := t7M_surj (mem_P.mp g.2).1 (mem_P.mp g.2).2
  rw [Equiv.Perm.mem_alternatingGroup]
  show Equiv.Perm.sign (t7Perm i ((g.1 : Matrix.GeneralLinearGroup (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4)) = 1
  rw [← hM]
  exact t7_sign_of_check hcheck i q hq

@[expose] def t7KerElt (i : Fin 6) (q : {q // q ∈ t7Ker i}) : (t7Hom i).ker :=
  ⟨t7Elt i ⟨q.1, (t7Ker_mem.mp q.2).1⟩, by
    rw [MonoidHom.mem_ker]
    show t7Perm i (t7M i q.1) = 1
    exact (t7Ker_mem.mp q.2).2⟩

theorem t7KerElt_injective (i : Fin 6) : Function.Injective (t7KerElt i) := by
  intro q r h
  have h1 : t7Elt i ⟨q.1, (t7Ker_mem.mp q.2).1⟩ = t7Elt i ⟨r.1, (t7Ker_mem.mp r.2).1⟩ :=
    congrArg Subtype.val h
  have h2 : (⟨q.1, (t7Ker_mem.mp q.2).1⟩ : {x // x ∈ t7Tup i}) = ⟨r.1, (t7Ker_mem.mp r.2).1⟩ :=
    t7Elt_injective i h1
  have h3 := congrArg Subtype.val h2
  exact Subtype.ext h3

theorem t7KerElt_surjective (hcheck : t7Check () = true) (i : Fin 6) :
    Function.Surjective (t7KerElt i) := by
  rintro ⟨g, hg⟩
  have hg1 : t7Hom i g = 1 := MonoidHom.mem_ker.mp hg
  obtain ⟨hdet, hstab⟩ := mem_P.mp g.2
  obtain ⟨q, hq, hM⟩ := t7M_surj hdet hstab
  have h1 : t7Perm i (t7M i q) = 1 := by
    rw [hM]
    exact hg1
  have hqk : q ∈ t7Ker i := t7Ker_mem.mpr ⟨hq, h1⟩
  exact ⟨⟨q, hqk⟩, Subtype.ext (Subtype.ext (Units.ext hM))⟩

theorem card_ker (hcheck : t7Check () = true) (i : Fin 6) : Nat.card (t7Hom i).ker = 3 := by
  have h := Nat.card_eq_of_bijective (t7KerElt i)
    ⟨t7KerElt_injective i, t7KerElt_surjective hcheck i⟩
  rw [Nat.card_eq_finsetCard, (t7Check_sound hcheck).2.2.1 i] at h
  exact h.symm

theorem t7Hom_ker_scalar (hcheck : t7Check () = true) (i : Fin 6) (x : (t7Hom i).ker) :
    ∃ c ∈ t7Scal, ((x.1.1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      c • (1 : Matrix (Fin 3) (Fin 3) F4) := by
  obtain ⟨q, rfl⟩ := t7KerElt_surjective hcheck i x
  exact (t7Check_sound hcheck).2.2.2 i q.1 q.2

theorem card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_range (hcheck : t7Check () = true) (i : Fin 6) :
    Nat.card (t7Hom i).range = 360 := by
  have h1 := Subgroup.card_mul_index (H := (t7Hom i).ker)
  rw [card_ker hcheck i, Subgroup.index_ker, card_P hcheck i] at h1
  omega

theorem t7Hom_range (hcheck : t7Check () = true) (i : Fin 6) :
    (t7Hom i).range = alternatingGroup (Fin 6) :=
  Subgroup.eq_of_le_of_card_ge (t7Hom_range_le hcheck i)
    (card_A6.trans (card_range hcheck i).symm).le

theorem center_le_ker (hcheck : t7Check () = true) (i : Fin 6) :
    Subgroup.center (P i) ≤ (t7Hom i).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hA : t7Hom i z ∈ alternatingGroup (Fin 6) :=
    t7Hom_range_le hcheck i (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  have hcomm : ∀ g : alternatingGroup (Fin 6), g * ⟨t7Hom i z, hA⟩ = ⟨t7Hom i z, hA⟩ * g := by
    intro g
    have hg : (g : Equiv.Perm (Fin 6)) ∈ (t7Hom i).range := by
      rw [t7Hom_range hcheck i]
      exact g.2
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp hg
    have hzh : h * z = z * h := Subgroup.mem_center_iff.mp hz h
    apply Subtype.ext
    show (g : Equiv.Perm (Fin 6)) * t7Hom i z = t7Hom i z * (g : Equiv.Perm (Fin 6))
    rw [← hh, ← map_mul, ← map_mul, hzh]
  have hmem : (⟨t7Hom i z, hA⟩ : alternatingGroup (Fin 6)) ∈
      Subgroup.center (alternatingGroup (Fin 6)) :=
    Subgroup.mem_center_iff.mpr hcomm
  have h4 : 4 ≤ Nat.card (Fin 6) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  rw [alternatingGroup.center_eq_bot h4] at hmem
  have h1 := congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  simpa using h1

theorem ker_le_center (hcheck : t7Check () = true) (i : Fin 6) :
    (t7Hom i).ker ≤ Subgroup.center (P i) := by
  intro x hx
  obtain ⟨c, _, hxc⟩ := t7Hom_ker_scalar hcheck i ⟨x, hx⟩
  have hxc' : ((x : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      c • (1 : Matrix (Fin 3) (Fin 3) F4) := hxc
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hxc', Matrix.mul_smul, Matrix.smul_mul,
    mul_one, one_mul]

theorem center_eq_ker (hcheck : t7Check () = true) (i : Fin 6) :
    Subgroup.center (P i) = (t7Hom i).ker :=
  le_antisymm (center_le_ker hcheck i) (ker_le_center hcheck i)

theorem card_center (hcheck : t7Check () = true) (i : Fin 6) :
    Nat.card (Subgroup.center (P i)) = 3 := by
  rw [center_eq_ker hcheck i, card_ker hcheck i]

theorem det_Xd : (Xd : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  rw [← t7Det_eq]
  decide +kernel

theorem det_Wm1 : (Wm 1 : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  rw [← t7Det_eq]
  decide +kernel

theorem det_om2 : (om2 • (1 : Matrix (Fin 3) (Fin 3) F4)).det = 1 := by
  rw [← t7Det_eq]
  decide +kernel

theorem stab_Xd : ∀ i : Fin 6, t7Stab i Xd := by
  decide +kernel

theorem stab_Wm1 : ∀ i : Fin 6, t7Stab i (Wm 1) := by
  decide +kernel

theorem stab_om2 : ∀ i : Fin 6, t7Stab i (om2 • (1 : Matrix (Fin 3) (Fin 3) F4)) := by
  decide +kernel

@[expose] def mkP (i : Fin 6) (M : Matrix (Fin 3) (Fin 3) F4) (hM : M.det = 1)
    (hs : t7Stab i M) : P i :=
  ⟨t7U M hM, mem_P.mpr ⟨hM, (t7Stab_iff i M).mp hs⟩⟩

@[expose] def wP (i : Fin 6) : P i :=
  mkP i (om2 • (1 : Matrix (Fin 3) (Fin 3) F4)) det_om2 (stab_om2 i)

theorem P_ext {i : Fin 6} {x y : P i}
    (h : ((x.1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      ((y.1 : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) : x = y :=
  Subtype.ext (Units.ext h)

theorem XW_eq' : Xd * Wm 1 = (om2 • (1 : Matrix (Fin 3) (Fin 3) F4)) * Wm 1 * Xd := by
  decide +kernel

theorem comm_eq_of {G : Type*} [Group G] {x y z : G} (h : x * y = z * y * x) :
    x * y * x⁻¹ * y⁻¹ = z := by
  rw [h]
  group

theorem w_comm (i : Fin 6) :
    mkP i Xd det_Xd (stab_Xd i) * mkP i (Wm 1) det_Wm1 (stab_Wm1 i) =
      wP i * mkP i (Wm 1) det_Wm1 (stab_Wm1 i) * mkP i Xd det_Xd (stab_Xd i) :=
  P_ext XW_eq'

theorem w_mem (i : Fin 6) : wP i ∈ commutator ↥(P i) := by
  have h : mkP i Xd det_Xd (stab_Xd i) * mkP i (Wm 1) det_Wm1 (stab_Wm1 i) *
      (mkP i Xd det_Xd (stab_Xd i))⁻¹ * (mkP i (Wm 1) det_Wm1 (stab_Wm1 i))⁻¹ ∈
        ⁅(⊤ : Subgroup ↥(P i)), ⊤⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top (mkP i Xd det_Xd (stab_Xd i)))
      (Subgroup.mem_top (mkP i (Wm 1) det_Wm1 (stab_Wm1 i)))
  rw [comm_eq_of (w_comm i)] at h
  exact h

theorem wP_sq_mat :
    (om2 • (1 : Matrix (Fin 3) (Fin 3) F4)) * (om2 • (1 : Matrix (Fin 3) (Fin 3) F4)) =
      F4.ω • (1 : Matrix (Fin 3) (Fin 3) F4) := by
  decide +kernel

theorem ker_le_commutator (hcheck : t7Check () = true) (i : Fin 6) :
    (t7Hom i).ker ≤ commutator ↥(P i) := by
  intro x hx
  obtain ⟨c, hc, hmat⟩ : ∃ c ∈ t7Scal,
      ((x : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
        c • (1 : Matrix (Fin 3) (Fin 3) F4) :=
    t7Hom_ker_scalar hcheck i ⟨x, hx⟩
  simp [t7Scal] at hc
  rcases hc with rfl | rfl | rfl
  · have hx1 : x = 1 := P_ext (by simp [hmat])
    rw [hx1]
    exact Subgroup.one_mem _
  · have hx2 : x = wP i * wP i := P_ext (hmat.trans wP_sq_mat.symm)
    rw [hx2]
    exact Subgroup.mul_mem _ (w_mem i) (w_mem i)
  · have hx3 : x = wP i := P_ext hmat
    rw [hx3]
    exact w_mem i

theorem commutator_P_eq_top (hcheck : t7Check () = true) (i : Fin 6) :
    commutator ↥(P i) = ⊤ := by
  have key := Subgroup.comap_map_eq_self (ker_le_commutator hcheck i)
  have hmap : Subgroup.map (t7Hom i) (commutator ↥(P i)) = alternatingGroup (Fin 6) := by
    show Subgroup.map (t7Hom i) ⁅(⊤ : Subgroup ↥(P i)), ⊤⁆ = alternatingGroup (Fin 6)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, t7Hom_range hcheck i]
    exact commutator_alternatingGroup_eq_self (by simp)
  rw [hmap] at key
  rw [← key, Subgroup.eq_top_iff']
  intro x
  rw [Subgroup.mem_comap, ← t7Hom_range hcheck i]
  exact MonoidHom.mem_range.mpr ⟨x, rfl⟩

theorem isPerfect_P (hcheck : t7Check () = true) (i : Fin 6) : Group.IsPerfect ↥(P i) :=
  ⟨commutator_P_eq_top hcheck i⟩

@[expose] def t7Phi (hcheck : t7Check () = true) (i : Fin 6) :
    ↥(P i) →* alternatingGroup (Fin 6) :=
  (t7Hom i).codRestrict (alternatingGroup (Fin 6))
    (fun x => t7Hom_range_le hcheck i (MonoidHom.mem_range.mpr ⟨x, rfl⟩))

theorem t7Phi_ker (hcheck : t7Check () = true) (i : Fin 6) :
    (t7Phi hcheck i).ker = (t7Hom i).ker := by
  ext x
  simp [t7Phi, MonoidHom.mem_ker, Subtype.ext_iff]

theorem t7Phi_surjective (hcheck : t7Check () = true) (i : Fin 6) :
    Function.Surjective (t7Phi hcheck i) := by
  intro y
  have hy : (y : Equiv.Perm (Fin 6)) ∈ (t7Hom i).range := by
    rw [t7Hom_range hcheck i]
    exact y.2
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  exact ⟨x, Subtype.ext hx⟩

theorem quotient_center_iso (hcheck : t7Check () = true) (i : Fin 6) :
    Nonempty (↥(P i) ⧸ Subgroup.center ↥(P i) ≃* alternatingGroup (Fin 6)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
      ((center_eq_ker hcheck i).trans (t7Phi_ker hcheck i).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (t7Phi hcheck i) (t7Phi_surjective hcheck i))⟩

theorem center_eq_comap {X P : Type*} [Group X] [Group P] (e : X ≃* P) :
    Subgroup.center X = (Subgroup.center P).comap e.toMonoidHom := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    obtain ⟨y, rfl⟩ := e.surjective g
    show e y * e x = e x * e y
    rw [← map_mul, ← map_mul, h y]
  · intro h g
    apply e.injective
    show e (g * x) = e (x * g)
    rw [map_mul, map_mul]
    exact h (e g)

theorem card_center_transport {X P : Type*} [Group X] [Group P] (e : X ≃* P) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center P) := by
  rw [center_eq_comap e]
  calc Nat.card ↥((Subgroup.center P).comap e.toMonoidHom)
      = Nat.card ↥(Subgroup.map e.toMonoidHom ((Subgroup.center P).comap e.toMonoidHom)) :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
    _ = Nat.card ↥(Subgroup.center P) := by
        rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]

theorem map_center_eq {X P : Type*} [Group X] [Group P] (e : X ≃* P) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center P := by
  rw [center_eq_comap e]
  exact Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective _

theorem isTripleCover_P (hcheck : t7Check () = true) (i : Fin 6) {X : Type*} [Group X]
    (e : X ≃* ↥(P i)) :
    CFSG.RankThree.PartTwo.Sec4.IsTripleCover X (alternatingGroup (Fin 6)) := by
  unfold CFSG.RankThree.PartTwo.Sec4.IsTripleCover
  obtain ⟨φ⟩ := quotient_center_iso hcheck i
  refine ⟨?_, ?_⟩
  · rw [card_center_transport e, card_center hcheck i]
  · exact ⟨(QuotientGroup.congr (Subgroup.center X) (Subgroup.center ↥(P i)) e
      (map_center_eq e)).trans φ⟩

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34

end

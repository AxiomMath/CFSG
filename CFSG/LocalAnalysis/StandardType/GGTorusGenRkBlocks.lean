module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenComp
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private abbrev cls {d : ℕ} {K : Type} [DecidableEq K] (t : Fin d → K) (i₀ : Fin d) :
    Finset (Fin d) :=
  Finset.univ.filter fun i => t i = t i₀

private theorem cls_mem {d : ℕ} {K : Type} [DecidableEq K] {t : Fin d → K} (i₀ i : Fin d) :
    i ∈ cls t i₀ ↔ t i = t i₀ := by
  simp [cls]

private theorem cls_const {d : ℕ} {K : Type} [DecidableEq K] {t : Fin d → K} (i₀ : Fin d)
    {i j : Fin d} (hi : i ∈ cls t i₀) (hj : j ∈ cls t i₀) : t i = t j := by
  rw [cls_mem] at hi hj
  rw [hi, hj]

private theorem cls_union {d : ℕ} {K : Type} [DecidableEq K] {t : Fin d → K} (i₀ : Fin d)
    {i : Fin d} (hi : i ∈ cls t i₀) {j : Fin d} (hj : t j = t i) : j ∈ cls t i₀ := by
  rw [cls_mem] at hi ⊢
  rw [hj, hi]

private theorem blockDiag_mul {d : ℕ} {K : Type} [Field K] {t : Fin d → K}
    {A B : Matrix (Fin d) (Fin d) K}
    (hA : ∀ i j, t i ≠ t j → A i j = 0) (hB : ∀ i j, t i ≠ t j → B i j = 0) :
    ∀ i j, t i ≠ t j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : t k = t i
  · rw [hB k j (by rw [hk]; exact hij), mul_zero]
  · rw [hA i k (fun h => hk h.symm), zero_mul]

private theorem blockRes_mul_of_blockDiag {d : ℕ} {K : Type} [Field K] {t : Fin d → K}
    {S : Finset (Fin d)}
    (hS : ∀ i ∈ S, ∀ j, t j = t i → j ∈ S)
    {A B : Matrix (Fin d) (Fin d) K}
    (hA : ∀ i j, t i ≠ t j → A i j = 0) (hB : ∀ i j, t i ≠ t j → B i j = 0) :
    TableBUE.blockRes S (A * B) = TableBUE.blockRes S A * TableBUE.blockRes S B := by
  ext a b
  simp only [TableBUE.blockRes, Matrix.mul_apply]
  set e := S.equivFin.symm with he
  have hz : ∀ k ∉ S, A (e a) k * B k (e b) = 0 := by
    intro k hk
    have hne : t (e a) ≠ t k := fun h => hk (hS (e a) (e a).2 k h.symm)
    rw [hA (e a) k hne, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort S fun k : Fin d => A (e a) k * B k (e b)]
  exact (Equiv.sum_comp e fun k : ↥S => A (e a) (↑k) * B (↑k) (e b)).symm

private theorem blockRes_eq_one_of_isBlockOn_disjoint {d : ℕ} {K : Type} [Field K]
    {S Kset : Finset (Fin d)} {M : Matrix (Fin d) (Fin d) K}
    (hM : TableBUE.IsBlockOn Kset M) (hdisj : ∀ a ∈ S, a ∉ Kset) :
    TableBUE.blockRes S M = 1 := by
  ext a b
  rw [TableBUE.blockRes, hM _ _ (Or.inl (hdisj _ (S.equivFin.symm a).2))]
  exact congrFun (congrFun (TableBUE.blockRes_one (S := S)) a) b

private theorem blockRes_inv_mul_eq_one {d : ℕ} {K : Type} [Field K] {t : Fin d → K}
    {Kset : Finset (Fin d)}
    (hKcls : ∀ i ∈ Kset, ∀ j, t j = t i → j ∈ Kset)
    {A Ainv M : Matrix (Fin d) (Fin d) K}
    (hAbd : ∀ i j, t i ≠ t j → A i j = 0)
    (hAinvbd : ∀ i j, t i ≠ t j → Ainv i j = 0)
    (hMbd : ∀ i j, t i ≠ t j → M i j = 0)
    (hAAinv : A * Ainv = 1) (hAinvA : Ainv * A = 1)
    (hAblock : TableBUE.blockRes Kset A = TableBUE.blockRes Kset M) :
    TableBUE.blockRes Kset (Ainv * M) = 1 := by
  have hm2 : TableBUE.blockRes Kset Ainv * TableBUE.blockRes Kset A = 1 := by
    have h := blockRes_mul_of_blockDiag hKcls hAinvbd hAbd
    rw [hAinvA, TableBUE.blockRes_one] at h
    exact h.symm
  calc TableBUE.blockRes Kset (Ainv * M)
      = TableBUE.blockRes Kset Ainv * TableBUE.blockRes Kset M :=
        blockRes_mul_of_blockDiag hKcls hAinvbd hMbd
    _ = TableBUE.blockRes Kset Ainv * TableBUE.blockRes Kset A := by rw [← hAblock]
    _ = 1 := hm2

private theorem isBlockOn_sdiff_of_blockExt_inv_mul {d : ℕ} {K : Type} [Field K]
    {t : Fin d → K} {S Kset : Finset (Fin d)}
    (hS : ∀ i ∈ S, ∀ j, t j = t i → j ∈ S)
    (hKconst : ∀ i ∈ Kset, ∀ j ∈ Kset, t i = t j)
    (hKcls : ∀ i ∈ Kset, ∀ j, t j = t i → j ∈ Kset)
    (hKS : Kset ⊆ S)
    {A Ainv M : Matrix (Fin d) (Fin d) K}
    (hA : TableBUE.IsBlockOn Kset A)
    (hAinv : TableBUE.IsBlockOn Kset Ainv)
    (hM : TableBUE.IsBlockOn S M)
    (hAbd : ∀ i j, t i ≠ t j → A i j = 0)
    (hAinvbd : ∀ i j, t i ≠ t j → Ainv i j = 0)
    (hMbd : ∀ i j, t i ≠ t j → M i j = 0)
    (hAAinv : A * Ainv = 1) (hAinvA : Ainv * A = 1)
    (hAblock : TableBUE.blockRes Kset A = TableBUE.blockRes Kset M) :
    TableBUE.IsBlockOn (S \ Kset) (Ainv * M) := by
  have hbres1 : TableBUE.blockRes Kset (Ainv * M) = 1 :=
    blockRes_inv_mul_eq_one hKcls hAbd hAinvbd hMbd hAAinv hAinvA hAblock
  have hboth : ∀ {i j : Fin d}, i ∈ Kset → j ∈ Kset →
      (Ainv * M) i j = (1 : Matrix (Fin d) (Fin d) K) i j := by
    intro i j hiK hjK
    have hread : (Ainv * M) i j = (TableBUE.blockRes Kset (Ainv * M))
        (Kset.equivFin ⟨i, hiK⟩) (Kset.equivFin ⟨j, hjK⟩) := by
      simp only [TableBUE.blockRes, Equiv.symm_apply_apply]
    rw [hread, hbres1]
    by_cases hij' : i = j
    · subst hij'
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (fun h => hij' (congrArg Subtype.val (Kset.equivFin.injective h))),
        Matrix.one_apply_ne hij']
  intro i j hij
  rcases hij with hi | hj
  · by_cases hiK : i ∈ Kset
    · by_cases hjK : j ∈ Kset
      · exact hboth hiK hjK
      · have hne : i ≠ j := fun h => hjK (h ▸ hiK)
        rw [Matrix.mul_apply, Matrix.one_apply_ne hne]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hkK : k ∈ Kset
        · rw [hMbd k j (fun h => hjK (hKcls k hkK j h.symm)), mul_zero]
        · rw [hAinvbd i k (fun h => hkK (hKcls i hiK k h.symm)), zero_mul]
    · have hiS : i ∉ S := fun hiS => hi (Finset.mem_sdiff.mpr ⟨hiS, hiK⟩)
      rw [TableBUE.IsBlockOn.mul_apply_left hAinv hiK, hM i j (Or.inl hiS)]
  · by_cases hjK : j ∈ Kset
    · by_cases hiK : i ∈ Kset
      · exact hboth hiK hjK
      · have hne : i ≠ j := fun h => hiK (h ▸ hjK)
        rw [Matrix.mul_apply, Matrix.one_apply_ne hne]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hkK : k ∈ Kset
        · rw [hAinvbd i k (fun h => hiK (hKcls k hkK i h)), zero_mul]
        · rw [hMbd k j (fun h => hkK (hKcls j hjK k h)), mul_zero]
    · have hjS : j ∉ S := fun hjS => hj (Finset.mem_sdiff.mpr ⟨hjS, hjK⟩)
      rw [TableBUE.IsBlockOn.mul_apply_right hM i hjS, hAinv i j (Or.inr hjK)]

private theorem isBlockOn_mul_comm_of_disjoint {d : ℕ} {K : Type} [Field K]
    {S1 S2 : Finset (Fin d)} {A B : Matrix (Fin d) (Fin d) K}
    (hA : TableBUE.IsBlockOn S1 A) (hB : TableBUE.IsBlockOn S2 B)
    (hdisj : Disjoint S1 S2) : A * B = B * A := by
  ext i j
  by_cases hi1 : i ∈ S1
  · have hi2 : i ∉ S2 := fun h => Finset.disjoint_left.mp hdisj hi1 h
    rw [TableBUE.IsBlockOn.mul_apply_left hB hi2]
    by_cases hj2 : j ∈ S2
    · have hj1 : j ∉ S1 := fun h => Finset.disjoint_left.mp hdisj h hj2
      have hij : i ≠ j := fun h => hj1 (h ▸ hi1)
      have hsum : (∑ k, A i k * B k j) = 0 := Finset.sum_eq_zero fun k _ => by
        by_cases hk1 : k ∈ S1
        · have hk2 : k ∉ S2 := fun h => Finset.disjoint_left.mp hdisj hk1 h
          have hkj : k ≠ j := fun h => hk2 (h ▸ hj2)
          rw [hB k j (Or.inl hk2), Matrix.one_apply_ne hkj, mul_zero]
        · have hik : i ≠ k := fun h => hk1 (h ▸ hi1)
          rw [hA i k (Or.inr hk1), Matrix.one_apply_ne hik, zero_mul]
      rw [Matrix.mul_apply, hsum, hA i j (Or.inr hj1), Matrix.one_apply_ne hij]
    · rw [TableBUE.IsBlockOn.mul_apply_right hB i hj2]
  · by_cases hi2 : i ∈ S2
    · rw [TableBUE.IsBlockOn.mul_apply_left hA hi1]
      by_cases hj1 : j ∈ S1
      · have hj2 : j ∉ S2 := fun h => Finset.disjoint_left.mp hdisj hj1 h
        have hij : i ≠ j := fun h => hj2 (h ▸ hi2)
        have hsum : (∑ k, B i k * A k j) = 0 := Finset.sum_eq_zero fun k _ => by
          by_cases hk2 : k ∈ S2
          · have hk1 : k ∉ S1 := fun h => Finset.disjoint_left.mp hdisj h hk2
            have hkj : k ≠ j := fun h => hk1 (h ▸ hj1)
            rw [hA k j (Or.inl hk1), Matrix.one_apply_ne hkj, mul_zero]
          · have hik : i ≠ k := fun h => hk2 (h ▸ hi2)
            rw [hB i k (Or.inr hk2), Matrix.one_apply_ne hik, zero_mul]
        rw [Matrix.mul_apply, hsum, hB i j (Or.inr hj2), Matrix.one_apply_ne hij]
      · rw [TableBUE.IsBlockOn.mul_apply_right hA i hj1]
    · rw [TableBUE.IsBlockOn.mul_apply_left hA hi1, TableBUE.IsBlockOn.mul_apply_left hB hi2,
        hA i j (Or.inl hi1), hB i j (Or.inl hi2)]

private theorem classBlockDiag_of_isBlockOn_class {d : ℕ} {K : Type} [Field K] {t : Fin d → K}
    {S : Finset (Fin d)}
    (hSconst : ∀ i ∈ S, ∀ j ∈ S, t i = t j)
    {M : Matrix (Fin d) (Fin d) K} (hM : TableBUE.IsBlockOn S M) :
    ∀ i j, t i ≠ t j → M i j = 0 := by
  intro i j hij
  have hnot : i ∉ S ∨ j ∉ S := by
    by_contra hc
    push Not at hc
    exact hij (hSconst i hc.1 j hc.2)
  rw [hM i j hnot, Matrix.one_apply_ne (fun h => hij (by rw [h]))]

private theorem mul_diagonal_comm_of_blockDiag {d : ℕ} {K : Type} [Field K] {t : Fin d → K}
    {M : Matrix (Fin d) (Fin d) K}
    (hbd : ∀ i j, t i ≠ t j → M i j = 0) : M * diagonal t = diagonal t * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : t i = t j
  · rw [hij, mul_comm]
  · rw [hbd i j hij, mul_zero, zero_mul]

private theorem entry_eq_zero_of_commute_diagonal {d : ℕ} {K : Type} [Field K] {t : Fin d → K}
    {M : Matrix (Fin d) (Fin d) K} (h : M * diagonal t = diagonal t * M) {i j : Fin d}
    (hij : t i ≠ t j) : M i j = 0 := by
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : M i j * (t j - t i) = 0 := by
    rw [mul_sub, h1]
    ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hij

private theorem mem_ggFix_iff_blockDiag {d n : ℕ} {K : Type} [Field K] {t : Fin d → K}
    (ht : ∀ i, t i ≠ 0) {δ : MulAut ↥(unitarySU 2 n K d)}
    (hδ : ∀ s : ↥(unitarySU 2 n K d),
      (((δ s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    (g : ↥(unitarySU 2 n K d)) :
    g ∈ ggFix δ ↔ ∀ i j, t i ≠ t j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
  have hdet : (diagonal t).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ht i
  let D : GL (Fin d) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal t) hdet
  have hD : ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal t :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero (diagonal t) hdet
  have hDGL : ∀ s : ↥(unitarySU 2 n K d),
      ((δ s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * D = D * (s : GL (Fin d) K) := by
    intro s
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD]
    exact hδ s
  constructor
  · intro hg i j hij
    have h := hDGL g
    rw [show δ g = g from hg] at h
    have hmat : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have h2 := congrArg (fun u : GL (Fin d) K => (u : Matrix (Fin d) (Fin d) K)) h
      rwa [Units.val_mul, Units.val_mul, hD] at h2
    exact entry_eq_zero_of_commute_diagonal hmat hij
  · intro hbd
    have hcomm : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      mul_diagonal_comm_of_blockDiag hbd
    have hcommGL : (g : GL (Fin d) K) * D = D * (g : GL (Fin d) K) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hD]
      exact hcomm
    have h := hDGL g
    have hgl : (δ g : GL (Fin d) K) = (g : GL (Fin d) K) := by
      have h2 : (δ g : GL (Fin d) K) * D = (g : GL (Fin d) K) * D := by rw [h, hcommGL]
      exact mul_right_cancel h2
    exact Subtype.ext hgl

private theorem blockDiag_det_one_mem_iSup {d n : ℕ} {K : Type} [Field K] [DecidableEq K]
    (hKd : UnitaryFieldData 2 n K) {t : Fin d → K} {c : ↥(unitarySU 2 n K d)}
    (hcbd : ∀ i j, t i ≠ t j → ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0)
    (hdet : ∀ i₀ : Fin d,
      (TableBUE.blockRes (cls t i₀)
        ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1) :
    c ∈ ⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n) (cls t i₀) := by
  have hmain : ∀ S : Finset (Fin d),
      (∀ i ∈ S, ∀ j, t j = t i → j ∈ S) →
      ∀ c : ↥(unitarySU 2 n K d),
        (∀ i j, t i ≠ t j → ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0) →
        TableBUE.IsBlockOn S ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
        (∀ i₀ ∈ S,
          (TableBUE.blockRes (cls t i₀) ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1) →
        c ∈ ⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n) (cls t i₀) := by
    intro S
    refine Finset.strongInduction (p := fun S =>
      (∀ i ∈ S, ∀ j, t j = t i → j ∈ S) →
      ∀ c : ↥(unitarySU 2 n K d),
        (∀ i j, t i ≠ t j → ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0) →
        TableBUE.IsBlockOn S ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) →
        (∀ i₀ ∈ S,
          (TableBUE.blockRes (cls t i₀) ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1) →
        c ∈ ⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n) (cls t i₀)) ?_ S
    intro S ih hSunion c hcbd hcsupp hcdet
    by_cases hS : S = ∅
    · subst hS
      have hc1 : c = 1 := by
        apply Subtype.ext; apply Units.ext; ext i j
        exact hcsupp i j (Or.inl (by simp))
      rw [hc1]
      exact (⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n) (cls t i₀)).one_mem
    · obtain ⟨r, hrS⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      let M : Matrix (Fin d) (Fin d) K := ((c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      have hKconst : ∀ i ∈ cls t r, ∀ j ∈ cls t r, t i = t j :=
        fun i hi j hj => cls_const (t := t) r hi hj
      have hKcls : ∀ i ∈ cls t r, ∀ j, t j = t i → j ∈ cls t r :=
        fun i hi j hj => cls_union (t := t) r hi hj
      have hKS : cls t r ⊆ S := by
        intro i hi
        exact hSunion r hrS i ((cls_mem r i).mp hi)
      have hMdet : (TableBUE.blockRes (cls t r) M).det = 1 := hcdet r hrS
      have hMbd : ∀ i j, t i ≠ t j → M i j = 0 := fun i j hij => hcbd i j hij
      have hMunit : (((TableBUE.blockRes (cls t r) M).map hKd.bar)ᵀ) *
          TableBUE.blockRes (cls t r) M = 1 := by
        have hcU := (mem_unitarySU_iff hKd).mp c.2
        have hmul := blockRes_mul_of_blockDiag (S := cls t r)
          (fun i hi j hj => cls_union (t := t) r hi hj)
          (A := (M.map hKd.bar)ᵀ) (B := M)
          (fun i j hij => by
            rw [Matrix.transpose_apply, Matrix.map_apply, hMbd j i hij.symm, map_zero])
          hMbd
        rw [hcU.2, TableBUE.blockRes_one, TableBUE.blockRes_map_transpose] at hmul
        exact hmul.symm
      have hne : (TableBUE.blockRes (cls t r) M).det ≠ 0 := by
        rw [hMdet]; exact one_ne_zero
      let u : ↥(unitarySU 2 n K (cls t r).card) :=
        ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (TableBUE.blockRes (cls t r) M) hne,
          (mem_unitarySU_iff hKd).mpr
            ⟨by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; exact hMdet,
             by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; exact hMunit⟩⟩
      let cK : ↥(unitarySU 2 n K d) := TableBUE.blockExtSU (cls t r) hKd u
      have hcKmem : cK ∈ TableBUE.blockSU (K := K) (n := n) (cls t r) := by
        rw [← TableBUE.range_blockExtSU (cls t r) hKd]
        exact ⟨u, rfl⟩
      have hcKmat : ((cK : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          TableBUE.blockExt (cls t r) (TableBUE.blockRes (cls t r) M) :=
        TableBUE.coe_blockExtSU (cls t r) hKd u
      have hcKbd : ∀ i j, t i ≠ t j → ((cK : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 :=
        classBlockDiag_of_isBlockOn_class hKconst (TableBUE.mem_blockSU.mp hcKmem)
      have hcKinvbd : ∀ i j, t i ≠ t j →
          ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0 :=
        classBlockDiag_of_isBlockOn_class hKconst
          (TableBUE.mem_blockSU.mp ((TableBUE.blockSU (cls t r)).inv_mem hcKmem))
      let c' : ↥(unitarySU 2 n K d) := cK⁻¹ * c
      have hc'bd : ∀ i j, t i ≠ t j →
          ((c' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
        intro i j hij
        have := blockDiag_mul hcKinvbd hcbd i j hij
        simpa only [c', M, Subgroup.coe_mul, Units.val_mul] using this
      have hAAinv : ((cK : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      have hAinvA : ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
          ((cK : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      have hAblock : TableBUE.blockRes (cls t r) ((cK : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          TableBUE.blockRes (cls t r) M := by
        rw [hcKmat, TableBUE.blockRes_blockExt]
      have hc'supp : TableBUE.IsBlockOn (S \ cls t r)
          ((c' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        have hres := isBlockOn_sdiff_of_blockExt_inv_mul (t := t) (S := S) (Kset := cls t r)
          hSunion hKconst hKcls hKS
          (A := ((cK : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
          (Ainv := ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)))
          (M := M)
          (TableBUE.mem_blockSU.mp hcKmem)
          (TableBUE.mem_blockSU.mp ((TableBUE.blockSU (cls t r)).inv_mem hcKmem))
          hcsupp hcKbd hcKinvbd hcbd hAAinv hAinvA hAblock
        simpa only [c', M, Subgroup.coe_mul, Units.val_mul] using hres
      have hSunion' : ∀ i ∈ S \ cls t r, ∀ j, t j = t i → j ∈ S \ cls t r := by
        intro i hi j hj
        obtain ⟨hiS, hiK⟩ := Finset.mem_sdiff.mp hi
        exact Finset.mem_sdiff.mpr ⟨hSunion i hiS j hj, fun hjK => hiK (hKcls j hjK i hj.symm)⟩
      have hc'det : ∀ i₀ ∈ S \ cls t r,
          (TableBUE.blockRes (cls t i₀) ((c' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).det = 1 := by
        intro i₀ hi₀
        obtain ⟨hi₀S, hi₀K⟩ := Finset.mem_sdiff.mp hi₀
        have hcls_ne : ∀ a ∈ cls t i₀, a ∉ cls t r := by
          intro a ha haK
          have ha1 : t a = t i₀ := (cls_mem i₀ a).mp ha
          have ha2 : t a = t r := (cls_mem r a).mp haK
          exact hi₀K ((cls_mem r i₀).mpr (ha1.symm.trans ha2))
        have hAinvBlock1 : TableBUE.blockRes (cls t i₀)
            ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 :=
          blockRes_eq_one_of_isBlockOn_disjoint
            (TableBUE.mem_blockSU.mp ((TableBUE.blockSU (cls t r)).inv_mem hcKmem)) hcls_ne
        have hbres := blockRes_mul_of_blockDiag (S := cls t i₀)
          (fun i hi j hj => cls_union (t := t) i₀ hi hj)
          (A := ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)))
          (B := M) hcKinvbd hcbd
        have hc'mat : ((c' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            ((((cK⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) * M := by
          simp only [c', M, Subgroup.coe_mul, Units.val_mul]
        rw [hc'mat, hbres, hAinvBlock1, one_mul]
        exact hcdet i₀ hi₀S
      have hssub : S \ cls t r ⊂ S := by
        refine (Finset.ssubset_iff_subset_ne).mpr ⟨Finset.sdiff_subset, fun h => ?_⟩
        have : r ∈ S \ cls t r := h.symm ▸ hrS
        exact (Finset.mem_sdiff.mp this).2 ((cls_mem r r).mpr rfl)
      have hc' := ih (S \ cls t r) hssub hSunion' c' hc'bd hc'supp hc'det
      have hc_eq : c = cK * c' := by
        simp only [c']
        group
      rw [hc_eq]
      exact (⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n) (cls t i₀)).mul_mem
        (Subgroup.mem_iSup_of_mem r hcKmem) hc'
  have hres := hmain Finset.univ (by intro i _ j _; exact Finset.mem_univ j) c hcbd
    (by
      intro i j h
      rcases h with hh | hh
      · exact absurd (Finset.mem_univ i) hh
      · exact absurd (Finset.mem_univ j) hh)
    (by intro i₀ _; exact hdet i₀)
  simpa only [cls] using hres

private theorem blockRes_det_commutator_eq_one {d n : ℕ} {K : Type} [Field K] [DecidableEq K]
    {t : Fin d → K} (i₀ : Fin d) {g h : ↥(unitarySU 2 n K d)}
    (hgM : ∀ i j, t i ≠ t j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0)
    (hhM : ∀ i j, t i ≠ t j → ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0)
    (hgiM : ∀ i j, t i ≠ t j →
      ((((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0)
    (hhiM : ∀ i j, t i ≠ t j →
      ((((h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) i j = 0) :
    (TableBUE.blockRes (cls t i₀)
      (((g * h * g⁻¹ * h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K)).det = 1 := by
  have hgMgi : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have hhMhi : ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((((h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  set A := TableBUE.blockRes (cls t i₀) ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hA
  set B := TableBUE.blockRes (cls t i₀) ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hB
  set A' := TableBUE.blockRes (cls t i₀)
    ((((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) with hA'
  set B' := TableBUE.blockRes (cls t i₀)
    ((((h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) with hB'
  have hAA' : A * A' = 1 := by
    rw [hA, hA', ← blockRes_mul_of_blockDiag (S := cls t i₀)
        (fun i hi j hj => cls_union (t := t) i₀ hi hj) hgM hgiM,
      hgMgi, TableBUE.blockRes_one]
  have hBB' : B * B' = 1 := by
    rw [hB, hB', ← blockRes_mul_of_blockDiag (S := cls t i₀)
        (fun i hi j hj => cls_union (t := t) i₀ hi hj) hhM hhiM,
      hhMhi, TableBUE.blockRes_one]
  have hdetA' : A'.det = (A.det)⁻¹ := by
    have := congrArg Matrix.det hAA'
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact eq_inv_of_mul_eq_one_right this
  have hdetB' : B'.det = (B.det)⁻¹ := by
    have := congrArg Matrix.det hBB'
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact eq_inv_of_mul_eq_one_right this
  have hfull : TableBUE.blockRes (cls t i₀)
      (((g * h * g⁻¹ * h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = A * B * A' * B' := by
    have hM : (((g * h * g⁻¹ * h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) =
        ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) *
              ((((h⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
                Matrix (Fin d) (Fin d) K)) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hM, blockRes_mul_of_blockDiag (S := cls t i₀)
        (fun i hi j hj => cls_union (t := t) i₀ hi hj)
        (blockDiag_mul (blockDiag_mul hgM hhM) hgiM) hhiM,
      blockRes_mul_of_blockDiag (S := cls t i₀)
        (fun i hi j hj => cls_union (t := t) i₀ hi hj) (blockDiag_mul hgM hhM) hgiM,
      blockRes_mul_of_blockDiag (S := cls t i₀)
        (fun i hi j hj => cls_union (t := t) i₀ hi hj) hgM hhM]
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAA'
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at this
    exact one_ne_zero this.symm
  have hBdet : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB'
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at this
    exact one_ne_zero this.symm
  rw [hfull, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hdetA', hdetB']
  calc A.det * B.det * (A.det)⁻¹ * (B.det)⁻¹
      = (A.det * (A.det)⁻¹) * (B.det * (B.det)⁻¹) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ hAdet, mul_inv_cancel₀ hBdet, mul_one]

open Classical in
theorem ggFix_diag_block_structure
    {d n : ℕ} {K : Type} [Field K] [Finite K] (hKd : UnitaryFieldData 2 n K)
    {t : Fin d → K} (ht : ∀ i, t i ≠ 0) (δ : MulAut ↥(unitarySU 2 n K d))
    (hδ : ∀ s : ↥(unitarySU 2 n K d),
      (((δ s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    (∀ i₀ : Fin d,
      TableBUE.blockSU (K := K) (n := n) (Finset.univ.filter fun i => t i = t i₀) ≤ ggFix δ ∧
        ∀ g ∈ ggFix δ, ∀ x ∈ TableBUE.blockSU (K := K) (n := n)
          (Finset.univ.filter fun i => t i = t i₀), g * x * g⁻¹ ∈ TableBUE.blockSU (K := K) (n := n)
            (Finset.univ.filter fun i => t i = t i₀)) ∧
    (∀ i₀ j₀ : Fin d, t i₀ ≠ t j₀ →
      ∀ x ∈ TableBUE.blockSU (K := K) (n := n) (Finset.univ.filter fun i => t i = t i₀),
      ∀ y ∈ TableBUE.blockSU (K := K) (n := n) (Finset.univ.filter fun i => t i = t j₀),
        x * y = y * x) ∧
    ⁅ggFix δ, ggFix δ⁆ ≤ ⨆ i₀ : Fin d,
      TableBUE.blockSU (K := K) (n := n) (Finset.univ.filter fun i => t i = t i₀) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i₀
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (mem_ggFix_iff_blockDiag ht hδ x).mpr fun i j hij => by
        have hnot : i ∉ cls t i₀ ∨ j ∉ cls t i₀ := by
          by_contra hc
          push Not at hc
          exact hij (cls_const (t := t) i₀ hc.1 hc.2)
        rw [TableBUE.mem_blockSU.mp hx i j hnot]
        exact Matrix.one_apply_ne fun h => hij (by rw [h])
    · intro g hg x hx
      have hgM := (mem_ggFix_iff_blockDiag ht hδ g).mp hg
      have hgiM := (mem_ggFix_iff_blockDiag ht hδ g⁻¹).mp ((ggFix δ).inv_mem hg)
      have hxM := TableBUE.mem_blockSU.mp hx
      have hGGi : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((((g⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      have hres := StdSubRestU.isBlockOn_conj hGGi hxM
        (fun i k hi hk => hgM i k (fun h => hi (cls_union (t := t) i₀ hk h)))
        (fun l j hl hj => hgiM l j (fun h => hj (cls_union (t := t) i₀ hl h.symm)))
      rw [TableBUE.mem_blockSU]
      simpa only [Subgroup.coe_mul, Units.val_mul] using hres
  · intro i₀ j₀ hij x hx y hy
    have hdisj : Disjoint (cls t i₀) (cls t j₀) := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      exact hij (((cls_mem i₀ a).mp ha1).symm.trans ((cls_mem j₀ a).mp ha2))
    apply Subtype.ext
    apply Units.ext
    exact isBlockOn_mul_comm_of_disjoint (TableBUE.mem_blockSU.mp hx) (TableBUE.mem_blockSU.mp hy)
      hdisj
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    apply blockDiag_det_one_mem_iSup hKd
    · have hgM := (mem_ggFix_iff_blockDiag ht hδ g).mp hg
      have hhM := (mem_ggFix_iff_blockDiag ht hδ h).mp hh
      have hgiM := (mem_ggFix_iff_blockDiag ht hδ g⁻¹).mp ((ggFix δ).inv_mem hg)
      have hhiM := (mem_ggFix_iff_blockDiag ht hδ h⁻¹).mp ((ggFix δ).inv_mem hh)
      intro i j hij
      have h1 := blockDiag_mul hgM hhM
      have h2 := blockDiag_mul h1 hgiM
      have h3 := blockDiag_mul h2 hhiM
      simpa only [Subgroup.coe_mul, Units.val_mul] using h3 i j hij
    · intro i₀
      have hgM := (mem_ggFix_iff_blockDiag ht hδ g).mp hg
      have hhM := (mem_ggFix_iff_blockDiag ht hδ h).mp hh
      have hgiM := (mem_ggFix_iff_blockDiag ht hδ g⁻¹).mp ((ggFix δ).inv_mem hg)
      have hhiM := (mem_ggFix_iff_blockDiag ht hδ h⁻¹).mp ((ggFix δ).inv_mem hh)
      exact blockRes_det_commutator_eq_one i₀ hgM hhM hgiM hhiM

end CFSG.StandardType

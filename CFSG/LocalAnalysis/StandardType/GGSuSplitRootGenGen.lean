module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSUGen
public import CFSG.LieType.SeitzGeneration.UnitarySplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.CALinearPlane
  CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration CFSG.LieType.BorelTits
  CFSG.LieType.Universal.SpecialLinear CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwo

variable {n r ε : ℕ} {K : Type} [Field K]

private noncomputable def hypReindexGL (r ε : ℕ) (K : Type) [Field K] :
    GL (HypIndex r ε) K ≃* GL (Fin (2 * r + ε)) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (hypEquivFin r ε)).toMulEquiv

private theorem coe_hypReindexGL {g : GL (HypIndex r ε) K} :
    ((hypReindexGL r ε K g : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      Matrix.reindex (hypEquivFin r ε) (hypEquivFin r ε)
        (g : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  rw [hypReindexGL, Units.coe_mapEquiv]
  rfl

private theorem bar_eq_unitaryInvolution (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (c : K) :
    h.bar c = unitaryInvolution K 2 n c := by
  rw [UnitaryFieldData.bar_apply, unitaryInvolution_apply]

private theorem reindex_hypGram_eq_antidiag (hε : ε ≤ 1) :
    Matrix.reindex (hypEquivFin r ε) (hypEquivFin r ε) (hypGram r ε K) =
      antidiag (2 * r + ε) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, hypGram_apply, antidiag, Matrix.of_apply]
  have hiff : ((hypEquivFin r ε).symm j = hypPartner ((hypEquivFin r ε).symm i)) ↔
      (j = Fin.rev i) := by
    rw [Equiv.symm_apply_eq, hypEquivFin_hypPartner hε, Equiv.apply_symm_apply]
  by_cases h : j = Fin.rev i
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

private theorem map_hypSU_eq_SU (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1) :
    (hypSU h r ε).map (hypReindexGL r ε K).toMonoidHom =
      SU (unitaryInvolution K 2 n) (2 * r + ε) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  have hbar : ⇑h.bar = ⇑(unitaryInvolution K 2 n) := by
    funext c; exact bar_eq_unitaryInvolution h c
  have hgram : hypGram r ε K =
      (antidiag (2 * r + ε)).submatrix (hypEquivFin r ε) (hypEquivFin r ε) := by
    rw [← reindex_hypGram_eq_antidiag hε, Matrix.reindex_apply, Matrix.submatrix_submatrix]
    simp
  ext g
  rw [Subgroup.mem_map_equiv]
  let y : GL (HypIndex r ε) K := (hypReindexGL r ε K).symm g
  change y ∈ hypSU h r ε ↔ g ∈ SU (unitaryInvolution K 2 n) (2 * r + ε)
  have hy : (y : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).submatrix
        (hypEquivFin r ε) (hypEquivFin r ε) := by
    rw [show y = (hypReindexGL r ε K).symm g from rfl, hypReindexGL, Units.mapEquiv_symm,
      Units.coe_mapEquiv]
    rfl
  rw [mem_hypSU, mem_SU]
  let Rie := Matrix.reindexAlgEquiv K K (hypEquivFin r ε)
  have hRy : Rie (y : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) := by
    rw [show Rie = Matrix.reindexAlgEquiv K K (hypEquivFin r ε) from rfl,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, hy, Matrix.submatrix_submatrix]
    simp
  have hRgram : Rie (hypGram r ε K) = antidiag (2 * r + ε) := by
    rw [show Rie = Matrix.reindexAlgEquiv K K (hypEquivFin r ε) from rfl,
      Matrix.coe_reindexAlgEquiv]
    exact reindex_hypGram_eq_antidiag hε
  have hRmap : ∀ M : Matrix (HypIndex r ε) (HypIndex r ε) K,
      Rie (M.map h.bar) = (Rie M).map (unitaryInvolution K 2 n) := by
    intro M
    change (M.map h.bar).submatrix (hypEquivFin r ε).symm (hypEquivFin r ε).symm =
      (M.submatrix (hypEquivFin r ε).symm (hypEquivFin r ε).symm).map
        (unitaryInvolution K 2 n)
    rw [Matrix.submatrix_map, hbar]
  have hRtrans : ∀ M : Matrix (HypIndex r ε) (HypIndex r ε) K,
      Rie Mᵀ = (Rie M)ᵀ := by
    intro M
    exact (Matrix.transpose_reindex (hypEquivFin r ε) (hypEquivFin r ε) M).symm
  have hRy' : Rie.symm (g : Matrix _ _ _) = (y : Matrix _ _ _) := by
    rw [← hRy, AlgEquiv.symm_apply_apply]
  have hRgram' : Rie.symm (antidiag (2 * r + ε)) = hypGram r ε K := by
    rw [← hRgram, AlgEquiv.symm_apply_apply]
  have hRmap' : ∀ M : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K,
      Rie.symm (M.map (unitaryInvolution K 2 n)) = (Rie.symm M).map h.bar := by
    intro M
    change (M.map (unitaryInvolution K 2 n)).submatrix (hypEquivFin r ε) (hypEquivFin r ε) =
      (M.submatrix (hypEquivFin r ε) (hypEquivFin r ε)).map h.bar
    rw [Matrix.submatrix_map, ← hbar]
  have hRtrans' : ∀ M : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K,
      Rie.symm Mᵀ = (Rie.symm M)ᵀ := by
    intro M
    exact (Matrix.transpose_reindex (hypEquivFin r ε).symm (hypEquivFin r ε).symm M).symm
  have hiff : (((y : Matrix _ _ _).map h.bar)ᵀ * hypGram r ε K * (y : Matrix _ _ _) =
        hypGram r ε K) ↔
      (((g : Matrix _ _ _).map (unitaryInvolution K 2 n))ᵀ * antidiag (2 * r + ε) *
        (g : Matrix _ _ _) = antidiag (2 * r + ε)) := by
    constructor
    · intro h1
      have h2 := congrArg Rie h1
      rw [map_mul, map_mul] at h2
      rw [hRtrans ((y : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar),
        hRmap (y : Matrix (HypIndex r ε) (HypIndex r ε) K), hRy, hRgram] at h2
      exact h2
    · intro h1
      have h2 := congrArg Rie.symm h1
      rw [map_mul, map_mul] at h2
      rw [hRtrans' ((g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).map
          (unitaryInvolution K 2 n)),
        hRmap' (g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K), hRy', hRgram'] at h2
      exact h2
  have hdet : ((y : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1) ↔
      ((g : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).det = 1) := by
    rw [hy, Matrix.det_submatrix_equiv_self]
  exact ⟨fun h => ⟨hdet.mp h.2, hiff.mp h.1⟩, fun h => ⟨hiff.mpr h.2, hdet.mpr h.1⟩⟩

noncomputable def hypSUEquiv (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1) :
    hypSU h r ε ≃* SU (unitaryInvolution K 2 n) (2 * r + ε) :=
  ((hypReindexGL r ε K).subgroupMap (hypSU h r ε)).trans
    (MulEquiv.subgroupCongr (map_hypSU_eq_SU h hε))

theorem coe_hypSUEquiv (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1) (M : hypSU h r ε) :
    (((hypSUEquiv h hε M : SU (unitaryInvolution K 2 n) (2 * r + ε)) :
        GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) =
      Matrix.reindex (hypEquivFin r ε) (hypEquivFin r ε)
        ((M : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  change ((hypReindexGL r ε K (M : GL (HypIndex r ε) K)) :
    Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) = _
  exact coe_hypReindexGL

private theorem coe_hypSUEquiv_symm (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1)
    (M : SU (unitaryInvolution K 2 n) (2 * r + ε)) :
    (((hypSUEquiv h hε).symm M : hypSU h r ε) : GL (HypIndex r ε) K) =
      (hypReindexGL r ε K).symm (M : GL (Fin (2 * r + ε)) K) :=
  rfl

private theorem signedPerm_conj_apply {π : Equiv.Perm (HypIndex r ε)}
    (M : Matrix (HypIndex r ε) (HypIndex r ε) K) (x y : HypIndex r ε) :
    ((signedPerm π (fun _ => (1 : K)) * M *
      (signedPerm π (fun _ => (1 : K)))⁻¹ : Matrix (HypIndex r ε) (HypIndex r ε) K)) x y =
      M (π.symm x) (π.symm y) := by
  have hPinv : (signedPerm π (fun _ => (1 : K)) : Matrix (HypIndex r ε) (HypIndex r ε) K)⁻¹ =
      signedPerm π.symm (fun _ => (1 : K)) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [signedPerm_mul_signedPerm, show π * π.symm = 1 from mul_inv_cancel π]
    ext i j
    simp [signedPerm_apply, Matrix.one_apply]
    rfl
  have hsingle : ∀ a b (c : K), signedPerm π (fun _ => (1 : K)) * single a b c *
      (signedPerm π (fun _ => (1 : K)))⁻¹ = single (π a) (π b) c := by
    intro a b c
    rw [hPinv, signedPerm_mul_single, single_mul_signedPerm]
    simp
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [Matrix.mul_sum, Matrix.sum_mul, hsingle, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single (π.symm x)]
  · rw [Finset.sum_eq_single (π.symm y)]
    · simp
    · intro b _ hb
      have h1 : y ≠ π b := fun h => hb (by rw [h]; exact (Equiv.symm_apply_apply π b).symm)
      rw [if_neg (fun h => h1 h.2.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a _ ha
    have h1 : x ≠ π a := fun h => ha (by rw [h]; exact (Equiv.symm_apply_apply π a).symm)
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg (fun h => h1 h.1.symm)]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem isHypBlockOn_signedPerm_conj {T : Set (HypIndex r ε)}
    {M : Matrix (HypIndex r ε) (HypIndex r ε) K} (hM : IsHypBlockOn T M)
    (π : Equiv.Perm (HypIndex r ε)) :
    IsHypBlockOn (π '' T) (signedPerm π (fun _ => (1 : K)) * M *
      (signedPerm π (fun _ => (1 : K)))⁻¹) := by
  intro x y hxy
  have hxy' : π.symm x ∉ T ∨ π.symm y ∉ T := by
    rcases hxy with hx | hy
    · exact Or.inl fun h => hx ⟨π.symm x, h, by simp⟩
    · exact Or.inr fun h => hy ⟨π.symm y, h, by simp⟩
  have h1 : ((signedPerm π (fun _ => (1 : K)) * M *
      (signedPerm π (fun _ => (1 : K)))⁻¹ : Matrix (HypIndex r ε) (HypIndex r ε) K)) x y =
      M (π.symm x) (π.symm y) := signedPerm_conj_apply (π := π) (M := M) x y
  rw [h1, Matrix.one_apply, hM (π.symm x) (π.symm y) hxy', Matrix.one_apply]
  by_cases h : x = y
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun hh => h (π.symm.injective hh)), if_neg h]

private noncomputable def linePerm (m : Fin r) : Equiv.Perm (HypIndex r ε) :=
  weylPerm (ε := ε) (swapSet {m})

private noncomputable def pairPerm (i j : Fin r) : Equiv.Perm (HypIndex r ε) :=
  weylPerm (ε := ε) (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j))

private theorem weylCoeff_one (h : UnitaryFieldData 2 n K)
    (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    weylCoeff h 1 w = (fun _ : HypIndex r ε => (1 : K)) := by
  funext a
  rcases a with i | k | i <;> simp [weylCoeff]

private theorem coe_lineWeyl (h : UnitaryFieldData 2 n K) (m : Fin r) :
    (((lineWeyl h ε m : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      signedPerm (linePerm (ε := ε) m) (fun _ => (1 : K)) := by
  rw [lineWeyl, coe_weylElt, weylMat, weylCoeff_one]
  rfl

private theorem coe_pairWeyl (h : UnitaryFieldData 2 n K) (i j : Fin r) :
    (((pairWeyl h ε i j : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      signedPerm (pairPerm (ε := ε) i j) (fun _ => (1 : K)) := by
  rw [pairWeyl, coe_weylElt, weylMat, weylCoeff_one]
  rfl

private theorem linePerm_inl_self (m : Fin r) :
    linePerm (ε := ε) m (.inl m) = .inr (.inr m) := by
  rw [linePerm, weylPerm_swapSet_inl]
  simp

private theorem linePerm_inr_inr_self (m : Fin r) :
    linePerm (ε := ε) m (.inr (.inr m)) = .inl m := by
  rw [linePerm, weylPerm_swapSet_inr_inr]
  simp

private theorem linePerm_inl_of_ne {m i : Fin r} (h : i ≠ m) :
    linePerm (ε := ε) m (.inl i) = .inl i := by
  rw [linePerm, weylPerm_swapSet_inl]
  simp [h]

private theorem linePerm_inr_inr_of_ne {m i : Fin r} (h : i ≠ m) :
    linePerm (ε := ε) m (.inr (.inr i)) = .inr (.inr i) := by
  rw [linePerm, weylPerm_swapSet_inr_inr]
  simp [h]

private theorem linePerm_inr_inl (m : Fin r) (k : Fin ε) :
    linePerm (ε := ε) m (.inr (.inl k)) = .inr (.inl k) := by
  rw [linePerm, weylPerm_inr_inl]

private theorem linePerm_hypPartner (m : Fin r) (a : HypIndex r ε) :
    linePerm (ε := ε) m (hypPartner a) = hypPartner (linePerm (ε := ε) m a) :=
  weylPerm_hypPartner (swapSet_mem_hypWeyl {m}) a

private theorem pairPerm_inl (i j k : Fin r) :
    pairPerm (ε := ε) i j (.inl k) = .inl (Equiv.swap i j k) := by
  rw [pairPerm, weylPerm_inl]
  rfl

private theorem pairPerm_inr_inr (i j k : Fin r) :
    pairPerm (ε := ε) i j (.inr (.inr k)) = .inr (.inr (Equiv.swap i j k)) := by
  rw [pairPerm, weylPerm_inr_inr]
  rfl

private theorem pairPerm_inr_inl (i j : Fin r) (k : Fin ε) :
    pairPerm (ε := ε) i j (.inr (.inl k)) = .inr (.inl k) := by
  rw [pairPerm, weylPerm_inr_inl]

private theorem pairPerm_hypPartner (i j : Fin r) (a : HypIndex r ε) :
    pairPerm (ε := ε) i j (hypPartner a) = hypPartner (pairPerm (ε := ε) i j a) :=
  weylPerm_hypPartner (sumCongr_mem_hypWeyl (Equiv.swap i j)) a

private theorem signedPerm_one_inv (π : Equiv.Perm (HypIndex r ε)) :
    (signedPerm π (fun _ => (1 : K)) : Matrix (HypIndex r ε) (HypIndex r ε) K)⁻¹ =
      signedPerm π.symm (fun _ => (1 : K)) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [signedPerm_mul_signedPerm, show π * π.symm = 1 from mul_inv_cancel π]
  ext i j
  simp [signedPerm_apply, Matrix.one_apply]
  rfl

private theorem pairPerm_symm_image_lineCoords (i j : Fin r) :
    (pairPerm (ε := ε) j i).symm '' lineCoords (ε := ε) i = lineCoords (ε := ε) j := by
  have h1 : pairPerm (ε := ε) j i (.inl j) = .inl i := by
    rw [pairPerm_inl]
    simp [Equiv.swap_apply_right]
  have h2 : ∀ k : Fin ε, pairPerm (ε := ε) j i (.inr (.inl k)) = .inr (.inl k) :=
    fun k => pairPerm_inr_inl (i := j) (j := i) (k := k)
  have h3 : pairPerm (ε := ε) j i (.inr (.inr j)) = .inr (.inr i) := by
    rw [pairPerm_inr_inr]
    simp [Equiv.swap_apply_right]
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases hb with rfl | ⟨k, rfl⟩ | rfl
    · refine Or.inl ?_
      rw [← h1, Equiv.symm_apply_apply]
    · refine Or.inr (Or.inl ⟨k, ?_⟩)
      rw [← h2 k, Equiv.symm_apply_apply]
      exact (h2 k).symm
    · refine Or.inr (Or.inr ?_)
      rw [← h3, Equiv.symm_apply_apply]
  · intro ha
    rcases ha with rfl | ⟨k, rfl⟩ | rfl
    · refine ⟨.inl i, Or.inl rfl, ?_⟩
      rw [← h1, Equiv.symm_apply_apply]
    · refine ⟨.inr (.inl k), Or.inr (Or.inl ⟨k, rfl⟩), ?_⟩
      rw [← h2 k, Equiv.symm_apply_apply]
      exact (h2 k).symm
    · refine ⟨.inr (.inr i), Or.inr (Or.inr rfl), ?_⟩
      rw [← h3, Equiv.symm_apply_apply]

private theorem coe_hypSUEquiv_symm_matrix (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1) (M : SU (unitaryInvolution K 2 n) (2 * r + ε)) :
    ((((hypSUEquiv h hε).symm M : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((M : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).submatrix
        (hypEquivFin r ε) (hypEquivFin r ε) := by
  rw [coe_hypSUEquiv_symm, hypReindexGL, Units.mapEquiv_symm, Units.coe_mapEquiv]
  rfl

private theorem hypEquivFin_symm_rev (hε : ε ≤ 1) (i : Fin (2 * r + ε)) :
    (hypEquivFin r ε).symm (Fin.rev i) = hypPartner ((hypEquivFin r ε).symm i) := by
  rw [Equiv.symm_apply_eq, hypEquivFin_hypPartner hε, Equiv.apply_symm_apply]

private theorem exists_line_of_ne_rev (hε : ε ≤ 1) {i : Fin (2 * r + ε)} (hi : i ≠ Fin.rev i) :
    ∃ k : Fin r,
      (hypEquivFin r ε).symm i = .inl k ∨ (hypEquivFin r ε).symm i = .inr (.inr k) := by
  rcases hx : (hypEquivFin r ε).symm i with k | z | k
  · exact ⟨k, Or.inl rfl⟩
  · exfalso
    apply hi
    have h1 := hypEquivFin_symm_rev hε i
    rw [hx, hypPartner_inr_inl, ← hx] at h1
    exact ((hypEquivFin r ε).symm.injective h1).symm
  · exact ⟨k, Or.inr rfl⟩

private theorem exists_eq_inr_inl_of_rev_eq (hε : ε ≤ 1) {k : Fin (2 * r + ε)}
    (hk : Fin.rev k = k) : ∃ z : Fin ε, (hypEquivFin r ε).symm k = .inr (.inl z) := by
  have h1 := hypEquivFin_symm_rev hε k
  rw [hk] at h1
  rcases hx : (hypEquivFin r ε).symm k with l | z | l
  · rw [hx, hypPartner_inl] at h1
    exact absurd h1 (by simp)
  · exact ⟨z, rfl⟩
  · rw [hx, hypPartner_inr_inr] at h1
    exact absurd h1 (by simp)

private theorem mem_lineCoords_of_eq (hε : ε ≤ 1) {i : Fin (2 * r + ε)} {k : Fin r}
    (hk : (hypEquivFin r ε).symm i = .inl k ∨ (hypEquivFin r ε).symm i = .inr (.inr k))
    {a : HypIndex r ε} (ha : hypEquivFin r ε a = i ∨ hypEquivFin r ε a = Fin.rev i) :
    a ∈ lineCoords (ε := ε) k := by
  have ha' : a = (hypEquivFin r ε).symm i ∨ a = hypPartner ((hypEquivFin r ε).symm i) := by
    rcases ha with ha | ha
    · exact Or.inl ((Equiv.eq_symm_apply _).mpr ha)
    · refine Or.inr ?_
      rw [← hypEquivFin_symm_rev hε]
      exact (Equiv.eq_symm_apply _).mpr ha
  rcases hk with hk | hk <;> rw [hk] at ha' <;> rcases ha' with rfl | rfl <;> simp [lineCoords]

private theorem inr_inl_mem_lineCoords (k : Fin r) (z : Fin ε) :
    (.inr (.inl z) : HypIndex r ε) ∈ lineCoords (ε := ε) k :=
  Or.inr (Or.inl ⟨z, rfl⟩)

private theorem symm_mem_lineBlock (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1) {T : Set (Fin (2 * r + ε))} {k : Fin r}
    (hT : ∀ a, hypEquivFin r ε a ∈ T → a ∈ lineCoords (ε := ε) k)
    {M : SU (unitaryInvolution K 2 n) (2 * r + ε)}
    (hM : ∀ u v, (u ∉ T ∨ v ∉ T) → ((M : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) u v =
        (1 : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) u v) :
    (hypSUEquiv h hε).symm M ∈ lineBlock h k := by
  rw [lineBlock, mem_hypBlock, coe_hypSUEquiv_symm_matrix]
  intro a b hab
  have huv : hypEquivFin r ε a ∉ T ∨ hypEquivFin r ε b ∉ T :=
    hab.imp (fun ha h' => ha (hT a h')) (fun hb h' => hb (hT b h'))
  rw [Matrix.submatrix_apply, hM _ _ huv, Matrix.one_apply, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

private theorem longRootMatrix_apply_of_not_mem {N : ℕ} {i : Fin N} (c : K) {u v : Fin N}
    (huv : u ∉ ({i, Fin.rev i} : Set (Fin N)) ∨ v ∉ ({i, Fin.rev i} : Set (Fin N))) :
    longRootMatrix i c u v = (1 : Matrix (Fin N) (Fin N) K) u v := by
  have hne : ¬ (i = u ∧ Fin.rev i = v) := by
    rintro ⟨rfl, rfl⟩
    rcases huv with hu | hv
    · exact hu (by simp)
    · exact hv (by simp)
  rw [longRootMatrix, Matrix.add_apply, Matrix.single_apply, if_neg hne, add_zero]

private theorem heisenbergMatrix_apply_of_not_mem (σ : K ≃+* K) {N : ℕ} {i k : Fin N} (a b : K)
    {u v : Fin N}
    (huv : u ∉ ({i, k, Fin.rev i} : Set (Fin N)) ∨ v ∉ ({i, k, Fin.rev i} : Set (Fin N))) :
    heisenbergMatrix σ i k a b u v = (1 : Matrix (Fin N) (Fin N) K) u v := by
  have hmem : ∀ {x y : Fin N}, x ∈ ({i, k, Fin.rev i} : Set (Fin N)) →
      y ∈ ({i, k, Fin.rev i} : Set (Fin N)) → x = u → y = v → False := by
    rintro x y hx hy rfl rfl
    rcases huv with hu | hv
    · exact hu hx
    · exact hv hy
  have h1 : ¬ (i = u ∧ k = v) := fun hh => hmem (by simp) (by simp) hh.1 hh.2
  have h2 : ¬ (k = u ∧ Fin.rev i = v) := fun hh => hmem (by simp) (by simp) hh.1 hh.2
  have h3 : ¬ (i = u ∧ Fin.rev i = v) := fun hh => hmem (by simp) (by simp) hh.1 hh.2
  rw [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h2, if_neg h3]
  simp

private noncomputable def hypRoot (h : UnitaryFieldData 2 n K) (a b : HypIndex r ε) (c : K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K :=
  1 + single a b c - single (hypPartner b) (hypPartner a) (h.bar c)

private def HasHypRoot (h : UnitaryFieldData 2 n K) (R : Subgroup (hypSU h r ε))
    (a b : HypIndex r ε) : Prop :=
  ∀ c : K, ∃ g ∈ R, (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) = hypRoot h a b c

private theorem submatrix_rootMatrix (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2]
    (hε : ε ≤ 1) (i j : Fin (2 * r + ε)) (c : K) :
    (rootMatrix (unitaryInvolution K 2 n) i j c).submatrix (hypEquivFin r ε)
        (hypEquivFin r ε) =
      hypRoot h ((hypEquivFin r ε).symm i) ((hypEquivFin r ε).symm j) c := by
  ext a b
  simp only [rootMatrix, hypRoot, Matrix.submatrix_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.single_apply, EmbeddingLike.apply_eq_iff_eq,
    ← hypEquivFin_symm_rev hε, Equiv.symm_apply_eq, bar_eq_unitaryInvolution h]

private theorem signedPerm_conj_hypRoot (h : UnitaryFieldData 2 n K)
    {π : Equiv.Perm (HypIndex r ε)} (hπ : ∀ a, π (hypPartner a) = hypPartner (π a))
    (a b : HypIndex r ε) (c : K) :
    signedPerm π (fun _ => (1 : K)) * hypRoot h a b c * (signedPerm π (fun _ => (1 : K)))⁻¹ =
      hypRoot h (π a) (π b) c := by
  ext x y
  rw [signedPerm_conj_apply]
  simp only [hypRoot, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply,
    EmbeddingLike.apply_eq_iff_eq, ← hπ, Equiv.eq_symm_apply, Equiv.apply_symm_apply]

private theorem coe_leviSU_transvection (h : UnitaryFieldData 2 n K) {k l : Fin r} (hkl : k ≠ l)
    (c : K) :
    (((leviSU h ε (Matrix.SpecialLinearGroup.transvection hkl c) : hypSU h r ε) :
      GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      hypRoot h (.inl k) (.inl l) c := by
  have hinv : (((Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hkl c))⁻¹ : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K) = 1 + single k l (-c) := by
    rw [← map_inv, Matrix.SpecialLinearGroup.transvection_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe]
  rw [coe_leviSU, coe_leviGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.transvection_coe, leviDual, hinv]
  ext x y
  rcases x with x | z | x <;> rcases y with y | w | y
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp [hypRoot, Matrix.single_apply, Matrix.one_apply]
  · simp only [blk3_inr_inr_inr_inr, Matrix.transpose_apply, Matrix.map_apply, hypRoot,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply, map_add,
      Sum.inr.injEq, hypPartner_inl]
    by_cases hxy : y = x
    · subst hxy
      by_cases h1 : l = y ∧ k = y
      · exact absurd (h1.1.trans h1.2.symm) (Ne.symm hkl)
      · have h2 : ¬ (k = y ∧ l = y) := fun hh => h1 ⟨hh.2, hh.1⟩
        simp [h1, h2]
    · have hxy' : ¬ x = y := fun hh => hxy hh.symm
      by_cases h1 : l = x ∧ k = y
      · have h2 : k = y ∧ l = x := ⟨h1.2, h1.1⟩
        simp [h1, h2, hxy, hxy']
      · have h2 : ¬ (k = y ∧ l = x) := fun hh => h1 ⟨hh.2, hh.1⟩
        simp [h1, h2, hxy, hxy']

private theorem hasHypRoot_linePerm (h : UnitaryFieldData 2 n K) {R : Subgroup (hypSU h r ε)}
    {m : Fin r} (hW : lineWeyl h ε m ∈ R) {a b : HypIndex r ε} (hab : HasHypRoot h R a b) :
    HasHypRoot h R (linePerm (ε := ε) m a) (linePerm (ε := ε) m b) := by
  intro c
  obtain ⟨g, hg, hgM⟩ := hab c
  refine ⟨lineWeyl h ε m * g * (lineWeyl h ε m)⁻¹,
    R.mul_mem (R.mul_mem hW hg) (R.inv_mem hW), ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
    Matrix.GeneralLinearGroup.coe_inv, coe_lineWeyl, hgM]
  exact signedPerm_conj_hypRoot h (linePerm_hypPartner m) a b c

private theorem lineBlock_le_of_levi (h : UnitaryFieldData 2 n K) {R : Subgroup (hypSU h r ε)}
    (hL : (leviSU h ε).range ≤ R) {m₀ : Fin r} (hm : lineBlock h m₀ ≤ R) (m : Fin r) :
    lineBlock h m ≤ R := by
  intro g hg
  have hg' := hg
  rw [lineBlock, mem_hypBlock] at hg'
  have hw : pairWeyl h ε m₀ m ∈ R :=
    hL (Subgroup.map_le_range _ _ (pairWeyl_mem_pairBlock h m₀ m))
  have hconj : (pairWeyl h ε m₀ m)⁻¹ * g * pairWeyl h ε m₀ m ∈ lineBlock h m₀ := by
    rw [lineBlock, mem_hypBlock, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv, coe_pairWeyl,
      ← pairPerm_symm_image_lineCoords m m₀]
    have := isHypBlockOn_signedPerm_conj hg' (pairPerm (ε := ε) m₀ m).symm
    rwa [signedPerm_one_inv (pairPerm (ε := ε) m₀ m).symm, Equiv.symm_symm,
      ← signedPerm_one_inv (pairPerm (ε := ε) m₀ m)] at this
  have hgeq : g = pairWeyl h ε m₀ m * ((pairWeyl h ε m₀ m)⁻¹ * g * pairWeyl h ε m₀ m) *
      (pairWeyl h ε m₀ m)⁻¹ := by group
  rw [hgeq]
  exact R.mul_mem (R.mul_mem hw (hm hconj)) (R.inv_mem hw)

theorem eq_top_of_levi_lineBlock (h : UnitaryFieldData 2 n K) (hε : ε ≤ 1)
    {R : Subgroup (hypSU h r ε)} (hL : (leviSU h ε).range ≤ R) (m₀ : Fin r)
    (hm : lineBlock h m₀ ≤ R) : R = ⊤ := by
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  have hF : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hall : ∀ m, lineBlock h m ≤ R := lineBlock_le_of_levi h hL hm
  have hW : ∀ m, lineWeyl h ε m ∈ R := fun m => hall m (lineWeyl_mem_lineBlock h m)
  have hbase : ∀ k l : Fin r, k ≠ l → HasHypRoot h R (.inl k) (.inl l) := fun k l hkl c =>
    ⟨leviSU h ε (Matrix.SpecialLinearGroup.transvection hkl c), hL ⟨_, rfl⟩,
      coe_leviSU_transvection h hkl c⟩
  have hfe : ∀ k l : Fin r, k ≠ l → HasHypRoot h R (.inr (.inr k)) (.inl l) := fun k l hkl => by
    have := hasHypRoot_linePerm h (hW k) (hbase k l hkl)
    rwa [linePerm_inl_self, linePerm_inl_of_ne (Ne.symm hkl)] at this
  have hef : ∀ k l : Fin r, k ≠ l → HasHypRoot h R (.inl k) (.inr (.inr l)) := fun k l hkl => by
    have := hasHypRoot_linePerm h (hW l) (hbase k l hkl)
    rwa [linePerm_inl_of_ne hkl, linePerm_inl_self] at this
  have hff : ∀ k l : Fin r, k ≠ l → HasHypRoot h R (.inr (.inr k)) (.inr (.inr l)) :=
    fun k l hkl => by
      have := hasHypRoot_linePerm h (hW k) (hef k l hkl)
      rwa [linePerm_inl_self, linePerm_inr_inr_of_ne (Ne.symm hkl)] at this
  have hroot : ∀ k l : Fin r, k ≠ l → ∀ a b : HypIndex r ε,
      (a = .inl k ∨ a = .inr (.inr k)) → (b = .inl l ∨ b = .inr (.inr l)) →
        HasHypRoot h R a b := by
    rintro k l hkl a b (rfl | rfl) (rfl | rfl)
    · exact hbase k l hkl
    · exact hef k l hkl
    · exact hfe k l hkl
    · exact hff k l hkl
  have hmap : R.map (hypSUEquiv h hε).toMonoidHom = ⊤ := by
    have hn2 : 2 ≤ 2 * r + ε := by have := m₀.isLt; omega
    refine GGOppRadSpU.eq_top_of_root_le hF hn2 _ ?_ ?_ ?_
    · rintro i j hij hi hj hji _ ⟨c, rfl⟩
      rw [Subgroup.mem_map_equiv]
      obtain ⟨k, hk⟩ := exists_line_of_ne_rev hε hi
      obtain ⟨l, hl⟩ := exists_line_of_ne_rev hε hj
      have hkl : k ≠ l := by
        rintro rfl
        have hpart := hypEquivFin_symm_rev (r := r) hε i
        rcases hk with hk | hk <;> rcases hl with hl | hl
        · exact hij ((hypEquivFin r ε).symm.injective (hk.trans hl.symm))
        · exact hji ((hypEquivFin r ε).symm.injective (by rw [hl, hpart, hk, hypPartner_inl]))
        · exact hji ((hypEquivFin r ε).symm.injective (by rw [hl, hpart, hk, hypPartner_inr_inr]))
        · exact hij ((hypEquivFin r ε).symm.injective (hk.trans hl.symm))
      obtain ⟨g, hg, hgM⟩ := hroot k l hkl _ _ hk hl (Multiplicative.toAdd c)
      have hgeq : (hypSUEquiv h hε).symm (rootHom (unitaryInvolution K 2 n)
          (unitaryInvolution_involutive hF) hij hi hj c) = g := by
        refine Subtype.ext (Units.ext ?_)
        rw [coe_hypSUEquiv_symm_matrix, coe_rootHom, submatrix_rootMatrix h hε, hgM]
      rw [hgeq]
      exact hg
    · rintro i hi _ ⟨c, rfl⟩
      rw [Subgroup.mem_map_equiv]
      obtain ⟨k, hk⟩ := exists_line_of_ne_rev hε hi
      refine hall k (symm_mem_lineBlock h hε (T := {i, Fin.rev i})
        (fun a ha => mem_lineCoords_of_eq hε hk ha) fun u v huv => ?_)
      rw [coe_longRootHom]
      exact longRootMatrix_apply_of_not_mem _ huv
    · rintro i k' hi hik hk' g ⟨a, b, -, hg⟩
      rw [Subgroup.mem_map_equiv]
      obtain ⟨k, hk⟩ := exists_line_of_ne_rev hε hi
      obtain ⟨z, hz⟩ := exists_eq_inr_inl_of_rev_eq hε hk'
      refine hall k (symm_mem_lineBlock h hε (T := {i, k', Fin.rev i}) (fun x hx => ?_)
        fun u v huv => ?_)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx | hx
        · exact mem_lineCoords_of_eq hε hk (Or.inl hx)
        · have hxz : x = .inr (.inl z) := by
            rw [← hz]
            exact (Equiv.eq_symm_apply _).mpr hx
          rw [hxz]
          exact inr_inl_mem_lineCoords k z
        · exact mem_lineCoords_of_eq hε hk (Or.inr hx)
      · rw [hg]
        exact heisenbergMatrix_apply_of_not_mem _ a b huv
  rw [eq_top_iff]
  intro g _
  have hg : hypSUEquiv h hε g ∈ R.map (hypSUEquiv h hε).toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_top _
  rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hg

private theorem iSup_pairBlock_eq_range (h : UnitaryFieldData 2 n K)
    {s : Fin r → Fin r → Prop}
    (hgen : (⨆ (i : Fin r) (j : Fin r) (_ : s i j),
      coordBlockSL K ({i, j} : Finset (Fin r))) = ⊤) :
    (⨆ (i : Fin r) (j : Fin r) (_ : s i j), pairBlock h ε i j) = (leviSU h ε).range := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun j => iSup_le fun _ => Subgroup.map_le_range ..
  · have hmap : (⨆ (i : Fin r) (j : Fin r) (_ : s i j), pairBlock h ε i j) =
        (⨆ (i : Fin r) (j : Fin r) (_ : s i j),
          coordBlockSL K ({i, j} : Finset (Fin r))).map (leviSU h ε) := by
      simp only [pairBlock, Subgroup.map_iSup]
    rw [hmap, hgen, MonoidHom.range_eq_map]

theorem iSup_blocks_avoid_pair_eq_top (h : UnitaryFieldData 2 n K) (hε : ε ≤ 1) (hr : 3 ≤ r)
    (i₀ j₀ : Fin r) :
    (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j ∧ ({i, j} : Finset (Fin r)) ≠ {i₀, j₀}),
      pairBlock h ε i j) ⊔ (⨆ m : Fin r, lineBlock h m) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  have hpair := iSup_pairBlock_eq_range (ε := ε) h
    (s := fun i j => i ≠ j ∧ ({i, j} : Finset (Fin r)) ≠ {i₀, j₀})
    (TypeA.iSup_coordBlockSL_pairs (K := K) (d := r) hr i₀ j₀)
  refine eq_top_of_levi_lineBlock h hε ?_ ⟨0, by omega⟩ ?_
  · rw [← hpair]; exact le_sup_left
  · exact le_sup_of_le_right (le_iSup (fun m => lineBlock h m) _)

theorem iSup_blocks_avoid_line_eq_top (h : UnitaryFieldData 2 n K) (hε : ε ≤ 1) (hr : 3 ≤ r)
    (m₀ : Fin r) :
    (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j), pairBlock h ε i j) ⊔
      (⨆ (m : Fin r) (_ : m ≠ m₀), lineBlock h m) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : Fin r, m₁ ≠ m₀ :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) m₀
  have hpair_avoid := iSup_pairBlock_eq_range (ε := ε) h
    (s := fun i j => i ≠ j ∧ ({i, j} : Finset (Fin r)) ≠ {m₀, m₁})
    (TypeA.iSup_coordBlockSL_pairs (K := K) (d := r) hr m₀ m₁)
  have hle : (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j ∧
      ({i, j} : Finset (Fin r)) ≠ {m₀, m₁}), pairBlock h ε i j) ≤
      (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j), pairBlock h ε i j) :=
    iSup_le fun i => iSup_le fun j => iSup_le fun hs =>
      le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hs.1 le_rfl))
  have hpair : (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j), pairBlock h ε i j) =
      (leviSU h ε).range := by
    apply le_antisymm
    · exact iSup_le fun i => iSup_le fun j => iSup_le fun _ => Subgroup.map_le_range ..
    · rw [← hpair_avoid]; exact hle
  refine eq_top_of_levi_lineBlock h hε ?_ m₁ ?_
  · rw [← hpair]; exact le_sup_left
  · exact le_sup_of_le_right
      (le_iSup_of_le m₁ (le_iSup_of_le hm₁ le_rfl))

end CFSG.StandardType.SuSplitRootGen

end

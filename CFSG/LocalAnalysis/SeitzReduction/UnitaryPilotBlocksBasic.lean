module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockMatrix
  blockMatrix_apply blockMatrix_one blockMatrix_mul blockEmbed coe_blockEmbed
  blockEmbed_injective range_blockEmbed reindexSpecialLinear)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

variable (n) in
@[expose] def toSL : unitarySU p f K n →* SpecialLinearGroup (Fin n) K where
  toFun A := ⟨((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ((mem_unitarySU_iff h).1 A.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[simp]
theorem coe_toSL (A : unitarySU p f K n) :
    ((toSL h n A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
  rfl

theorem toSL_injective : Function.Injective (toSL h n) := fun _ _ hAB =>
  Subtype.ext (Units.ext (congrArg Subtype.val hAB))

theorem unitary_toSL (A : unitarySU p f K n) :
    (((toSL h n A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((toSL h n A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  ((mem_unitarySU_iff h).1 A.2).2

@[expose] def ofSL (B : SpecialLinearGroup (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1) :
    unitarySU p f K n :=
  ⟨SpecialLinearGroup.toGL B, (mem_unitarySU_iff h).2 ⟨B.2, hB⟩⟩

@[simp]
theorem coe_ofSL (B : SpecialLinearGroup (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1) :
    (((ofSL h B hB : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = B :=
  rfl

@[simp]
theorem toSL_ofSL (B : SpecialLinearGroup (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1) :
    toSL h n (ofSL h B hB) = B :=
  rfl

theorem mem_range_toSL_iff {B : SpecialLinearGroup (Fin n) K} :
    B ∈ (toSL h n).range ↔
      ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1 := by
  constructor
  · rintro ⟨A, rfl⟩
    exact unitary_toSL h A
  · intro hB
    exact ⟨ofSL h B hB, rfl⟩

@[expose] def unitaryBlock (I : Finset (Fin n)) : Subgroup (unitarySU p f K n) :=
  (blockSpecialLinear I).comap (toSL h n)

theorem mem_unitaryBlock {I : Finset (Fin n)} {A : unitarySU p f K n} :
    A ∈ unitaryBlock h I ↔ ∀ i j, (i ∉ I ∨ j ∉ I) →
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j :=
  Iff.rfl

theorem mem_unitaryBlock_iff_toSL {I : Finset (Fin n)} {A : unitarySU p f K n} :
    A ∈ unitaryBlock h I ↔ toSL h n A ∈ blockSpecialLinear I :=
  Iff.rfl

theorem unitaryBlock_mono {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    unitaryBlock h I ≤ unitaryBlock h J :=
  Subgroup.comap_mono (LinearPilot.blockSpecialLinear_mono hIJ)

@[simp]
theorem unitaryBlock_empty : unitaryBlock h (∅ : Finset (Fin n)) = ⊥ := by
  rw [unitaryBlock, LinearPilot.blockSpecialLinear_empty]
  exact (MonoidHom.ker_eq_bot_iff _).2 (toSL_injective h)

@[simp]
theorem unitaryBlock_univ : unitaryBlock h (Finset.univ : Finset (Fin n)) = ⊤ := by
  rw [unitaryBlock, LinearPilot.blockSpecialLinear_univ, Subgroup.comap_top]

section BlockMatrix

theorem blockMatrix_map (I : Finset (Fin n)) (φ : K →+* K) (A : Matrix I I K) :
    (blockMatrix I A).map φ = blockMatrix I (A.map φ) := by
  ext i j
  rw [Matrix.map_apply, blockMatrix_apply, blockMatrix_apply]
  split_ifs with hij
  · rfl
  · rw [one_apply]
    split_ifs <;> simp

theorem blockMatrix_transpose (I : Finset (Fin n)) (A : Matrix I I K) :
    (blockMatrix I A)ᵀ = blockMatrix I Aᵀ := by
  ext i j
  rw [transpose_apply, blockMatrix_apply, blockMatrix_apply]
  by_cases hij : i ∈ I ∧ j ∈ I
  · rw [dite_eq_left ⟨hij.2, hij.1⟩, dite_eq_left hij, transpose_apply]
  · rw [dite_eq_right (fun h' => hij ⟨h'.2, h'.1⟩), dite_eq_right hij]
    by_cases e : i = j
    · subst e
      rfl
    · rw [one_apply_ne e, one_apply_ne (Ne.symm e)]

theorem blockMatrix_injective (I : Finset (Fin n)) :
    Function.Injective (blockMatrix (K := K) I) := by
  intro A B hAB
  ext a b
  have := congrFun (congrFun hAB a) b
  rwa [blockMatrix_apply, blockMatrix_apply, dite_eq_left ⟨a.2, b.2⟩,
    dite_eq_left ⟨a.2, b.2⟩] at this

end BlockMatrix

theorem blockMatrix_unitary (I : Finset (Fin n)) {A : Matrix I I K}
    (hA : (A.map h.bar)ᵀ * A = 1) :
    ((blockMatrix I A).map h.bar)ᵀ * blockMatrix I A = 1 := by
  rw [blockMatrix_map, blockMatrix_transpose, ← blockMatrix_mul, hA, blockMatrix_one]

theorem unitary_of_blockMatrix_unitary (I : Finset (Fin n)) {A : Matrix I I K}
    (hA : ((blockMatrix I A).map h.bar)ᵀ * blockMatrix I A = 1) : (A.map h.bar)ᵀ * A = 1 := by
  rw [blockMatrix_map, blockMatrix_transpose, ← blockMatrix_mul,
    ← blockMatrix_one (K := K) I] at hA
  exact blockMatrix_injective I hA

theorem reindex_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) {X : Matrix ι ι K} (hX : (X.map h.bar)ᵀ * X = 1) :
    ((reindex e e X).map h.bar)ᵀ * reindex e e X = 1 := by
  rw [reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv, hX,
    submatrix_one_equiv]

theorem unitary_of_reindex_unitary {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) {X : Matrix ι ι K}
    (hX : ((reindex e e X).map h.bar)ᵀ * reindex e e X = 1) : (X.map h.bar)ᵀ * X = 1 := by
  have h1 := reindex_unitary h e.symm hX
  rwa [← reindex_symm, Equiv.symm_apply_apply] at h1

@[expose] noncomputable def unitaryBlockEmbed (I : Finset (Fin n)) :
    unitarySU p f K I.card →* unitarySU p f K n :=
  (SpecialLinearGroup.toGL.comp ((blockEmbed I).comp
      ((reindexSpecialLinear I.equivFin.symm).toMonoidHom.comp (toSL h I.card)))).codRestrict
    (unitarySU p f K n) fun X => (mem_unitarySU_iff h).2
      ⟨((blockEmbed I) ((reindexSpecialLinear I.equivFin.symm) (toSL h I.card X))).2,
        blockMatrix_unitary h I (reindex_unitary h I.equivFin.symm (unitary_toSL h X))⟩

theorem coe_unitaryBlockEmbed (I : Finset (Fin n)) (X : unitarySU p f K I.card) :
    (((unitaryBlockEmbed h I X : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockMatrix I (reindex I.equivFin.symm I.equivFin.symm
        ((X : GL (Fin I.card) K) : Matrix (Fin I.card) (Fin I.card) K)) :=
  rfl

theorem toSL_unitaryBlockEmbed (I : Finset (Fin n)) (X : unitarySU p f K I.card) :
    toSL h n (unitaryBlockEmbed h I X) =
      blockEmbed I (reindexSpecialLinear I.equivFin.symm (toSL h I.card X)) :=
  rfl

theorem unitaryBlockEmbed_injective (I : Finset (Fin n)) :
    Function.Injective (unitaryBlockEmbed h I) := by
  intro X Y hXY
  have h1 := congrArg (toSL h n) hXY
  rw [toSL_unitaryBlockEmbed, toSL_unitaryBlockEmbed] at h1
  exact toSL_injective h ((reindexSpecialLinear _).injective (blockEmbed_injective I h1))

theorem range_unitaryBlockEmbed (I : Finset (Fin n)) :
    (unitaryBlockEmbed h I).range = unitaryBlock h I := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_unitaryBlock_iff_toSL, toSL_unitaryBlockEmbed, ← range_blockEmbed]
    exact ⟨_, rfl⟩
  · intro A hA
    rw [mem_unitaryBlock_iff_toSL, ← range_blockEmbed] at hA
    obtain ⟨B, hB⟩ := hA
    have hBu : ((B : Matrix I I K).map h.bar)ᵀ * (B : Matrix I I K) = 1 := by
      have hA' := unitary_toSL h A
      rw [← hB, coe_blockEmbed] at hA'
      exact unitary_of_blockMatrix_unitary h I hA'
    set X₀ := (reindexSpecialLinear I.equivFin.symm).symm B with hX₀
    have hX₀u : ((X₀ : Matrix (Fin I.card) (Fin I.card) K).map h.bar)ᵀ *
        (X₀ : Matrix (Fin I.card) (Fin I.card) K) = 1 :=
      reindex_unitary h I.equivFin.symm.symm hBu
    refine ⟨ofSL h X₀ hX₀u, toSL_injective h ?_⟩
    rw [toSL_unitaryBlockEmbed, toSL_ofSL, hX₀, MulEquiv.apply_symm_apply, hB]

@[expose] noncomputable def unitaryBlockEquiv (I : Finset (Fin n)) :
    unitarySU p f K I.card ≃* unitaryBlock h I :=
  (MonoidHom.ofInjective (unitaryBlockEmbed_injective h I)).trans
    (MulEquiv.subgroupCongr (range_unitaryBlockEmbed h I))

@[simp]
theorem coe_unitaryBlockEquiv (I : Finset (Fin n)) (X : unitarySU p f K I.card) :
    ((unitaryBlockEquiv h I X : unitaryBlock h I) : unitarySU p f K n) =
      unitaryBlockEmbed h I X :=
  rfl

theorem eq_one_of_mem_unitaryBlock_of_unitaryProj_eq_one {I : Finset (Fin n)} (hI : I.card < n)
    {A : unitarySU p f K n} (hA : A ∈ unitaryBlock h I) (h1 : unitaryProj h n A = 1) : A = 1 := by
  have hker : A ∈ (unitaryProj h n).ker := h1
  rw [ker_unitaryProj, mem_unitaryScalars] at hker
  obtain ⟨c, -, -, hc⟩ := hker
  obtain ⟨j, -, hj⟩ : ∃ j, j ∈ (Finset.univ : Finset (Fin n)) ∧ j ∉ I :=
    Finset.exists_mem_notMem_of_card_lt_card (by simpa using hI)
  have hjj : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j =
      (1 : Matrix (Fin n) (Fin n) K) j j := hA j j (Or.inl hj)
  rw [hc, GeneralLinearGroup.coe_scalar, one_apply_eq] at hjj
  have hc1 : c = 1 := Units.ext (by simpa using hjj)
  exact Subtype.ext (by rw [hc, hc1, map_one, Subgroup.coe_one])

theorem unitaryProj_comp_unitaryBlockEmbed_injective {I : Finset (Fin n)} (hI : I.card < n) :
    Function.Injective ((unitaryProj h n).comp (unitaryBlockEmbed h I)) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have hmem : unitaryBlockEmbed h I X ∈ unitaryBlock h I := by
    rw [← range_unitaryBlockEmbed h I]
    exact ⟨X, rfl⟩
  have h1 := eq_one_of_mem_unitaryBlock_of_unitaryProj_eq_one h hI hmem hX
  exact unitaryBlockEmbed_injective h I (by rw [h1, map_one])

theorem commute_unitaryBlock_of_disjoint {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    {A B : unitarySU p f K n} (hA : A ∈ unitaryBlock h I) (hB : B ∈ unitaryBlock h J) :
    Commute A B :=
  toSL_injective h (by
    rw [map_mul, map_mul]
    exact (LinearPilot.commute_blockSpecialLinear_of_disjoint hIJ hA hB).eq)

@[expose] def blockSU (I : Finset (Fin n)) : Subgroup (unitaryPSU h n) :=
  (unitaryBlock h I).map (unitaryProj h n)

@[expose] def rootSU2 (a b : Fin n) : Subgroup (unitaryPSU h n) :=
  blockSU h {a, b}

theorem mem_blockSU {I : Finset (Fin n)} {x : unitaryPSU h n} :
    x ∈ blockSU h I ↔ ∃ A ∈ unitaryBlock h I, unitaryProj h n A = x :=
  Subgroup.mem_map

theorem unitaryProj_mem_blockSU {I : Finset (Fin n)} {A : unitarySU p f K n}
    (hA : A ∈ unitaryBlock h I) : unitaryProj h n A ∈ blockSU h I :=
  Subgroup.mem_map_of_mem _ hA

theorem rootSU2_eq (a b : Fin n) : rootSU2 h a b = blockSU h {a, b} :=
  rfl

theorem blockSU_eq_range (I : Finset (Fin n)) :
    blockSU h I = ((unitaryProj h n).comp (unitaryBlockEmbed h I)).range := by
  rw [MonoidHom.range_comp, range_unitaryBlockEmbed, blockSU]

theorem blockSU_mono {I J : Finset (Fin n)} (hIJ : I ⊆ J) : blockSU h I ≤ blockSU h J :=
  Subgroup.map_mono (unitaryBlock_mono h hIJ)

@[simp]
theorem blockSU_empty : blockSU h (∅ : Finset (Fin n)) = ⊥ := by
  rw [blockSU, unitaryBlock_empty, Subgroup.map_bot]

@[simp]
theorem blockSU_univ : blockSU h (Finset.univ : Finset (Fin n)) = ⊤ := by
  rw [blockSU, unitaryBlock_univ, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 (unitaryProj_surjective h n)]

theorem rootSU2_comm (a b : Fin n) : rootSU2 h a b = rootSU2 h b a := by
  rw [rootSU2, rootSU2, Finset.pair_comm]

theorem rootSU2_le_blockSU {I : Finset (Fin n)} {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) :
    rootSU2 h a b ≤ blockSU h I :=
  blockSU_mono h (Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb))

@[expose] noncomputable def blockSUEquiv {I : Finset (Fin n)} (hI : I.card < n) :
    unitarySU p f K I.card ≃* blockSU h I :=
  (MonoidHom.ofInjective (unitaryProj_comp_unitaryBlockEmbed_injective h hI)).trans
    (MulEquiv.subgroupCongr (blockSU_eq_range h I).symm)

@[simp]
theorem coe_blockSUEquiv {I : Finset (Fin n)} (hI : I.card < n) (X : unitarySU p f K I.card) :
    ((blockSUEquiv h hI X : blockSU h I) : unitaryPSU h n) =
      unitaryProj h n (unitaryBlockEmbed h I X) :=
  rfl

theorem blockSU_mulEquiv (I : Finset (Fin n)) (hI : I.card < n) :
    Nonempty (blockSU h I ≃* unitarySU p f K I.card) :=
  ⟨(blockSUEquiv h hI).symm⟩

theorem rootSU2_mulEquiv {a b : Fin n} (hab : a ≠ b) (hn : 3 ≤ n) :
    Nonempty (rootSU2 h a b ≃* unitarySU p f K 2) := by
  have hcard : ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair hab
  obtain ⟨e⟩ := blockSU_mulEquiv h {a, b} (by omega)
  rw [hcard] at e
  exact ⟨e⟩

theorem commute_blockSU_of_disjoint {I J : Finset (Fin n)} (hIJ : Disjoint I J) :
    ∀ x ∈ blockSU h I, ∀ y ∈ blockSU h J, x * y = y * x := by
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  rw [← map_mul, ← map_mul, (commute_unitaryBlock_of_disjoint h hIJ hA hB).eq]

@[expose] noncomputable def pairEmbedSU {a b : Fin n} (hab : a ≠ b) :
    unitarySU p f K 2 →* unitarySU p f K n :=
  (SpecialLinearGroup.toGL.comp ((LinearPilot.pairEmbed hab).comp (toSL h 2))).codRestrict
    (unitarySU p f K n) fun X => (mem_unitarySU_iff h).2
      ⟨((LinearPilot.pairEmbed hab) (toSL h 2 X)).2,
        blockMatrix_unitary h {a, b} (reindex_unitary h _ (unitary_toSL h X))⟩

theorem toSL_pairEmbedSU {a b : Fin n} (hab : a ≠ b) (X : unitarySU p f K 2) :
    toSL h n (pairEmbedSU h hab X) = LinearPilot.pairEmbed hab (toSL h 2 X) :=
  rfl

theorem coe_pairEmbedSU {a b : Fin n} (hab : a ≠ b) (X : unitarySU p f K 2) :
    (((pairEmbedSU h hab X : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((LinearPilot.pairEmbed hab (toSL h 2 X) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) :=
  rfl

theorem pairEmbedSU_injective {a b : Fin n} (hab : a ≠ b) :
    Function.Injective (pairEmbedSU h hab) := by
  intro X Y hXY
  have h1 := congrArg (toSL h n) hXY
  rw [toSL_pairEmbedSU, toSL_pairEmbedSU] at h1
  exact toSL_injective h (LinearPilot.pairEmbed_injective hab h1)

theorem range_pairEmbedSU {a b : Fin n} (hab : a ≠ b) :
    (pairEmbedSU h hab).range = unitaryBlock h {a, b} := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [mem_unitaryBlock_iff_toSL, toSL_pairEmbedSU, ← LinearPilot.range_pairEmbed hab]
    exact ⟨_, rfl⟩
  · intro A hA
    rw [mem_unitaryBlock_iff_toSL, ← LinearPilot.range_pairEmbed hab] at hA
    obtain ⟨B, hB⟩ := hA
    have hBu : ((B : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
        (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
      have hA' := unitary_toSL h A
      rw [← hB] at hA'
      exact unitary_of_reindex_unitary h _ (unitary_of_blockMatrix_unitary h {a, b} hA')
    exact ⟨ofSL h B hBu, toSL_injective h (by rw [toSL_pairEmbedSU, toSL_ofSL, hB])⟩

theorem rootSU2_eq_range_pairEmbedSU {a b : Fin n} (hab : a ≠ b) :
    rootSU2 h a b = ((unitaryProj h n).comp (pairEmbedSU h hab)).range := by
  rw [MonoidHom.range_comp, range_pairEmbedSU, rootSU2, blockSU]

theorem unitaryProj_pairEmbedSU_mem_rootSU2 {a b : Fin n} (hab : a ≠ b)
    (X : unitarySU p f K 2) : unitaryProj h n (pairEmbedSU h hab X) ∈ rootSU2 h a b := by
  rw [rootSU2_eq_range_pairEmbedSU h hab]
  exact ⟨X, rfl⟩

theorem unitaryProj_comp_pairEmbedSU_injective {a b : Fin n} (hab : a ≠ b) (hn : 3 ≤ n) :
    Function.Injective ((unitaryProj h n).comp (pairEmbedSU h hab)) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have hmem : pairEmbedSU h hab X ∈ unitaryBlock h {a, b} := by
    rw [← range_pairEmbedSU h hab]
    exact ⟨X, rfl⟩
  have h1 := eq_one_of_mem_unitaryBlock_of_unitaryProj_eq_one h
    (by rw [Finset.card_pair hab]; omega) hmem hX
  exact pairEmbedSU_injective h hab (by rw [h1, map_one])

end CFSG.SeitzReduction.UnitaryPilot

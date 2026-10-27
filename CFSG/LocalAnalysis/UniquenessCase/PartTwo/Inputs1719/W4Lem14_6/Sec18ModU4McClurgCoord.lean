module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4OuterClsAct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
open CFSG.SeitzReduction.F4Pilot (omIsoGroup statedOmega_le_omIsoGroup)
open scoped Matrix

@[expose] def adjIdx : Fin 14 → Om6Idx × Om6Idx :=
  ![(.inl 0, .inl 1), (.inl 0, .inr (.inl 1)), (.inl 0, .inr (.inr 0)), (.inl 0, .inr (.inr 1)),
    (.inl 1, .inr (.inl 0)), (.inl 1, .inr (.inl 1)), (.inl 1, .inr (.inr 0)),
    (.inl 1, .inr (.inr 1)), (.inr (.inl 0), .inr (.inl 1)), (.inr (.inl 0), .inr (.inr 0)),
    (.inr (.inl 0), .inr (.inr 1)), (.inr (.inl 1), .inr (.inr 0)),
    (.inr (.inl 1), .inr (.inr 1)), (.inr (.inr 0), .inr (.inr 1))]

@[expose] def adjCoord {F : Type} (X : Matrix Om6Idx Om6Idx F) : Fin 14 → F :=
  fun j => X (adjIdx j).1 (adjIdx j).2

@[expose] def adjOfCoord (F : Type) [Field F] (b : F) (v : Fin 14 → F) :
    Matrix Om6Idx Om6Idx F :=
  ∑ j, v j • wedgeM (Pi.single (adjIdx j).1 (1 : F)) (Pi.single (adjIdx j).2 1) -
    (v 5 + b * v 13) • wedgeM (Pi.single (Sum.inl 0 : Om6Idx) (1 : F))
      (Pi.single (Sum.inr (Sum.inl 0)) 1)

private lemma adjIdx_injective : Function.Injective adjIdx := by decide

private lemma adjIdx_ne_swap : ∀ i j : Fin 14, adjIdx i ≠ (adjIdx j).swap := by decide

private lemma adjIdx_fst_ne_snd : ∀ j : Fin 14, (adjIdx j).1 ≠ (adjIdx j).2 := by decide

private lemma adjIdx_ne_excl : ∀ j : Fin 14,
    adjIdx j ≠ (Sum.inl 0, Sum.inr (Sum.inl 0)) ∧
      adjIdx j ≠ (Sum.inr (Sum.inl 0), Sum.inl 0) := by decide

private lemma adjIdx_cover (c d : Om6Idx) (hcd : c ≠ d) :
    (∃ j, adjIdx j = (c, d)) ∨ (∃ j, adjIdx j = (d, c)) ∨
      (c = Sum.inl 0 ∧ d = Sum.inr (Sum.inl 0)) ∨
      (c = Sum.inr (Sum.inl 0) ∧ d = Sum.inl 0) := by
  revert c d
  decide

private lemma wedgeM_transpose_coord {F : Type} [Field F] (v w : Om6Idx → F) :
    (wedgeM v w)ᵀ = wedgeM v w := by
  simp only [wedgeM, Matrix.transpose_add, Matrix.transpose_vecMulVec]
  rw [add_comm]

private lemma wedgeM_single_apply {F : Type} [Field F] (a b c d : Om6Idx) :
    wedgeM (Pi.single a (1 : F)) (Pi.single b 1) c d =
      (if c = a ∧ d = b then (1 : F) else 0) +
        (if c = b ∧ d = a then 1 else 0) := by
  simp only [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

private lemma wedgeM_single_diag {F : Type} [Field F] {a b : Om6Idx} (h : a ≠ b)
    (i : Om6Idx) : wedgeM (Pi.single a (1 : F)) (Pi.single b 1) i i = 0 := by
  rcases eq_or_ne i a with rfl | hia
  · simp [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne h]
  · rcases eq_or_ne i b with rfl | hib
    · simp [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply,
        Pi.single_eq_of_ne (Ne.symm h)]
    · simp [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_eq_of_ne hia,
        Pi.single_eq_of_ne hib]

private lemma inner_sum_inl {F : Type} [Field F] (j : Fin 14) :
    (∑ i : Fin 2, wedgeM (Pi.single (adjIdx j).1 (1 : F)) (Pi.single (adjIdx j).2 1)
        (Sum.inl i) (Sum.inr (Sum.inl i))) = if j = 5 then (1 : F) else 0 := by
  fin_cases j <;> simp [adjIdx, wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply,
    Fin.sum_univ_two]

private lemma inner_sum_b {F : Type} [Field F] (j : Fin 14) :
    wedgeM (Pi.single (adjIdx j).1 (1 : F)) (Pi.single (adjIdx j).2 1)
        (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) = if j = 13 then (1 : F) else 0 := by
  fin_cases j <;> simp [adjIdx, wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]

private lemma adjOfCoord_functional (F : Type) [Field F] (b : F) (v : Fin 14 → F) :
    (∑ i : Fin 2, adjOfCoord F b v (Sum.inl i) (Sum.inr (Sum.inl i)))
      + b * adjOfCoord F b v (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) = 0 := by
  simp only [adjOfCoord, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ x : Fin 2, ∑ j : Fin 14, v j *
      wedgeM (Pi.single (adjIdx j).1 (1 : F)) (Pi.single (adjIdx j).2 1)
        (Sum.inl x) (Sum.inr (Sum.inl x))) = v 5 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_eq_single 5]
    · simp [adjIdx, wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply,
        Fin.sum_univ_two]
    · intro j _ hj
      simp [inner_sum_inl j, hj]
    · intro h5
      simp at h5
  have h2 : (∑ x : Fin 2, wedgeM (Pi.single (Sum.inl 0 : Om6Idx) (1 : F))
      (Pi.single (Sum.inr (Sum.inl 0)) 1) (Sum.inl x) (Sum.inr (Sum.inl x))) = 1 := by
    rw [Fin.sum_univ_two]
    simp [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  have h3 : (∑ j : Fin 14, v j * wedgeM (Pi.single (adjIdx j).1 (1 : F))
      (Pi.single (adjIdx j).2 1) (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1))) = v 13 := by
    rw [Finset.sum_eq_single 13]
    · simp [adjIdx, wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
    · intro j _ hj
      simp [inner_sum_b j, hj]
    · intro h13
      simp at h13
  have h4 : wedgeM (Pi.single (Sum.inl 0 : Om6Idx) (1 : F))
      (Pi.single (Sum.inr (Sum.inl 0)) 1) (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) = 0 := by
    simp [wedgeM, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.single_apply]
  rw [h1]
  rw [← Finset.mul_sum, h2]
  rw [h3, h4]
  ring

theorem adjOfCoord_mem (F : Type) [Field F] (b : F) (v : Fin 14 → F) :
    adjOfCoord F b v ∈ adjOmega6 F b := by
  have h0 : ∀ i : Fin 14, (adjIdx i).1 ≠ (adjIdx i).2 := adjIdx_fst_ne_snd
  have h1 : (Sum.inl 0 : Om6Idx) ≠ Sum.inr (Sum.inl 0) := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [adjOfCoord, Matrix.transpose_sub, Matrix.transpose_sum, Matrix.transpose_smul,
      wedgeM_transpose_coord]
  · intro i
    simp only [adjOfCoord, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero (fun j _ => by rw [wedgeM_single_diag (h0 j), mul_zero])]
    rw [wedgeM_single_diag h1]
    simp
  · simpa using adjOfCoord_functional F b v

theorem adjCoord_adjOfCoord (F : Type) [Field F] (b : F) (v : Fin 14 → F) :
    adjCoord (adjOfCoord F b v) = v := by
  funext j
  have hterm : ∀ x : Fin 14, v x * wedgeM (Pi.single (adjIdx x).1 (1 : F))
      (Pi.single (adjIdx x).2 1) (adjIdx j).1 (adjIdx j).2 =
        if x = j then v j else 0 := by
    intro x
    rw [wedgeM_single_apply]
    by_cases hxj : x = j
    · subst x
      have hdist : (adjIdx j).1 ≠ (adjIdx j).2 := adjIdx_fst_ne_snd j
      simp [hdist, Ne.symm hdist]
    · have h1 : ¬ ((adjIdx j).1 = (adjIdx x).1 ∧ (adjIdx j).2 = (adjIdx x).2) := by
        rintro ⟨e1, e2⟩
        exact hxj (adjIdx_injective (Prod.ext e1 e2).symm)
      have h2 : ¬ ((adjIdx j).1 = (adjIdx x).2 ∧ (adjIdx j).2 = (adjIdx x).1) := by
        rintro ⟨e1, e2⟩
        exact adjIdx_ne_swap x j (Prod.ext e2 e1).symm
      simp [h1, h2, hxj]
  have hcorr : wedgeM (Pi.single (Sum.inl 0 : Om6Idx) (1 : F))
      (Pi.single (Sum.inr (Sum.inl 0)) 1) (adjIdx j).1 (adjIdx j).2 = 0 := by
    rw [wedgeM_single_apply]
    have h1 : ¬ ((adjIdx j).1 = Sum.inl 0 ∧ (adjIdx j).2 = Sum.inr (Sum.inl 0)) :=
      fun h => (adjIdx_ne_excl j).1 (Prod.ext h.1 h.2)
    have h2 : ¬ ((adjIdx j).1 = Sum.inr (Sum.inl 0) ∧ (adjIdx j).2 = Sum.inl 0) :=
      fun h => (adjIdx_ne_excl j).2 (Prod.ext h.1 h.2)
    simp [h1, h2]
  have hsum : (∑ x : Fin 14, v x * wedgeM (Pi.single (adjIdx x).1 (1 : F))
      (Pi.single (adjIdx x).2 1) (adjIdx j).1 (adjIdx j).2) = v j := by
    rw [Finset.sum_congr rfl fun x _ => hterm x]
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  simp only [adjCoord, adjOfCoord, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [hsum, hcorr, mul_zero, sub_zero]

theorem adjOfCoord_adjCoord {F : Type} [Field F] {b : F} {X : Matrix Om6Idx Om6Idx F}
    (hX : X ∈ adjOmega6 F b) : adjOfCoord F b (adjCoord X) = X := by
  let Y := adjOfCoord F b (adjCoord X)
  have hY : Y ∈ adjOmega6 F b := adjOfCoord_mem F b _
  have hYX : adjCoord Y = adjCoord X := adjCoord_adjOfCoord F b _
  let Z := X - Y
  have hZ : Z ∈ adjOmega6 F b := (adjOmega6 F b).sub_mem hX hY
  have hZc : adjCoord Z = 0 := by
    funext j
    change adjCoord Z j = 0
    have h := congrFun hYX j
    simp only [Z, Matrix.sub_apply, adjCoord] at h ⊢
    rw [h, sub_self]
  have hsym : ∀ a b : Om6Idx, Z a b = Z b a := by
    intro a b
    have h := congrFun (congrFun hZ.1 b) a
    simpa using h
  have hZ0 : Z = 0 := by
    ext c d
    by_cases hcd : c = d
    · subst c
      simpa using hZ.2.1 d
    · have hf : Z (Sum.inl 0) (Sum.inr (Sum.inl 0)) = 0 := by
        have h := hZ.2.2
        rw [Fin.sum_univ_two] at h
        have h5 : Z (Sum.inl 1) (Sum.inr (Sum.inl 1)) = 0 := by
          have hp : adjIdx 5 = (Sum.inl 1, Sum.inr (Sum.inl 1)) := by decide
          simpa [adjCoord, hp] using congrFun hZc 5
        have h13 : Z (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) = 0 := by
          have hp : adjIdx 13 = (Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)) := by decide
          simpa [adjCoord, hp] using congrFun hZc 13
        rw [h5, h13, mul_zero, add_zero, add_zero] at h
        exact h
      rcases adjIdx_cover c d hcd with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hc : c = (adjIdx j).1 := (congrArg Prod.fst hj).symm
        have hd : d = (adjIdx j).2 := (congrArg Prod.snd hj).symm
        rw [hc, hd]
        exact congrFun hZc j
      · calc Z c d = Z d c := hsym c d
          _ = 0 := by
            have hc : c = (adjIdx j).2 := (congrArg Prod.snd hj).symm
            have hd : d = (adjIdx j).1 := (congrArg Prod.fst hj).symm
            rw [hd, hc]
            exact congrFun hZc j
      · rw [h1, h2]
        exact hf
      · calc Z c d = Z d c := hsym c d
          _ = 0 := by
            rw [h1, h2]
            exact hf
  exact (sub_eq_zero.mp hZ0).symm

@[expose] def adjCoordEquiv (F : Type) [Field F] (b : F) : ↥(adjOmega6 F b) ≃+ (Fin 14 → F) where
  toFun X := adjCoord (X : Matrix Om6Idx Om6Idx F)
  invFun v := ⟨adjOfCoord F b v, adjOfCoord_mem F b v⟩
  left_inv X := Subtype.ext (adjOfCoord_adjCoord X.2)
  right_inv v := adjCoord_adjOfCoord F b v
  map_add' X Y := rfl

private lemma adjOfCoord_zero (F : Type) [Field F] (b : F) : adjOfCoord F b 0 = 0 :=
  congrArg Subtype.val ((adjCoordEquiv F b).symm.map_zero)

private lemma adjOfCoord_add (F : Type) [Field F] (b : F) (v w : Fin 14 → F) :
    adjOfCoord F b (v + w) = adjOfCoord F b v + adjOfCoord F b w :=
  congrArg Subtype.val ((adjCoordEquiv F b).symm.map_add v w)

private lemma adjOfCoord_smul (F : Type) [Field F] (b : F) (c : F) (v : Fin 14 → F) :
    adjOfCoord F b (c • v) = c • adjOfCoord F b v := by
  have hmem : c • adjOfCoord F b v ∈ adjOmega6 F b := by
    obtain ⟨hs, hd, hf⟩ := adjOfCoord_mem F b v
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.transpose_smul, hs]
    · intro i
      simp [hd i]
    · simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      rw [show b * (c * adjOfCoord F b v (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1))) =
        c * (b * adjOfCoord F b v (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1))) by ring]
      rw [← mul_add, hf, mul_zero]
  have h : adjCoord (adjOfCoord F b (c • v)) = adjCoord (c • adjOfCoord F b v) := by
    rw [adjCoord_adjOfCoord]
    show c • v = adjCoord (c • adjOfCoord F b v)
    rw [show adjCoord (c • adjOfCoord F b v) = c • adjCoord (adjOfCoord F b v) from rfl,
      adjCoord_adjOfCoord]
  symm
  calc c • adjOfCoord F b v
      = adjOfCoord F b (adjCoord (c • adjOfCoord F b v)) :=
        (adjOfCoord_adjCoord hmem).symm
    _ = adjOfCoord F b (adjCoord (adjOfCoord F b (c • v))) := by rw [h]
    _ = adjOfCoord F b (c • v) := adjOfCoord_adjCoord (adjOfCoord_mem F b (c • v))

private lemma adjOfCoord_sumFinset (F : Type) [Field F] {ι : Type} (b : F) (s : Finset ι)
    (g : ι → Fin 14 → F) :
    adjOfCoord F b (∑ i ∈ s, g i) = ∑ i ∈ s, adjOfCoord F b (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [adjOfCoord_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, adjOfCoord_add, ih]

private lemma adjOfCoord_sum (F : Type) [Field F] {ι : Type} [Fintype ι] (b : F)
    (g : ι → Fin 14 → F) :
    adjOfCoord F b (∑ i, g i) = ∑ i, adjOfCoord F b (g i) :=
  adjOfCoord_sumFinset F b Finset.univ g

private lemma adjOfCoord_eq_sum_single (F : Type) [Field F] (b : F) (v : Fin 14 → F) :
    adjOfCoord F b v = ∑ j, v j • adjOfCoord F b (Pi.single j 1) := by
  have hv : v = ∑ j, v j • Pi.single j (1 : F) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
    · intro hi
      simp at hi
  conv_lhs => rw [hv]
  rw [adjOfCoord_sum]
  exact Finset.sum_congr rfl fun j _ => adjOfCoord_smul F b (v j) _

@[expose] def adjMat (F : Type) [Field F] (b : F) (A : Matrix Om6Idx Om6Idx F) :
    Matrix (Fin 14) (Fin 14) F :=
  Matrix.of fun i j => adjCoord (A * adjOfCoord F b (Pi.single j 1) * Aᵀ) i

private lemma adjCoord_conj_aux (F : Type) [Field F] (b : F) (A : Matrix Om6Idx Om6Idx F)
    (v : Fin 14 → F) :
    adjCoord (A * adjOfCoord F b v * Aᵀ) = adjMat F b A *ᵥ v := by
  rw [adjOfCoord_eq_sum_single]
  ext i
  simp only [adjCoord, adjMat, Matrix.of_apply, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply, Matrix.mulVec,
    dotProduct, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => mul_comm _ _)]

theorem adjCoord_conj {F : Type} [Field F] {b : F} (A : Matrix Om6Idx Om6Idx F)
    {X : Matrix Om6Idx Om6Idx F} (hX : X ∈ adjOmega6 F b) :
    adjCoord (A * X * Aᵀ) = adjMat F b A *ᵥ adjCoord X := by
  conv_lhs => rw [← adjOfCoord_adjCoord hX]
  exact adjCoord_conj_aux F b A _

private lemma adjOmega6_map_mem {F : Type} [Field F] {F' : Type} [Field F']
    (f : F →+* F') (b : F) {X : Matrix Om6Idx Om6Idx F} (hX : X ∈ adjOmega6 F b) :
    X.map f ∈ adjOmega6 F' (f b) := by
  obtain ⟨hs, hd, hf⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.transpose_map, hs]
  · intro i
    simp [hd i]
  · simp only [Matrix.map_apply]
    rw [← map_sum, ← map_mul, ← map_add, hf, map_zero]

private lemma adjOfCoord_map {F : Type} [Field F] {F' : Type} [Field F'] (f : F →+* F')
    (b : F) (v : Fin 14 → F) :
    (adjOfCoord F b v).map f = adjOfCoord F' (f b) (fun j => f (v j)) := by
  have hmem : (adjOfCoord F b v).map f ∈ adjOmega6 F' (f b) :=
    adjOmega6_map_mem f b (adjOfCoord_mem F b v)
  have hcoord : adjCoord ((adjOfCoord F b v).map f) = fun j => f (v j) := by
    funext j
    simp only [adjCoord, Matrix.map_apply]
    exact congrArg f (congrFun (adjCoord_adjOfCoord F b v) j)
  calc (adjOfCoord F b v).map f
      = adjOfCoord F' (f b) (adjCoord ((adjOfCoord F b v).map f)) :=
        (adjOfCoord_adjCoord hmem).symm
    _ = adjOfCoord F' (f b) (fun j => f (v j)) := by rw [hcoord]

theorem adjMat_map {F F' : Type} [Field F] [Field F'] (f : F →+* F') (b : F)
    (A : Matrix Om6Idx Om6Idx F) : (adjMat F b A).map f = adjMat F' (f b) (A.map f) := by
  ext i j
  simp only [Matrix.map_apply, adjMat, Matrix.of_apply]
  change adjCoord ((A * adjOfCoord F b (Pi.single j (1 : F)) * Aᵀ).map f) i =
    adjCoord (A.map f * adjOfCoord F' (f b) (Pi.single j (1 : F')) * (A.map f)ᵀ) i
  rw [show (A * adjOfCoord F b (Pi.single j (1 : F)) * Aᵀ).map f =
      A.map f * (adjOfCoord F b (Pi.single j (1 : F))).map f * (A.map f)ᵀ by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]]
  rw [adjOfCoord_map]
  have hsingle : (fun j_1 : Fin 14 => f (((Pi.single j (1 : F) : Fin 14 → F) j_1))) =
      (Pi.single j (1 : F') : Fin 14 → F') := by
    funext k
    by_cases h : k = j <;> simp [Pi.single_apply, h]
  rw [hsingle]

theorem adjMat_one (F : Type) [Field F] (b : F) : adjMat F b 1 = 1 := by
  ext i j
  simp only [adjMat, Matrix.of_apply, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
    Matrix.one_apply, adjCoord_adjOfCoord, Pi.single_apply]

theorem adjMat_mul {F : Type} [Field F] {b : F} (A B : Matrix Om6Idx Om6Idx F)
    (hB : ∀ X ∈ adjOmega6 F b, B * X * Bᵀ ∈ adjOmega6 F b) :
    adjMat F b (A * B) = adjMat F b A * adjMat F b B := by
  ext i j
  simp only [adjMat, Matrix.of_apply, Matrix.mul_apply]
  have hBM : B * adjOfCoord F b (Pi.single j (1 : F)) * Bᵀ ∈ adjOmega6 F b :=
    hB _ (adjOfCoord_mem F b _)
  have hrew : A * B * adjOfCoord F b (Pi.single j (1 : F)) * (A * B)ᵀ =
      A * (B * adjOfCoord F b (Pi.single j (1 : F)) * Bᵀ) * Aᵀ := by
    rw [Matrix.transpose_mul]
    noncomm_ring
  rw [hrew]
  rw [show B * adjOfCoord F b (Pi.single j (1 : F)) * Bᵀ =
      adjOfCoord F b (adjCoord (B * adjOfCoord F b (Pi.single j (1 : F)) * Bᵀ)) from
    (adjOfCoord_adjCoord hBM).symm]
  rw [adjCoord_conj_aux F b A (adjCoord (B * adjOfCoord F b (Pi.single j (1 : F)) * Bᵀ))]
  rw [adjCoord_conj_aux F b B (Pi.single j (1 : F))]
  rw [adjCoord_adjOfCoord]
  rfl

@[expose] noncomputable def adjMatHom (F : Type) [Field F] [CharP F 2] (b c : F) :
    ↥(omIsoGroup (StatedQuadMinus 3 F b c)) →* GL (Fin 14) F :=
  MonoidHom.toHomUnits
    { toFun := fun g => adjMat F b ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)
      map_one' := by simpa using adjMat_one F b
      map_mul' := fun g h => adjMat_mul _ _ fun X hX => mem_adjOmega6_conj (fun v => h.2 v) hX }

@[expose] noncomputable def adjMatHomOmega (F : Type) [Field F] [CharP F 2] (b c : F) :
    ↥(StatedOmega (StatedQuadMinus 3 F b c)) →* GL (Fin 14) F :=
  (adjMatHom F b c).comp (Subgroup.inclusion (statedOmega_le_omIsoGroup _))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

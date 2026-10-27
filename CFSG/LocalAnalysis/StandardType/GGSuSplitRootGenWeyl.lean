module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock

public section

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.Universal.SpecialLinear
  Multiplicative

variable {n r ε p : ℕ} {K : Type} [Field K]

private theorem splitEntries_add {ζ : K} (hp : p.Prime) (hpow : ζ ^ p = 1)
    (t t' : Fin r → ZMod p) :
    splitEntries (ε := ε) ζ (t + t') = splitEntries ζ t * splitEntries ζ t' := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  funext x
  rcases x with i | k | i
  · simp only [splitEntries, Pi.add_apply, Pi.mul_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hpow, pow_add]
  · simp [splitEntries]
  · simp only [splitEntries, Pi.add_apply, Pi.mul_apply, ZMod.val_add]
    rw [← pow_eq_pow_mod _ hpow, pow_add, mul_inv]

theorem exists_isSplitTorus (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K} (hζ : ζ ^ p = 1)
    (hbar : h.bar ζ = ζ) :
    ∃ τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε, IsSplitTorus h ζ τ := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hbar_pow : ∀ m : ℕ, h.bar (ζ ^ m) = ζ ^ m := fun m => by rw [map_pow, hbar]
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  let a : (Fin r → ZMod p) → Fin r → Kˣ :=
    fun t i => Units.mk0 (ζ ^ (t i).val) (pow_ne_zero _ hζ0)
  let d1 : Fin ε → Kˣ := 1
  have hd : ∀ k : Fin ε, h.norm (d1 k : K) = 1 := fun k => by
    simp [d1, UnitaryFieldData.norm]
  have hratio : ∀ t, torusRatio h (a t) d1 = 1 := by
    intro t
    have hprod : (∏ i, (a t i : K) / h.bar (a t i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hb : h.bar (a t i : K) = (a t i : K) := by
        rw [Units.val_mk0]
        exact hbar_pow _
      rw [hb]
      exact div_self (by rw [Units.val_mk0]; exact pow_ne_zero _ hζ0)
    rw [torusRatio, hprod, Finset.prod_eq_one (fun k _ => by simp [d1]), mul_one]
  have hex : ∀ t : Fin r → ZMod p, ∃ g : hypSU h r ε,
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        diagonal (splitEntries ζ t)) := by
    intro t
    obtain ⟨g, -, hg⟩ := torusMat_mem_hypSU (d := d1) h (a t) hd (hratio t)
    refine ⟨g, ?_⟩
    rw [hg]
    congr 1
    funext x
    rcases x with i | k | i
    · simp [torusEntries, splitEntries, a]
    · simp [torusEntries, splitEntries, d1]
    · simp [torusEntries, splitEntries, a, hbar_pow]
  let g : (Fin r → ZMod p) → hypSU h r ε := fun t => Classical.choose (hex t)
  have hg : ∀ t : Fin r → ZMod p,
      (((g t : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal (splitEntries ζ t) :=
    fun t => Classical.choose_spec (hex t)
  have hmul : ∀ t t' : Fin r → ZMod p, g (t + t') = g t * g t' := by
    intro t t'
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hg, hg, hg, diagonal_mul_diagonal,
      splitEntries_add hp hζ]
    rfl
  refine ⟨MonoidHom.mk' (fun m : Multiplicative (Fin r → ZMod p) =>
    g (Multiplicative.toAdd m)) ?_, ?_⟩
  · intro m m'
    exact hmul (Multiplicative.toAdd m) (Multiplicative.toAdd m')
  · intro t
    exact hg t

theorem swapSet_mul_self (T : Finset (Fin r)) : swapSet T * swapSet T = 1 := by
  ext x
  rcases x with j | j <;> by_cases hj : j ∈ T <;> simp [swapSet, hj]

private theorem weylPerm_swapSet_singleton_symm (m : Fin r) :
    (weylPerm (ε := ε) (swapSet {m})).symm = weylPerm (ε := ε) (swapSet {m}) := by
  have hmul : weylPerm (ε := ε) (swapSet {m}) * weylPerm (ε := ε) (swapSet {m}) = 1 := by
    rw [← weylPerm_mul, swapSet_mul_self, weylPerm_one]
  rw [← Equiv.Perm.inv_def]
  exact inv_eq_of_mul_eq_one_right hmul

private theorem weylPerm_swapSet_singleton_inl (m i : Fin r) :
    weylPerm (ε := ε) (swapSet {m}) (.inl i) =
      if i = m then .inr (.inr m) else .inl i := by
  rw [UnitarySixFieldTwo.weylPerm_swapSet_inl]
  by_cases hi : i = m <;> simp [hi]

private theorem weylPerm_swapSet_singleton_inr_inr (m i : Fin r) :
    weylPerm (ε := ε) (swapSet {m}) (.inr (.inr i)) =
      if i = m then .inl m else .inr (.inr i) := by
  rw [UnitarySixFieldTwo.weylPerm_swapSet_inr_inr]
  by_cases hi : i = m <;> simp [hi]

private theorem weylPerm_swapSet_singleton_eq_self_of_notMem {m : Fin r} {b : HypIndex r ε}
    (hb : b ∉ lineCoords (ε := ε) m) : weylPerm (ε := ε) (swapSet {m}) b = b := by
  rcases b with i | k | i
  · have hi : i ≠ m := fun h => hb (by simp [lineCoords, h])
    rw [weylPerm_swapSet_singleton_inl, if_neg hi]
  · exact weylPerm_inr_inl _ _
  · have hi : i ≠ m := fun h => hb (by simp [lineCoords, h])
    rw [weylPerm_swapSet_singleton_inr_inr, if_neg hi]

private theorem weylPerm_swapSet_singleton_mem_of_mem {m : Fin r} {b : HypIndex r ε}
    (hb : b ∈ lineCoords (ε := ε) m) :
    weylPerm (ε := ε) (swapSet {m}) b ∈ lineCoords (ε := ε) m := by
  rcases b with i | k | i
  · rw [weylPerm_swapSet_singleton_inl]
    have hi : i = m := by simpa [lineCoords] using hb
    subst hi
    simp [lineCoords]
  · rw [weylPerm_inr_inl]
    simp [lineCoords]
  · rw [weylPerm_swapSet_singleton_inr_inr]
    have hi : i = m := by simpa [lineCoords] using hb
    subst hi
    simp [lineCoords]

theorem lineWeyl_mem_lineBlock (h : UnitaryFieldData 2 n K) (m : Fin r) :
    lineWeyl h ε m ∈ lineBlock h m := by
  rw [lineBlock, mem_hypBlock]
  intro a b hab
  have hW : (((lineWeyl h ε m : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = weylMat h 1 (swapSet {m}) :=
    coe_weylElt h (one_mem_traceZero h) one_ne_zero (swapSet_mem_hypWeyl {m})
  rw [hW, weylMat, UnitarySixFieldTwo.weylCoeff_one, signedPerm_apply, Matrix.one_apply]
  rcases hab with ha | hb
  · by_cases hbT : b ∈ lineCoords (ε := ε) m
    · have hwb : weylPerm (ε := ε) (swapSet {m}) b ∈ lineCoords (ε := ε) m :=
        weylPerm_swapSet_singleton_mem_of_mem hbT
      have hne : a ≠ weylPerm (ε := ε) (swapSet {m}) b := fun h => ha (h ▸ hwb)
      have hne' : a ≠ b := fun h => ha (h ▸ hbT)
      simp [hne, hne']
    · rw [weylPerm_swapSet_singleton_eq_self_of_notMem hbT]
  · rw [weylPerm_swapSet_singleton_eq_self_of_notMem hb]

private theorem coe_pairWeyl (h : UnitaryFieldData 2 n K) (i j : Fin r) :
    (((pairWeyl h ε i j : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blk3 ((Equiv.swap i j).permMatrix K) 0 0 1 0 ((Equiv.swap i j).permMatrix K) := by
  have hW : (((pairWeyl h ε i j : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      weylMat h 1 (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) :=
    coe_weylElt h (one_mem_traceZero h) one_ne_zero (sumCongr_mem_hypWeyl (Equiv.swap i j))
  rw [hW, weylMat, UnitarySixFieldTwo.weylCoeff_one,
    CFSG.RankThree.CentralLiftU.weylPerm_sumCongr_swap]
  have hP : ∀ x y : Fin r, (Equiv.swap i j).permMatrix K x y =
      if Equiv.swap i j x = y then 1 else 0 := by
    intro x y
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  ext a b
  rw [signedPerm_apply]
  rcases a with a | k | a <;> rcases b with b | l | b
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inl]
    simp only [Sum.inl.injEq, blk3_inl_inl]
    rw [hP]
    simp [Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_z]
    simp [blk3_inl_inr_inl]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inr]
    simp [blk3_inl_inr_inr]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inl]
    simp [blk3_inr_inl_inl]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_z]
    simp [blk3_inr_inl_inr_inl, Matrix.one_apply]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inr]
    simp [blk3_inr_inl_inr_inr]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inl]
    simp [blk3_inr_inr_inl]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_z]
    simp [blk3_inr_inr_inr_inl]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inr]
    simp only [Sum.inr.injEq, blk3_inr_inr_inr_inr]
    rw [hP]
    simp [Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap]

private theorem pairWeyl_eq_leviSU (h : UnitaryFieldData 2 n K) (i j : Fin r) [CharP K 2] :
    leviSU h ε (CFSG.StandardType.TypeA.permSL (Equiv.swap i j)) = pairWeyl h ε i j := by
  apply Subtype.ext
  apply Units.ext
  let A : GL (Fin r) K :=
    SpecialLinearGroup.toGL (CFSG.StandardType.TypeA.permSL (Equiv.swap i j))
  have hA : (A : Matrix (Fin r) (Fin r) K) = (Equiv.swap i j).permMatrix K := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix, CFSG.StandardType.TypeA.coe_permSL]
  have hD : leviDual h A = (Equiv.swap i j).permMatrix K := by
    have hAinv : ((A⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        ((Equiv.swap i j)⁻¹).permMatrix K := by
      rw [show A⁻¹ = SpecialLinearGroup.toGL
        ((CFSG.StandardType.TypeA.permSL (Equiv.swap i j))⁻¹) from (map_inv _ _).symm]
      rw [CFSG.StandardType.TypeA.permSL_inv, SpecialLinearGroup.coe_GL_coe_matrix,
        CFSG.StandardType.TypeA.coe_permSL]
    rw [leviDual, hAinv]
    have hmap : ((((Equiv.swap i j)⁻¹).permMatrix K)).map h.bar =
        ((Equiv.swap i j)⁻¹).permMatrix K := by
      ext a b
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
      by_cases hab : Equiv.swap i j a = b <;> simp [hab]
    rw [hmap, Matrix.transpose_permMatrix, inv_inv]
  rw [coe_leviSU, coe_leviGL, hA, hD]
  exact (coe_pairWeyl h i j).symm

theorem pairWeyl_mem_pairBlock (h : UnitaryFieldData 2 n K) (i j : Fin r) :
    pairWeyl h ε i j ∈ pairBlock h ε i j := by
  haveI : CharP K 2 := h.charP
  have hmem : CFSG.StandardType.TypeA.permSL (Equiv.swap i j) ∈
      CFSG.RankThree.CALinearPlane.coordBlockSL K ({i, j} : Finset (Fin r)) :=
    CFSG.StandardType.TypeA.permSL_mem_coordBlockSL
  rw [pairBlock, ← pairWeyl_eq_leviSU h i j]
  exact Subgroup.mem_map_of_mem (leviSU h ε) hmem

theorem lineWeyl_conj (h : UnitaryFieldData 2 n K) (hp : p.Prime) {ζ : K} (hζ : ζ ^ p = 1)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (m : Fin r)
    (t : Fin r → ZMod p) :
    lineWeyl h ε m * τ (ofAdd t) * (lineWeyl h ε m)⁻¹ =
      τ (ofAdd (SlNsRootGen.negMap m t)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hW : (((lineWeyl h ε m : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = weylMat h 1 (swapSet {m}) :=
    coe_weylElt h (one_mem_traceZero h) one_ne_zero (swapSet_mem_hypWeyl {m})
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
  rw [hW, hτ t, hτ (SlNsRootGen.negMap m t)]
  rw [weylMat_mul_diagonal]
  have hmul : weylMat (ε := ε) h 1 (swapSet {m}) *
      (weylMat (ε := ε) h 1 (swapSet {m}))⁻¹ = 1 := by
    rw [← hW, ← Matrix.GeneralLinearGroup.coe_inv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  rw [mul_assoc, hmul, mul_one]
  congr 1
  funext a
  rw [weylPerm_swapSet_singleton_symm]
  rcases a with i | k | i
  · by_cases hi : i = m
    · subst hi
      rw [weylPerm_swapSet_singleton_inl, if_pos rfl]
      simp [splitEntries, SlNsRootGen.negMap, Function.update_apply, hypEntries_neg hp hζ]
    · rw [weylPerm_swapSet_singleton_inl, if_neg hi]
      simp [splitEntries, SlNsRootGen.negMap, Function.update_apply, hi]
  · simp [splitEntries]
  · by_cases hi : i = m
    · subst hi
      rw [weylPerm_swapSet_singleton_inr_inr, if_pos rfl]
      simp [splitEntries, SlNsRootGen.negMap, Function.update_apply, hypEntries_neg hp hζ]
    · rw [weylPerm_swapSet_singleton_inr_inr, if_neg hi]
      simp [splitEntries, SlNsRootGen.negMap, Function.update_apply, hi]

theorem pairWeyl_conj (h : UnitaryFieldData 2 n K) {ζ : K}
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ) (i j : Fin r)
    (t : Fin r → ZMod p) :
    pairWeyl h ε i j * τ (ofAdd t) * (pairWeyl h ε i j)⁻¹ =
      τ (ofAdd (SlNsRootGen.swapMap i j t)) := by
  have hW : (((pairWeyl h ε i j : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      weylMat h 1 (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) :=
    coe_weylElt h (one_mem_traceZero h) one_ne_zero (sumCongr_mem_hypWeyl (Equiv.swap i j))
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
  rw [hW, hτ t, hτ (SlNsRootGen.swapMap i j t)]
  rw [weylMat_mul_diagonal]
  have hmul : weylMat (ε := ε) h 1 (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) *
      (weylMat (ε := ε) h 1 (Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)))⁻¹ = 1 := by
    rw [← hW, ← Matrix.GeneralLinearGroup.coe_inv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  rw [mul_assoc, hmul, mul_one]
  congr 1
  funext a
  rw [CFSG.RankThree.CentralLiftU.weylPerm_sumCongr_swap,
    CFSG.RankThree.CentralLiftU.swapIdx_symm]
  rcases a with a | k | a
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inl]
    simp [splitEntries, SlNsRootGen.swapMap]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_z]
    simp [splitEntries]
  · rw [CFSG.RankThree.CentralLiftU.swapIdx_inr]
    simp [splitEntries, SlNsRootGen.swapMap]

end CFSG.StandardType.SuSplitRootGen

end

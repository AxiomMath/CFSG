module

public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelBasic

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))

theorem mul_pow_fix (hF : Fintype.card F = 2 ^ (2 * l)) (b : F) :
    (b * b ^ 2 ^ l) ^ 2 ^ l = b * b ^ 2 ^ l := by
  rw [mul_pow]
  have h : (b ^ 2 ^ l) ^ 2 ^ l = b := by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]
  rw [h, mul_comm]

@[expose] def hermDiag (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (a : F)
    (ha : a ^ 2 ^ l = a) : ↥(hermA l F) :=
  ⟨!![a, 0; 0, 0], by
    refine mem_hermA_of fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sig_apply, ha]⟩

theorem hermDiag_coe (a : F) (ha : a ^ 2 ^ l = a) :
    (hermDiag l hF a ha : Matrix (Fin 2) (Fin 2) F) = !![a, 0; 0, 0] := rfl

@[expose] def hermDiag11 (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (a : F)
    (ha : a ^ 2 ^ l = a) : ↥(hermA l F) :=
  ⟨!![0, 0; 0, a], by
    refine mem_hermA_of fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sig_apply, ha]⟩

theorem hermDiag11_coe (a : F) (ha : a ^ 2 ^ l = a) :
    (hermDiag11 l hF a ha : Matrix (Fin 2) (Fin 2) F) = !![0, 0; 0, a] := rfl

@[expose] def hermOff (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (b : F) : ↥(hermA l F) :=
  ⟨!![0, b; b ^ 2 ^ l, 0], by
    have hb : (b ^ 2 ^ l) ^ 2 ^ l = b := by
      rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]
    refine mem_hermA_of fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [sig_apply, hb]⟩

theorem hermOff_coe (b : F) :
    (hermOff l hF b : Matrix (Fin 2) (Fin 2) F) = !![0, b; b ^ 2 ^ l, 0] := rfl

@[expose] def hermE11 (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) : ↥(hermA l F) :=
  hermDiag11 l hF 1 (by simp)

theorem hermE11_coe :
    (hermE11 l hF : Matrix (Fin 2) (Fin 2) F) = !![0, 0; 0, 1] :=
  hermDiag11_coe (hF := hF) (1 : F) (by simp)

@[expose] def hermP (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) : ↥(hermA l F) :=
  hermOff l hF 1

theorem hermP_coe : (hermP l hF : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
  rw [hermP, hermOff_coe, one_pow]

theorem eq_hermDiag_of_mem_herm1101 (X : ↥(hermA l F))
    (hX : X ∈ herm1101 l F) :
    X = hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) := by
  obtain ⟨h11, h01⟩ := hX
  refine hermA_ext ?_ ?_ ?_
  · rfl
  · rw [h01]; rfl
  · rw [h11]; rfl

theorem hermDiag_mem_herm1101 (a : F) (ha : a ^ 2 ^ l = a) :
    hermDiag l hF a ha ∈ herm1101 l F := by
  refine ⟨?_, ?_⟩
  · rw [hermDiag_coe]
    rfl
  · rw [hermDiag_coe]
    rfl

theorem eq_hermDiag_add_offdiag_of_herm11 (X : ↥(hermA l F))
    (h11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) :
    X = hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) +
      hermOff l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hD : (hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) :
      Matrix (Fin 2) (Fin 2) F) = !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
  have hO : (hermOff l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) :
      Matrix (Fin 2) (Fin 2) F) = !![0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
        ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l, 0] := rfl
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AddSubgroup.coe_add, Matrix.add_apply, hD, hO, h11, hermA_10 (a := l) X, sig_apply]

theorem eq_hermDiag_add_diag_add_offdiag (X : ↥(hermA l F)) :
    X = hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) +
      hermDiag11 l hF ((X : Matrix (Fin 2) (Fin 2) F) 1 1) (hermA_11 (a := l) X) +
        hermOff l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hD : (hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) :
      Matrix (Fin 2) (Fin 2) F) = !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
  have hD11 : (hermDiag11 l hF ((X : Matrix (Fin 2) (Fin 2) F) 1 1) (hermA_11 (a := l) X) :
      Matrix (Fin 2) (Fin 2) F) = !![0, 0; 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1] := rfl
  have hO : (hermOff l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) :
      Matrix (Fin 2) (Fin 2) F) = !![0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
        ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l, 0] := rfl
  refine hermA_ext ?_ ?_ ?_
  · rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_apply, Matrix.add_apply,
      hD, hD11, hO]; simp
  · rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_apply, Matrix.add_apply,
      hD, hD11, hO]; simp
  · rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_apply, Matrix.add_apply,
      hD, hD11, hO]; simp

@[expose] def hermV (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) (b : F) : ↥(hermA l F) :=
  hermAct l (sig_sig hF) (uMat b) (hermE11 l hF) - hermE11 l hF

theorem hermV_coe (b : F) :
    (hermV l hF b : Matrix (Fin 2) (Fin 2) F) = !![b * b ^ 2 ^ l, b; b ^ 2 ^ l, 0] := by
  rw [hermV, hermAct_uMat_sub l hF b (hermE11 l hF), hermE11_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem hermV_mem_commSub (b : F) :
    hermV l hF b ∈ commSub (hermRep l hF) upperSylow := by
  rw [hermV]
  exact range_le_commSub (mem_upperSylow_iff.mpr ⟨b, rfl⟩) ⟨hermE11 l hF, rfl⟩

theorem hermV_eq_diag_add_offdiag (b : F) :
    hermV l hF b = hermDiag l hF (b * b ^ 2 ^ l) (mul_pow_fix hF b) +
      hermOff l hF b := by
  have hV : (hermV l hF b : Matrix (Fin 2) (Fin 2) F) =
      !![b * b ^ 2 ^ l, b; b ^ 2 ^ l, 0] := hermV_coe hF b
  have hD : (hermDiag l hF (b * b ^ 2 ^ l) (mul_pow_fix hF b) :
      Matrix (Fin 2) (Fin 2) F) = !![b * b ^ 2 ^ l, 0; 0, 0] := rfl
  have hO : (hermOff l hF b : Matrix (Fin 2) (Fin 2) F) = !![0, b; b ^ 2 ^ l, 0] := rfl
  refine hermA_ext ?_ ?_ ?_
  · rw [AddSubgroup.coe_add, Matrix.add_apply, hV, hD, hO]; simp
  · rw [AddSubgroup.coe_add, Matrix.add_apply, hV, hD, hO]; simp
  · rw [AddSubgroup.coe_add, Matrix.add_apply, hV, hD, hO]; simp

theorem map_commSub_le (a : SL(2, F)) (ha : a ∈ upperSylow) :
    Submodule.map (hermRep l hF a) (commSub (hermRep l hF) upperSylow) ≤
      commSub (hermRep l hF) upperSylow := by
  obtain ⟨s, rfl⟩ := mem_upperSylow_iff.mp ha
  rw [Submodule.map_le_iff_le_comap]
  refine iSup₂_le fun b hb => ?_
  obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hb
  intro v hv
  rw [LinearMap.mem_range] at hv
  obtain ⟨u, rfl⟩ := hv
  refine range_le_commSub (mem_upperSylow_iff.mpr ⟨t, rfl⟩)
    ⟨hermRep l hF (uMat s) u, ?_⟩
  have hcomm : hermRep l hF (uMat t) * hermRep l hF (uMat s) =
      hermRep l hF (uMat s) * hermRep l hF (uMat t) := by
    rw [← map_mul, ← map_mul, uMat_mul, uMat_mul, add_comm]
  calc (hermRep l hF (uMat t) - 1) (hermRep l hF (uMat s) u)
      = hermRep l hF (uMat t) (hermRep l hF (uMat s) u) -
        hermRep l hF (uMat s) u := rfl
    _ = (hermRep l hF (uMat t) * hermRep l hF (uMat s)) u -
        hermRep l hF (uMat s) u := rfl
    _ = (hermRep l hF (uMat s) * hermRep l hF (uMat t)) u -
        hermRep l hF (uMat s) u := by rw [hcomm]
    _ = hermRep l hF (uMat s) (hermRep l hF (uMat t) u) -
        hermRep l hF (uMat s) u := rfl
    _ = hermRep l hF (uMat s) ((hermRep l hF (uMat t) - 1) u) := by
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub]

theorem commSub_map_sub_le (a : SL(2, F)) (ha : a ∈ upperSylow) :
    Submodule.map (hermRep l hF a - 1) (commSub (hermRep l hF) upperSylow) ≤
      commSub (hermRep l hF) upperSylow := by
  intro v hv
  rw [Submodule.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  rw [LinearMap.sub_apply, Module.End.one_apply]
  exact (commSub (hermRep l hF) upperSylow).sub_mem
    (map_commSub_le (hF := hF) a ha ⟨u, hu, rfl⟩) hu

@[expose] def doubleCommSub (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l))
    (w : ↥(hermA l F)) : AddSubgroup ↥(hermA l F) :=
  AddSubgroup.closure {x | ∃ a ∈ upperSylow, ∃ b ∈ upperSylow,
    x = (hermRep l hF a - 1) ((hermRep l hF b - 1) w)}

theorem hermA_11_mul_add_pow_fixed (hF' : Fintype.card F = 2 ^ (2 * l))
    (w : ↥(hermA l F)) (t : F) :
    (((w : Matrix (Fin 2) (Fin 2) F) 1 1 * (t ^ 2 ^ l + t)) ^ 2 ^ l) =
      (w : Matrix (Fin 2) (Fin 2) F) 1 1 * (t ^ 2 ^ l + t) := by
  rw [mul_pow]
  have ht : ((t ^ 2 ^ l + t) ^ 2 ^ l) = t ^ 2 ^ l + t := by
    rw [add_pow_char_pow]
    have hσ : (t ^ 2 ^ l) ^ 2 ^ l = t := by
      rw [← pow_mul, ← pow_add, ← two_mul, ← hF', FiniteField.pow_card]
    rw [hσ]; ring
  rw [ht]
  have hw := hermA_11 (a := l) w
  rw [sig_apply] at hw
  rw [hw]

theorem doubleCommSub_uMat_one (w : ↥(hermA l F)) (t : F) :
    (hermRep l hF (uMat t) - 1) ((hermRep l hF (uMat 1) - 1) w) =
      hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 1 1 * (t ^ 2 ^ l + t))
        (hermA_11_mul_add_pow_fixed hF w t) := by
  let Y : ↥(hermA l F) := (hermRep l hF (uMat 1) - 1) w
  have hY : (Y : Matrix (Fin 2) (Fin 2) F) =
      ((hermAct l (sig_sig hF) (uMat 1) w - w : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F) := rfl
  have hstep : (hermRep l hF (uMat t) - 1) Y =
      hermAct l (sig_sig hF) (uMat t) Y - Y := rfl
  apply Subtype.ext
  rw [hstep, hermAct_uMat_sub l hF t Y, hY, hermAct_uMat_sub l hF 1 w, hermDiag_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem doubleCommSub_le_herm1101 (w : ↥(hermA l F)) :
    doubleCommSub l hF w ≤ herm1101 l F := by
  rw [doubleCommSub, AddSubgroup.closure_le]
  rintro x ⟨a, ha, b, hb, rfl⟩
  obtain ⟨s, rfl⟩ := mem_upperSylow_iff.mp ha
  obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hb
  simp only [hermRep_apply, LinearMap.sub_apply, Module.End.one_apply]
  have hY11 : ((hermAct l (sig_sig hF) (uMat t) w - w : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    rw [AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_11, sub_self]
  have hZ11 : ((hermAct l (sig_sig hF) (uMat s)
      (hermAct l (sig_sig hF) (uMat t) w - w) -
        (hermAct l (sig_sig hF) (uMat t) w - w) : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    rw [AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_11, hY11, sub_self]
  have hZ01 : ((hermAct l (sig_sig hF) (uMat s)
      (hermAct l (sig_sig hF) (uMat t) w - w) -
        (hermAct l (sig_sig hF) (uMat t) w - w) : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    rw [AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_01, hY11, mul_zero, add_zero,
      sub_self]
  exact ⟨hZ11, hZ01⟩

theorem herm1101_le_doubleCommSub (w : ↥(hermA l F))
    (hw : (w : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    herm1101 l F ≤ doubleCommSub l hF w := by
  have hl : 1 ≤ l := one_le_of_card hF
  intro X hX
  have hwfix : ((w : Matrix (Fin 2) (Fin 2) F) 1 1) ^ 2 ^ l =
      (w : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h := hermA_11 (a := l) w
    rwa [sig_apply] at h
  have hdiag : ∀ a : F, (ha : a ^ 2 ^ l = a) →
      hermDiag l hF a ha ∈ doubleCommSub l hF w := by
    intro a ha
    have hdiv : a / (w : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ frobFixField l F :=
      (frobFixField l F).div_mem ha (mem_frobFixField.mpr hwfix)
    obtain ⟨t, ht⟩ := exists_add_sig_eq (hF := hF) (mem_frobFixField.mp hdiv)
    have hgen : (hermRep l hF (uMat t) - 1) ((hermRep l hF (uMat 1) - 1) w) =
        hermDiag l hF a ha := by
      rw [doubleCommSub_uMat_one (hF := hF) w t]
      refine hermA_ext ?_ ?_ ?_
      · rw [hermDiag_coe, hermDiag_coe]
        rw [eq_div_iff hw, mul_comm] at ht
        exact ht
      · rw [hermDiag_coe, hermDiag_coe]
        rfl
      · rw [hermDiag_coe, hermDiag_coe]
        rfl
    exact AddSubgroup.subset_closure ⟨uMat t, mem_upperSylow_iff.mpr ⟨t, rfl⟩,
      uMat 1, mem_upperSylow_iff.mpr ⟨1, rfl⟩, hgen.symm⟩
  rw [eq_hermDiag_of_mem_herm1101 (hF := hF) X hX]
  exact hdiag _ _

theorem herm1101_le_commSub : AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) ≤
    commSub (hermRep l hF) upperSylow := by
  have hl : 1 ≤ l := one_le_of_card hF
  have hw : (hermE11 l hF : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [hermE11_coe]; rfl
  have h1 : herm1101 l F ≤ doubleCommSub l hF (hermE11 l hF) :=
    herm1101_le_doubleCommSub (hF := hF) _ (by rw [hw]; exact one_ne_zero)
  have h2 : doubleCommSub l hF (hermE11 l hF) ≤
      (commSub (hermRep l hF) upperSylow).toAddSubgroup := by
    rw [doubleCommSub, AddSubgroup.closure_le]
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact commSub_map_sub_le (hF := hF) a ha ⟨_, range_le_commSub hb ⟨hermE11 l hF, rfl⟩, rfl⟩
  intro X hX
  exact h2 (h1 hX)

theorem herm11_le_commSub :
    AddSubgroup.toZModSubmodule (n := 2) (herm11 l F) ≤
      commSub (hermRep l hF) upperSylow := by
  have hl : 1 ≤ l := one_le_of_card hF
  intro X hX
  have hX11 : (X : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := hX
  have hdiag : hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) ∈
      commSub (hermRep l hF) upperSylow :=
    herm1101_le_commSub (hF := hF) (hermDiag_mem_herm1101 (hF := hF) _ _)
  have hV : hermV l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ∈
      commSub (hermRep l hF) upperSylow := hermV_mem_commSub (hF := hF) _
  have hoff : hermOff l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) =
      hermV l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) +
        hermDiag l hF (((X : Matrix (Fin 2) (Fin 2) F) 0 1) *
          ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l)
          (mul_pow_fix hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1)) := by
    have hO : (hermOff l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) :
        Matrix (Fin 2) (Fin 2) F) = !![0, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
          ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l, 0] := rfl
    have hV : (hermV l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1) :
        Matrix (Fin 2) (Fin 2) F) = !![((X : Matrix (Fin 2) (Fin 2) F) 0 1) *
          ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l, (X : Matrix (Fin 2) (Fin 2) F) 0 1;
            ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l, 0] := hermV_coe hF _
    have hD : (hermDiag l hF (((X : Matrix (Fin 2) (Fin 2) F) 0 1) *
          ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l)
          (mul_pow_fix hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1)) :
        Matrix (Fin 2) (Fin 2) F) = !![((X : Matrix (Fin 2) (Fin 2) F) 0 1) *
          ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l, 0; 0, 0] := rfl
    refine hermA_ext ?_ ?_ ?_
    · rw [AddSubgroup.coe_add, Matrix.add_apply, hO, hV, hD]; simp
      exact (CharTwo.add_self_eq_zero _).symm
    · rw [AddSubgroup.coe_add, Matrix.add_apply, hO, hV, hD]; simp
    · rw [AddSubgroup.coe_add, Matrix.add_apply, hO, hV, hD]; simp
  have hdiag' : hermDiag l hF (((X : Matrix (Fin 2) (Fin 2) F) 0 1) *
      ((X : Matrix (Fin 2) (Fin 2) F) 0 1) ^ 2 ^ l)
      (mul_pow_fix hF ((X : Matrix (Fin 2) (Fin 2) F) 0 1)) ∈
      commSub (hermRep l hF) upperSylow :=
    herm1101_le_commSub (hF := hF) (hermDiag_mem_herm1101 (hF := hF) _ _)
  rw [eq_hermDiag_add_offdiag_of_herm11 (hF := hF) X hX11]
  rw [hoff]
  have hsum := (commSub (hermRep l hF) upperSylow).add_mem
    ((commSub (hermRep l hF) upperSylow).add_mem hdiag hV) hdiag'
  simpa [add_assoc, add_comm, add_left_comm] using hsum

theorem commSub_upperSylow :
    commSub (hermRep l hF) upperSylow =
      AddSubgroup.toZModSubmodule (n := 2) (herm11 l F) := by
  have hl : 1 ≤ l := one_le_of_card hF
  refine le_antisymm (commSub_le_herm11 (hF := hF)) ?_
  intro X hX
  exact herm11_le_commSub (hF := hF) hX

theorem fixedSub_eq_span_double (w : ↥(hermA l F))
    (hw : w ∉ commSub (hermRep l hF) upperSylow) :
    fixedSub (hermRep l hF) upperSylow =
      AddSubgroup.toZModSubmodule (n := 2) (doubleCommSub l hF w) := by
  have hl : 1 ≤ l := one_le_of_card hF
  have hw11 : (w : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h
    exact hw (by rw [commSub_upperSylow (hF := hF)]; exact h)
  refine le_antisymm ?_ ?_
  · intro X hX
    have hX' : X ∈ AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
      rwa [← fixedSub_upperSylow (hF := hF)]
    exact herm1101_le_doubleCommSub (hF := hF) w hw11 hX'
  · intro X hX
    have hX' : X ∈ herm1101 l F := doubleCommSub_le_herm1101 (hF := hF) w hX
    rw [fixedSub_upperSylow (hF := hF)]
    exact hX'

@[expose] def commCommSub (l : ℕ) (hF : Fintype.card F = 2 ^ (2 * l)) :
    AddSubgroup ↥(hermA l F) :=
  AddSubgroup.closure {x | ∃ a ∈ upperSylow, ∃ v ∈ commSub (hermRep l hF) upperSylow,
    x = (hermRep l hF a - 1) v}

theorem commCommSub_le_herm1101 : commCommSub l hF ≤ herm1101 l F := by
  have hl : 1 ≤ l := one_le_of_card hF
  rw [commCommSub, AddSubgroup.closure_le]
  rintro x ⟨a, ha, v, hv, rfl⟩
  obtain ⟨s, rfl⟩ := mem_upperSylow_iff.mp ha
  simp only [hermRep_apply, LinearMap.sub_apply, Module.End.one_apply]
  have hv11 : (v : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    rw [commSub_upperSylow (hF := hF)] at hv
    exact hv
  have hZ11 : ((hermAct l (sig_sig hF) (uMat s) v - v : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    rw [AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_11, hv11, sub_self]
  have hZ01 : ((hermAct l (sig_sig hF) (uMat s) v - v : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    rw [AddSubgroup.coe_sub, Matrix.sub_apply, hermAct_uMat_01, hv11, mul_zero, add_zero,
      sub_self]
  exact ⟨hZ11, hZ01⟩

theorem herm1101_le_commCommSub : herm1101 l F ≤ commCommSub l hF := by
  have hl : 1 ≤ l := one_le_of_card hF
  intro X hX
  have hPmem : hermP l hF ∈ commSub (hermRep l hF) upperSylow := by
    rw [commSub_upperSylow (hF := hF)]
    show (hermP l hF : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
    rw [hermP_coe]
    rfl
  have hdiag : ∀ a : F, (ha : a ^ 2 ^ l = a) →
      hermDiag l hF a ha ∈ commCommSub l hF := by
    intro a ha
    obtain ⟨t, ht⟩ := exists_add_sig_eq (hF := hF) ha
    have hgen : (hermRep l hF (uMat t) - 1) (hermP l hF) = hermDiag l hF a ha := by
      apply Subtype.ext
      change ((hermAct l (sig_sig hF) (uMat t) (hermP l hF) - hermP l hF : ↥(hermA l F)) :
        Matrix (Fin 2) (Fin 2) F) = (hermDiag l hF a ha : Matrix (Fin 2) (Fin 2) F)
      have hP : (hermP l hF : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := hermP_coe (hF := hF)
      rw [hermAct_uMat_sub l hF t (hermP l hF), hP, hermDiag_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ht]
    exact AddSubgroup.subset_closure ⟨uMat t, mem_upperSylow_iff.mpr ⟨t, rfl⟩,
      hermP l hF, hPmem, hgen.symm⟩
  rw [eq_hermDiag_of_mem_herm1101 (hF := hF) X hX]
  exact hdiag _ _

theorem fixedSub_eq_span_commSub :
    fixedSub (hermRep l hF) upperSylow =
      AddSubgroup.toZModSubmodule (n := 2) (commCommSub l hF) := by
  have hl : 1 ≤ l := one_le_of_card hF
  refine le_antisymm ?_ ?_
  · intro X hX
    have hX' : X ∈ AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
      rwa [← fixedSub_upperSylow (hF := hF)]
    exact herm1101_le_commCommSub (hF := hF) hX'
  · intro X hX
    have hX' : X ∈ herm1101 l F := commCommSub_le_herm1101 (hF := hF) hX
    rw [fixedSub_upperSylow (hF := hF)]
    exact hX'

end CFSG.RankThree.GF2n.Tim81.Sec2

module

public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofSL2
public import CFSG.RankThree.PartTwo.Sec16.KL3SubProofElat

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace KL3SubProof

open Matrix CFSG.RankThree.PartOne.CTP

variable {K : Type} [Field K]

theorem single_two_vecMul (M : Matrix (Fin 3) (Fin 3) K) :
    (Pi.single 2 1 : Fin 3 → K) ᵥ* M = M.row 2 :=
  single_one_vecMul 2 M

@[expose] def blkSub (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K).det = 1}
  mul_mem' := by
    rintro g h ⟨hg0, hg1, hg2, hgd⟩ ⟨hh0, hh1, hh2, hhd⟩
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
      hg2, hh0, hh1, hh2, Matrix.det_mul, hgd, hhd]
    simp
  one_mem' := by
    simp
  inv_mem' := by
    rintro g ⟨hg0, hg1, hg2, hgd⟩
    have hrow : (Pi.single 2 1 : Fin 3 → K) ᵥ* (g : Matrix (Fin 3) (Fin 3) K) = Pi.single 2 1 := by
      rw [single_two_vecMul]
      ext j
      fin_cases j <;> simp [hg0, hg1, hg2]
    have hinv : (Pi.single 2 1 : Fin 3 → K) ᵥ* ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Pi.single 2 1 := by
      conv_lhs => rw [← hrow]
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    rw [single_two_vecMul] at hinv
    have h0 := congrFun hinv 0
    have h1 := congrFun hinv 1
    have h2 := congrFun hinv 2
    simp only [Matrix.row_apply] at h0 h1 h2
    refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, ?_⟩
    have hd : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det *
        (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hgd, mul_one] at hd
    exact hd

@[expose] def blkMat (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem blkMat_mul {M N : Matrix (Fin 3) (Fin 3) K} (h0 : N 2 0 = 0) (h1 : N 2 1 = 0) :
    blkMat (M * N) = blkMat M * blkMat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h0, h1]

theorem det_blkMat_of_mem_blkSub {g : GL (Fin 3) K} (hg : g ∈ blkSub K) :
    (blkMat (g : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
  obtain ⟨hg0, hg1, hg2, hgd⟩ := hg
  rw [Matrix.det_fin_three, hg0, hg1, hg2] at hgd
  rw [blkMat, Matrix.det_fin_two_of]
  linear_combination hgd

@[expose] def blkHom (K : Type) [Field K] : blkSub K →* SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨blkMat ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), det_blkMat_of_mem_blkSub g.2⟩
  map_one' := by
    apply Subtype.ext
    show blkMat ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  map_mul' g h := by
    apply Subtype.ext
    show blkMat (((g : GL (Fin 3) K) * (h : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = blkMat ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        blkMat ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [Units.val_mul]
    exact blkMat_mul h.2.1 h.2.2.1

theorem coe_blkHom (g : blkSub K) :
    ((blkHom K g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkMat ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

@[expose] def basisMat (a a' : Fin 3 → K) (k : Fin 3) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => ![a, a', Pi.single k 1] j i

theorem det_basisMat (a a' : Fin 3 → K) (k : Fin 3) :
    (basisMat a a' k).det = crossProduct a a' k := by
  rw [Matrix.det_fin_three]
  fin_cases k <;> simp [basisMat, cross_apply] <;> ring

theorem basisMat_mulVec_single (a a' : Fin 3 → K) (k : Fin 3) :
    basisMat a a' k *ᵥ Pi.single 0 1 = a ∧ basisMat a a' k *ᵥ Pi.single 1 1 = a' := by
  refine ⟨?_, ?_⟩ <;> rw [mulVec_single_one] <;> ext i <;> simp [basisMat]

theorem vecMul_basisMat (φ a a' : Fin 3 → K) (k : Fin 3) :
    φ ᵥ* basisMat a a' k = ![φ ⬝ᵥ a, φ ⬝ᵥ a', φ k] := by
  ext j
  fin_cases j <;> fin_cases k <;> simp [basisMat, vecMul, dotProduct, Fin.sum_univ_three]

theorem eq_one_of_elat_triple [Finite K] [CharP K 2]
    {H : Subgroup (GL (Fin 3) K)} (h3 : ¬ 3 ∣ Nat.card H) {z y s : GL (Fin 3) K}
    (hz : z ∈ H) (hy : y ∈ H) (hs : s ∈ H) {a φ a' φ' : Fin 3 → K} {c : K}
    (hzE : IsElat z a φ) (hyE : IsElat y a (c • φ)) (hsE : IsElat s a' φ')
    (h1 : φ ⬝ᵥ a' ≠ 0) (h2 : φ' ⬝ᵥ a ≠ 0) : c = 1 := by
  classical
  by_contra hc1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hyE.2.1 (zero_smul K φ)
  have hli : LinearIndependent K ![a, a'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hdot := congrArg (fun v => φ ⬝ᵥ v) hst
    simp only [dotProduct_add, dotProduct_smul, hzE.2.2.1, smul_eq_mul, mul_zero, zero_add,
      dotProduct_zero] at hdot
    have ht : t = 0 := (mul_eq_zero.mp hdot).resolve_right h1
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hzE.1, rfl⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (crossProduct_ne_zero_iff_linearIndependent.mpr hli)
  set B := basisMat a a' k with hBdef
  have hdet : IsUnit B.det := by
    rw [hBdef, det_basisMat]
    exact isUnit_iff_ne_zero.mpr hk
  set Bu : GL (Fin 3) K := Matrix.nonsingInvUnit B hdet with hBu
  have hBuval : (Bu : Matrix (Fin 3) (Fin 3) K) = B := rfl
  have hBuinv : ((Bu⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = B⁻¹ := rfl
  obtain ⟨hBa, hBa'⟩ := basisMat_mulVec_single a a' k
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBia : B⁻¹ *ᵥ a = Pi.single 0 1 := by
    rw [← hBa, Matrix.mulVec_mulVec, hBinv, Matrix.one_mulVec]
  have hBia' : B⁻¹ *ᵥ a' = Pi.single 1 1 := by
    rw [← hBa', Matrix.mulVec_mulVec, hBinv, Matrix.one_mulVec]
  set conjB : GL (Fin 3) K →* GL (Fin 3) K := (MulAut.conj Bu⁻¹).toMonoidHom with hconjB
  have hconj : ∀ g : GL (Fin 3) K, conjB g = Bu⁻¹ * g * Bu⁻¹⁻¹ := fun g => rfl
  have hzE' := hzE.conj Bu⁻¹
  have hyE' := hyE.conj Bu⁻¹
  have hsE' := hsE.conj Bu⁻¹
  rw [inv_inv, hBuinv, hBuval, hBia] at hzE' hyE'
  rw [inv_inv, hBuinv, hBuval, hBia'] at hsE'
  rw [vecMul_basisMat, hzE.2.2.1] at hzE'
  rw [vecMul_basisMat, dotProduct_comm, dotProduct_smul, dotProduct_comm, hzE.2.2.1,
    smul_zero] at hyE'
  rw [vecMul_basisMat, hsE.2.2.1] at hsE'
  have hblk : ∀ (g : GL (Fin 3) K) (i : Fin 3) (w : Fin 3 → K), i ≠ 2 → w i = 0 →
      (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec (Pi.single i 1) w → g ∈ blkSub K := by
    intro g i w hi hwi hg
    have hdetg : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [hg, det_one_add_vecMulVec, dotProduct_single, mul_one, hwi, add_zero]
    refine ⟨?_, ?_, ?_, hdetg⟩ <;> rw [hg] <;>
      simp [vecMulVec_apply, Ne.symm hi]
  set z' := Bu⁻¹ * z * Bu with hz'
  set y' := Bu⁻¹ * y * Bu with hy'
  set s' := Bu⁻¹ * s * Bu with hs'
  have hz'B : z' ∈ blkSub K := hblk z' 0 _ (by decide) (by simp) hzE'.2.2.2
  have hy'B : y' ∈ blkSub K := hblk y' 0 _ (by decide) (by simp) hyE'.2.2.2
  have hs'B : s' ∈ blkSub K := hblk s' 1 _ (by decide) (by simp) hsE'.2.2.2
  set C := Subgroup.closure ({z', y', s'} : Set (GL (Fin 3) K)) with hC
  have hCB : C ≤ blkSub K := by
    rw [hC, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    exacts [hz'B, hy'B, hs'B]
  have hCH : C ≤ H.map conjB := by
    rw [hC, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact ⟨z, hz, by rw [hconj, inv_inv]⟩
    · exact ⟨y, hy, by rw [hconj, inv_inv]⟩
    · exact ⟨s, hs, by rw [hconj, inv_inv]⟩
  set M := (C.subgroupOf (blkSub K)).map (blkHom K) with hM
  have hMH : Nat.card M ∣ Nat.card H := by
    have h1 : Nat.card M ∣ Nat.card (C.subgroupOf (blkSub K)) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (C.subgroupOf (blkSub K)) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
    have h3 : Nat.card C ∣ Nat.card (H.map conjB) := Subgroup.card_dvd_of_le hCH
    have h4 : Nat.card (H.map conjB) = Nat.card H :=
      Subgroup.card_map_of_injective (MulAut.conj Bu⁻¹).injective
    rw [h2] at h1
    rw [← h4]
    exact h1.trans h3
  have h3M : ¬ 3 ∣ Nat.card M := fun h => h3 (h.trans hMH)
  have hmemM : ∀ (g : GL (Fin 3) K) (hgB : g ∈ blkSub K), g ∈ C →
      blkHom K ⟨g, hgB⟩ ∈ M := by
    intro g hgB hgC
    exact ⟨⟨g, hgB⟩, Subgroup.mem_subgroupOf.mpr hgC, rfl⟩
  have hu1 : blkHom K ⟨z', hz'B⟩ = u2 (φ ⬝ᵥ a') := by
    apply Subtype.ext
    rw [coe_blkHom, u2_coe]
    simp only [hzE'.2.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  have hu2 : blkHom K ⟨y', hy'B⟩ = u2 (c * (φ ⬝ᵥ a')) := by
    apply Subtype.ext
    rw [coe_blkHom, u2_coe]
    simp only [hyE'.2.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  have hl : blkHom K ⟨s', hs'B⟩ = l2 (φ' ⬝ᵥ a) := by
    apply Subtype.ext
    rw [coe_blkHom, l2_coe]
    simp only [hsE'.2.2.2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  have hzC : z' ∈ C := Subgroup.subset_closure (by simp)
  have hyC : y' ∈ C := Subgroup.subset_closure (by simp)
  have hsC : s' ∈ C := Subgroup.subset_closure (by simp)
  refine false_of_root_elements h3M h1 (mul_ne_zero hc0 h1) ?_ h2
    (hu1 ▸ hmemM z' hz'B hzC) (hu2 ▸ hmemM y' hy'B hyC) (hl ▸ hmemM s' hs'B hsC)
  intro h
  apply hc1
  have : (c - 1) * (φ ⬝ᵥ a') = 0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h1)

end KL3SubProof

end CFSG.RankThree.PartTwo.Sec16

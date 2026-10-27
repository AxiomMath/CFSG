module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsBasic
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepFactsRad
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.RankThree.Classical.SiegelRadical

public section

namespace CFSG.StandardType

namespace SUFacts

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution)

@[expose] def lo (i : Fin 3) : Fin 6 := ⟨i, by omega⟩

@[expose] def hi (i : Fin 3) : Fin 6 := ⟨3 + i, by omega⟩

theorem val_lo (i : Fin 3) : (lo i : ℕ) = i := rfl

theorem val_hi (i : Fin 3) : (hi i : ℕ) = 3 + i := rfl

theorem lo_injective : Function.Injective lo := fun i j h => Fin.ext (by
  have := congrArg Fin.val h
  rwa [val_lo, val_lo] at this)

theorem hi_injective : Function.Injective hi := fun i j h => by
  have := congrArg Fin.val h
  rw [val_hi, val_hi] at this
  exact Fin.ext (by omega)

theorem lo_ne_hi (i j : Fin 3) : lo i ≠ hi j := by
  intro h
  have := congrArg Fin.val h
  rw [val_lo, val_hi] at this
  have := i.isLt
  omega

theorem rev_lo (i : Fin 3) : Fin.rev (lo i) = hi (Fin.rev i) := by
  ext
  rw [Fin.val_rev, val_lo, val_hi, Fin.val_rev]
  have := i.isLt
  omega

theorem rev_hi (i : Fin 3) : Fin.rev (hi i) = lo (Fin.rev i) := by
  ext
  rw [Fin.val_rev, val_lo, val_hi, Fin.val_rev]
  have := i.isLt
  omega

theorem fin_six_cases (a : Fin 6) : (∃ i, a = lo i) ∨ ∃ i, a = hi i := by
  by_cases ha : (a : ℕ) < 3
  · exact Or.inl ⟨⟨a, ha⟩, Fin.ext rfl⟩
  · have := a.isLt
    exact Or.inr ⟨⟨(a : ℕ) - 3, by omega⟩, Fin.ext (by rw [val_hi]; simp only; omega)⟩

theorem sum_fin_six_split {M : Type*} [AddCommMonoid M] (f : Fin 6 → M) :
    ∑ c, f c = ∑ i : Fin 3, f (lo i) + ∑ i : Fin 3, f (hi i) :=
  Fin.sum_univ_add (a := 3) (b := 3) f

variable {F : Type} [Field F]

theorem mul_ggInvUNil_six_three_apply (G : Matrix (Fin 6) (Fin 6) F) (a b : Fin 6) :
    (G * ggInvUNil 6 3 F) a b = if (b : ℕ) < 3 then G a (Fin.rev b) else 0 := by
  rw [mul_apply]
  by_cases hb : (b : ℕ) < 3
  · rw [ite_eq_left hb, Finset.sum_eq_single (Fin.rev b)]
    · rw [ggInvUNil_apply, ite_eq_left ⟨hb, by rw [Fin.val_rev]; omega,
        by rw [Fin.val_rev]; omega⟩, mul_one]
    · intro c _ hc
      rw [ggInvUNil_apply, ite_eq_right (fun h => hc (Fin.ext (by rw [Fin.val_rev]; omega))),
        mul_zero]
    · simp
  · rw [ite_eq_right hb]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [ggInvUNil_apply, ite_eq_right (fun h => hb h.1), mul_zero]

theorem ggInvUNil_six_three_mul_apply (G : Matrix (Fin 6) (Fin 6) F) (a b : Fin 6) :
    (ggInvUNil 6 3 F * G) a b = if 3 ≤ (a : ℕ) then G (Fin.rev a) b else 0 := by
  rw [mul_apply]
  by_cases ha : 3 ≤ (a : ℕ)
  · rw [ite_eq_left ha, Finset.sum_eq_single (Fin.rev a)]
    · have := a.isLt
      rw [ggInvUNil_apply, ite_eq_left ⟨by rw [Fin.val_rev]; omega, by rw [Fin.val_rev]; omega,
        by rw [Fin.val_rev]; omega⟩, one_mul]
    · intro c _ hc
      rw [ggInvUNil_apply, ite_eq_right (fun h => hc (Fin.ext (by rw [Fin.val_rev]; omega))),
        zero_mul]
    · simp
  · rw [ite_eq_right ha]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [ggInvUNil_apply, ite_eq_right (fun h => ha (by omega)), zero_mul]

theorem cent_blocks {G : Matrix (Fin 6) (Fin 6) F}
    (h : G * ggInvUMatrix 6 3 F = ggInvUMatrix 6 3 F * G) :
    (∀ i j, G (lo i) (hi j) = 0) ∧ ∀ i j, G (hi i) (hi j) = G (lo (Fin.rev i)) (lo (Fin.rev j)) := by
  have hN : G * ggInvUNil 6 3 F = ggInvUNil 6 3 F * G := by
    rw [ggInvUMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun (congrFun hN (lo i)) (lo (Fin.rev j))
    rw [mul_ggInvUNil_six_three_apply, ggInvUNil_six_three_mul_apply,
      ite_eq_left (by rw [val_lo]; exact (Fin.rev j).isLt),
      ite_eq_right (by rw [val_lo]; have := i.isLt; omega), rev_lo, Fin.rev_rev] at e
    exact e
  · have e := congrFun (congrFun hN (hi i)) (lo (Fin.rev j))
    rw [mul_ggInvUNil_six_three_apply, ggInvUNil_six_three_mul_apply,
      ite_eq_left (by rw [val_lo]; exact (Fin.rev j).isLt), ite_eq_left (by rw [val_hi]; omega),
      rev_lo, Fin.rev_rev, rev_hi] at e
    exact e

theorem commute_of_blocks {G : Matrix (Fin 6) (Fin 6) F} (h1 : ∀ i j, G (lo i) (hi j) = 0)
    (h2 : ∀ i j, G (hi i) (hi j) = G (lo (Fin.rev i)) (lo (Fin.rev j))) :
    G * ggInvUMatrix 6 3 F = ggInvUMatrix 6 3 F * G := by
  rw [ggInvUMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  rw [mul_ggInvUNil_six_three_apply, ggInvUNil_six_three_mul_apply]
  rcases fin_six_cases a with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases fin_six_cases b with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [ite_eq_left (by rw [val_lo]; exact j.isLt), ite_eq_right (by rw [val_lo]; have := i.isLt; omega),
      rev_lo, h1]
  · rw [ite_eq_right (by rw [val_hi]; omega), ite_eq_right (by rw [val_lo]; have := i.isLt; omega)]
  · rw [ite_eq_left (by rw [val_lo]; exact j.isLt), ite_eq_left (by rw [val_hi]; omega), rev_lo,
      rev_hi, h2, Fin.rev_rev]
  · rw [ite_eq_right (by rw [val_hi]; omega), ite_eq_left (by rw [val_hi]; omega), rev_hi, h1]

@[expose] def blockA (G : Matrix (Fin 6) (Fin 6) F) : Matrix (Fin 3) (Fin 3) F := G.submatrix lo lo

omit [Field F] in
theorem blockA_apply (G : Matrix (Fin 6) (Fin 6) F) (i j : Fin 3) : blockA G i j = G (lo i) (lo j) :=
  rfl

theorem blockA_mul {G G' : Matrix (Fin 6) (Fin 6) F} (h1 : ∀ i j, G (lo i) (hi j) = 0) :
    blockA (G * G') = blockA G * blockA G' := by
  ext i j
  rw [blockA_apply, mul_apply, sum_fin_six_split, mul_apply]
  have hz : ∑ k : Fin 3, G (lo i) (hi k) * G' (hi k) (lo j) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [h1, zero_mul]
  rw [hz, add_zero]
  rfl

theorem blockA_one : blockA (1 : Matrix (Fin 6) (Fin 6) F) = 1 := by
  ext i j
  rw [blockA_apply, one_apply, one_apply]
  by_cases hij : i = j
  · subst hij; rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right (fun h => hij (lo_injective h)), ite_eq_right hij]

theorem det_eq_det_blockA_sq {G : Matrix (Fin 6) (Fin 6) F} (h1 : ∀ i j, G (lo i) (hi j) = 0)
    (h2 : ∀ i j, G (hi i) (hi j) = G (lo (Fin.rev i)) (lo (Fin.rev j))) :
    G.det = (blockA G).det ^ 2 := by
  have e : G.submatrix (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6)
      (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) =
      fromBlocks (blockA G) 0 (G.submatrix hi lo) ((blockA G).submatrix Fin.revPerm Fin.revPerm) := by
    ext (i | i) (j | j)
    · rfl
    · exact h1 i j
    · rfl
    · exact h2 i j
  rw [← det_submatrix_equiv_self (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) G, e,
    det_fromBlocks_zero₁₂, det_submatrix_equiv_self Fin.revPerm (blockA G), sq]

variable (σ : F ≃+* F)

theorem blockA_unitary {G : Matrix (Fin 6) (Fin 6) F} (h1 : ∀ i j, G (lo i) (hi j) = 0)
    (h2 : ∀ i j, G (hi i) (hi j) = G (lo (Fin.rev i)) (lo (Fin.rev j)))
    (hU : conjTr σ G * antidiag 6 * G = antidiag 6) :
    ((blockA G).map σ)ᵀ * blockA G = 1 := by
  ext i j
  have e := congrFun (congrFun hU (lo i)) (hi (Fin.rev j))
  rw [conjTr_antidiag_mul_apply, sum_fin_six_split,
    Finset.sum_eq_zero (fun k _ => by rw [h1, mul_zero]), zero_add, antidiag, of_apply, rev_lo] at e
  have hs : ∑ k : Fin 3, σ (G (Fin.rev (hi k)) (lo i)) * G (hi k) (hi (Fin.rev j)) =
      ∑ m : Fin 3, σ (blockA G m i) * blockA G m j := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [rev_hi, h2, Fin.rev_rev, Fin.revPerm_apply, blockA_apply]
  rw [hs] at e
  rw [mul_apply, one_apply]
  simp only [transpose_apply, map_apply]
  rw [e]
  by_cases hij : i = j
  · subst hij; simp
  · have : hi (Fin.rev j) ≠ hi (Fin.rev i) := fun h => hij (Fin.rev_injective (hi_injective h)).symm
    rw [ite_eq_right this, ite_eq_right hij]

theorem isometry_of_blocks {G : Matrix (Fin 6) (Fin 6) F} (h1 : ∀ i j, G (lo i) (hi j) = 0)
    (h2 : ∀ i j, G (hi i) (hi j) = G (lo (Fin.rev i)) (lo (Fin.rev j)))
    (hA : ((blockA G).map σ)ᵀ * blockA G = 1)
    (hC : ∀ i j, ∑ k : Fin 3, σ (G (hi (Fin.rev k)) (lo i)) * G (lo k) (lo j) +
      ∑ k : Fin 3, σ (G (lo (Fin.rev k)) (lo i)) * G (hi k) (lo j) = 0) :
    conjTr σ G * antidiag 6 * G = antidiag 6 := by
  have hAe : ∀ i j, ∑ k : Fin 3, σ (G (lo k) (lo i)) * G (lo k) (lo j) =
      (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    have := congrFun (congrFun hA i) j
    rw [mul_apply] at this
    simpa only [transpose_apply, map_apply, blockA_apply] using this
  have hrev : ∀ i j, ∑ k : Fin 3, σ (G (lo (Fin.rev k)) (lo i)) * G (lo (Fin.rev k)) (lo j) =
      (1 : Matrix (Fin 3) (Fin 3) F) i j := by
    intro i j
    rw [← hAe i j, ← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.rev_rev]
  ext x y
  rw [conjTr_antidiag_mul_apply, sum_fin_six_split, antidiag, of_apply]
  simp only [rev_lo, rev_hi]
  rcases fin_six_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases fin_six_cases y with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [hC i j, rev_lo, ite_eq_right (lo_ne_hi j _)]
  · have e1 : ∑ k : Fin 3, σ (G (hi (Fin.rev k)) (lo i)) * G (lo k) (hi j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [h1, mul_zero]
    have e2 : ∑ k : Fin 3, σ (G (lo (Fin.rev k)) (lo i)) * G (hi k) (hi j) =
        (1 : Matrix (Fin 3) (Fin 3) F) i (Fin.rev j) := by
      rw [← hrev i (Fin.rev j)]
      exact Finset.sum_congr rfl fun k _ => by rw [h2]
    rw [e1, e2, zero_add, rev_lo, one_apply]
    by_cases hij : i = Fin.rev j
    · rw [ite_eq_left hij, ite_eq_left (by rw [hij, Fin.rev_rev])]
    · rw [ite_eq_right hij, ite_eq_right (fun h => hij (by rw [hi_injective h, Fin.rev_rev]))]
  · have e1 : ∑ k : Fin 3, σ (G (hi (Fin.rev k)) (hi i)) * G (lo k) (lo j) =
        (1 : Matrix (Fin 3) (Fin 3) F) (Fin.rev i) j := by
      rw [← hAe (Fin.rev i) j]
      exact Finset.sum_congr rfl fun k _ => by rw [h2, Fin.rev_rev]
    have e2 : ∑ k : Fin 3, σ (G (lo (Fin.rev k)) (hi i)) * G (hi k) (lo j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [h1, map_zero, zero_mul]
    rw [e1, e2, add_zero, rev_hi, one_apply]
    by_cases hij : Fin.rev i = j
    · rw [ite_eq_left hij, ite_eq_left (by rw [hij])]
    · rw [ite_eq_right hij, ite_eq_right (fun h => hij (lo_injective h).symm)]
  · have e1 : ∑ k : Fin 3, σ (G (hi (Fin.rev k)) (hi i)) * G (lo k) (hi j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [h1, mul_zero]
    have e2 : ∑ k : Fin 3, σ (G (lo (Fin.rev k)) (hi i)) * G (hi k) (hi j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [h1, map_zero, zero_mul]
    rw [e1, e2, add_zero, rev_hi, ite_eq_right (fun h => lo_ne_hi _ j h.symm)]

section Pi

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ}

theorem bar_eq_unitaryInvolution (h : UnitaryFieldData 2 a F) (c : F) :
    h.bar c = unitaryInvolution F 2 a c := by
  rw [UnitaryFieldData.bar_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]

theorem blocks_of_mem_centralizer {g : SU (unitaryInvolution F 2 a) 6}
    (hg : g ∈ Subgroup.centralizer {ggInvSU (unitaryInvolution F 2 a) 6 3}) :
    (∀ i j, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) (lo i) (hi j) = 0) ∧
      ∀ i j, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) (hi i) (hi j) =
        ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) (lo (Fin.rev i)) (lo (Fin.rev j)) := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hm := congrArg (fun x : SU (unitaryInvolution F 2 a) 6 =>
    ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hc
  simp only [Subgroup.coe_mul, Units.val_mul,
    coe_ggInvSU (unitaryInvolution F 2 a) (show 2 * 3 ≤ 6 by norm_num)] at hm
  exact cent_blocks hm

theorem blockA_mem_unitarySU (h : UnitaryFieldData 2 a F) {g : SU (unitaryInvolution F 2 a) 6}
    (hg : g ∈ Subgroup.centralizer {ggInvSU (unitaryInvolution F 2 a) 6 3})
    {A : GL (Fin 3) F} (hA : (A : Matrix (Fin 3) (Fin 3) F) =
      blockA ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) :
    A ∈ unitarySU 2 a F 3 := by
  obtain ⟨h1, h2⟩ := blocks_of_mem_centralizer hg
  rw [mem_unitarySU_iff h, hA]
  refine ⟨?_, ?_⟩
  · have hd := det_eq_det_blockA_sq h1 h2
    rw [g.2.1] at hd
    exact (CharTwo.sq_inj (R := F)).mp (by rw [one_pow]; exact hd.symm)
  · have hmap : (blockA ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)).map h.bar =
        (blockA ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)).map
          (unitaryInvolution F 2 a) := by
      ext i j
      exact bar_eq_unitaryInvolution h _
    rw [hmap]
    exact blockA_unitary _ h1 h2 g.2.2

variable (F a) in
noncomputable abbrev centT : Subgroup (SU (unitaryInvolution F 2 a) 6) :=
  Subgroup.centralizer {ggInvSU (unitaryInvolution F 2 a) 6 3}

noncomputable abbrev centMat (g : centT F a) : Matrix (Fin 6) (Fin 6) F :=
  (((g : SU (unitaryInvolution F 2 a) 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)

theorem centMat_mul (g g' : centT F a) : centMat (g * g') = centMat g * centMat g' := rfl

theorem centMat_one : centMat (1 : centT F a) = 1 := rfl

theorem centMat_mul_inv (g : centT F a) : centMat g * centMat g⁻¹ = 1 := by
  rw [← centMat_mul, mul_inv_cancel, centMat_one]

theorem centMat_inv_mul (g : centT F a) : centMat g⁻¹ * centMat g = 1 := by
  rw [← centMat_mul, inv_mul_cancel, centMat_one]

@[expose] noncomputable def centPiGL (g : centT F a) : GL (Fin 3) F :=
  ⟨blockA (centMat g), blockA (centMat g⁻¹),
    by rw [← blockA_mul (blocks_of_mem_centralizer g.2).1, centMat_mul_inv, blockA_one],
    by rw [← blockA_mul (blocks_of_mem_centralizer g⁻¹.2).1, centMat_inv_mul, blockA_one]⟩

variable (h : UnitaryFieldData 2 a F)

@[expose] noncomputable def centPi : centT F a →* unitarySU 2 a F 3 where
  toFun g := ⟨centPiGL g, blockA_mem_unitarySU h g.2 rfl⟩
  map_one' := Subtype.ext (Units.ext blockA_one)
  map_mul' g g' := Subtype.ext (Units.ext (by
    change blockA (centMat (g * g')) = blockA (centMat g) * blockA (centMat g')
    rw [centMat_mul, blockA_mul (blocks_of_mem_centralizer g.2).1]))

theorem matrix_centPi (g : centT F a) :
    (((centPi h g : unitarySU 2 a F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      blockA (centMat g) := rfl

end Pi

section BlockMat

variable {F : Type} [Field F]

@[expose] def blockMat (A B C D : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  (fromBlocks A B C D).submatrix (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm
    (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm

theorem symm_lo (i : Fin 3) : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm (lo i) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

theorem symm_hi (i : Fin 3) : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm (hi i) = Sum.inr i :=
  finSumFinEquiv_symm_apply_natAdd i

omit [Field F] in
theorem blockMat_lo_lo (A B C D : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    blockMat A B C D (lo i) (lo j) = A i j := by
  rw [blockMat, submatrix_apply, symm_lo, symm_lo, fromBlocks_apply₁₁]

omit [Field F] in
theorem blockMat_lo_hi (A B C D : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    blockMat A B C D (lo i) (hi j) = B i j := by
  rw [blockMat, submatrix_apply, symm_lo, symm_hi, fromBlocks_apply₁₂]

omit [Field F] in
theorem blockMat_hi_lo (A B C D : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    blockMat A B C D (hi i) (lo j) = C i j := by
  rw [blockMat, submatrix_apply, symm_hi, symm_lo, fromBlocks_apply₂₁]

omit [Field F] in
theorem blockMat_hi_hi (A B C D : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    blockMat A B C D (hi i) (hi j) = D i j := by
  rw [blockMat, submatrix_apply, symm_hi, symm_hi, fromBlocks_apply₂₂]

theorem blockMat_mul (A B C D A' B' C' D' : Matrix (Fin 3) (Fin 3) F) :
    blockMat A B C D * blockMat A' B' C' D' =
      blockMat (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  rw [blockMat, blockMat, submatrix_mul_equiv, fromBlocks_multiply]
  rfl

theorem blockMat_one : blockMat (1 : Matrix (Fin 3) (Fin 3) F) 0 0 1 = 1 := by
  rw [blockMat, fromBlocks_one, submatrix_one_equiv]

@[expose] def deltaMat (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  blockMat A 0 0 (A.submatrix Fin.revPerm Fin.revPerm)

theorem deltaMat_mul (A A' : Matrix (Fin 3) (Fin 3) F) :
    deltaMat (A * A') = deltaMat A * deltaMat A' := by
  rw [deltaMat, deltaMat, deltaMat, blockMat_mul, submatrix_mul_equiv]
  simp

theorem deltaMat_one : deltaMat (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [deltaMat, submatrix_one_equiv, blockMat_one]

theorem blockA_deltaMat (A : Matrix (Fin 3) (Fin 3) F) : blockA (deltaMat A) = A := by
  ext i j
  rw [blockA_apply, deltaMat, blockMat_lo_lo]

theorem deltaMat_blocks (A : Matrix (Fin 3) (Fin 3) F) :
    (∀ i j, deltaMat A (lo i) (hi j) = 0) ∧
      ∀ i j, deltaMat A (hi i) (hi j) = deltaMat A (lo (Fin.rev i)) (lo (Fin.rev j)) :=
  ⟨fun i j => by rw [deltaMat, blockMat_lo_hi, Matrix.zero_apply],
    fun i j => by rw [deltaMat, blockMat_hi_hi, blockMat_lo_lo, submatrix_apply]; rfl⟩

@[expose] def uMat (X : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  blockMat 1 0 (X.submatrix Fin.revPerm id) 1

theorem uMat_blocks (X : Matrix (Fin 3) (Fin 3) F) :
    (∀ i j, uMat X (lo i) (hi j) = 0) ∧
      ∀ i j, uMat X (hi i) (hi j) = uMat X (lo (Fin.rev i)) (lo (Fin.rev j)) :=
  ⟨fun i j => by rw [uMat, blockMat_lo_hi, Matrix.zero_apply],
    fun i j => by
      rw [uMat, blockMat_hi_hi, blockMat_lo_lo, one_apply, one_apply]
      by_cases hij : i = j
      · subst hij; rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hij, ite_eq_right (fun h => hij (Fin.rev_injective h))]⟩

theorem blockA_uMat (X : Matrix (Fin 3) (Fin 3) F) : blockA (uMat X) = 1 := by
  ext i j
  rw [blockA_apply, uMat, blockMat_lo_lo]

theorem uMat_hi_lo (X : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    uMat X (hi (Fin.rev i)) (lo j) = X i j := by
  rw [uMat, blockMat_hi_lo, submatrix_apply, Fin.revPerm_apply, Fin.rev_rev, id]

theorem uMat_mul_self [CharP F 2] (X : Matrix (Fin 3) (Fin 3) F) : uMat X * uMat X = 1 := by
  rw [uMat, blockMat_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [CharTwo.add_self_eq_zero, blockMat_one]

end BlockMat

section Levi

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.RankThree.Classical (skewHermMatrices mem_skewHermMatrices_iff card_skewHermMatrices)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} (h : UnitaryFieldData 2 a F)
include h

theorem deltaMat_mem_SU {A : GL (Fin 3) F} (hA : A ∈ unitarySU 2 a F 3) :
    (deltaMat (A : Matrix (Fin 3) (Fin 3) F)).det = 1 ∧
      conjTr (unitaryInvolution F 2 a) (deltaMat (A : Matrix (Fin 3) (Fin 3) F)) * antidiag 6 *
        deltaMat (A : Matrix (Fin 3) (Fin 3) F) = antidiag 6 := by
  obtain ⟨hd, hu⟩ := (mem_unitarySU_iff h).mp hA
  obtain ⟨h1, h2⟩ := deltaMat_blocks (A : Matrix (Fin 3) (Fin 3) F)
  refine ⟨by rw [det_eq_det_blockA_sq h1 h2, blockA_deltaMat, hd, one_pow], ?_⟩
  refine isometry_of_blocks _ h1 h2 ?_ fun i j => ?_
  · rw [blockA_deltaMat]
    have hmap : (A : Matrix (Fin 3) (Fin 3) F).map (unitaryInvolution F 2 a) =
        (A : Matrix (Fin 3) (Fin 3) F).map h.bar := by
      ext i j
      exact (bar_eq_unitaryInvolution h _).symm
    rw [hmap, hu]
  · have e1 : ∑ k : Fin 3, unitaryInvolution F 2 a (deltaMat (A : Matrix (Fin 3) (Fin 3) F)
        (hi (Fin.rev k)) (lo i)) * deltaMat (A : Matrix (Fin 3) (Fin 3) F) (lo k) (lo j) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [deltaMat, blockMat_hi_lo, Matrix.zero_apply, map_zero, zero_mul]
    have e2 : ∑ k : Fin 3, unitaryInvolution F 2 a (deltaMat (A : Matrix (Fin 3) (Fin 3) F)
        (lo (Fin.rev k)) (lo i)) * deltaMat (A : Matrix (Fin 3) (Fin 3) F) (hi k) (lo j) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [deltaMat, blockMat_hi_lo, Matrix.zero_apply, mul_zero]
    rw [e1, e2, add_zero]

@[expose] noncomputable def deltaSU (A : unitarySU 2 a F 3) : SU (unitaryInvolution F 2 a) 6 :=
  ⟨⟨deltaMat ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
      deltaMat (((A : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
      by rw [← deltaMat_mul, Units.mul_inv, deltaMat_one],
      by rw [← deltaMat_mul, Units.inv_mul, deltaMat_one]⟩,
    deltaMat_mem_SU h A.2⟩

theorem deltaSU_mem_centT (A : unitarySU 2 a F 3) : deltaSU h A ∈ centT F a := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    coe_ggInvSU (unitaryInvolution F 2 a) (show 2 * 3 ≤ 6 by norm_num)]
  obtain ⟨h1, h2⟩ := deltaMat_blocks ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  exact commute_of_blocks h1 h2

@[expose] noncomputable def centDelta : unitarySU 2 a F 3 →* centT F a where
  toFun A := ⟨deltaSU h A, deltaSU_mem_centT h A⟩
  map_one' := Subtype.ext (Subtype.ext (Units.ext deltaMat_one))
  map_mul' A B := Subtype.ext (Subtype.ext (Units.ext (by
    change deltaMat ((((A * B : unitarySU 2 a F 3) : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      deltaMat (((A : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *
        deltaMat (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)
    rw [← deltaMat_mul]
    rfl)))

theorem centMat_centDelta (A : unitarySU 2 a F 3) :
    centMat (centDelta h A) = deltaMat ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl

theorem centPi_centDelta (A : unitarySU 2 a F 3) : centPi h (centDelta h A) = A :=
  Subtype.ext (Units.ext (by rw [matrix_centPi, centMat_centDelta, blockA_deltaMat]))

theorem uMat_mem_SU {X : Matrix (Fin 3) (Fin 3) F} (hX : X ∈ skewHermMatrices h 3) :
    (uMat X).det = 1 ∧ conjTr (unitaryInvolution F 2 a) (uMat X) * antidiag 6 * uMat X =
      antidiag 6 := by
  obtain ⟨h1, h2⟩ := uMat_blocks X
  refine ⟨by rw [det_eq_det_blockA_sq h1 h2, blockA_uMat, det_one, one_pow], ?_⟩
  refine isometry_of_blocks _ h1 h2 ?_ fun i j => ?_
  · rw [blockA_uMat]
    ext i j
    simp [one_apply]
  · have hXij := (mem_skewHermMatrices_iff h).mp hX i j
    rw [bar_eq_unitaryInvolution h] at hXij
    have e1 : ∑ k : Fin 3, unitaryInvolution F 2 a (uMat X (hi (Fin.rev k)) (lo i)) *
        uMat X (lo k) (lo j) = unitaryInvolution F 2 a (X j i) := by
      rw [Finset.sum_eq_single j]
      · rw [uMat_hi_lo, uMat, blockMat_lo_lo, one_apply_eq, mul_one]
      · intro k _ hk
        rw [uMat, blockMat_lo_lo, one_apply_ne hk, mul_zero]
      · simp
    have e2 : ∑ k : Fin 3, unitaryInvolution F 2 a (uMat X (lo (Fin.rev k)) (lo i)) *
        uMat X (hi k) (lo j) = X i j := by
      rw [Finset.sum_eq_single (Fin.rev i)]
      · rw [Fin.rev_rev, uMat, blockMat_lo_lo, one_apply_eq, map_one, one_mul, ← uMat,
          uMat_hi_lo]
      · intro k _ hk
        rw [uMat, blockMat_lo_lo, one_apply_ne (fun h' => hk (by rw [← h', Fin.rev_rev])),
          map_zero, zero_mul]
      · simp
    rw [e1, e2, add_comm, hXij]

@[expose] noncomputable def uSU {X : Matrix (Fin 3) (Fin 3) F} (hX : X ∈ skewHermMatrices h 3) :
    SU (unitaryInvolution F 2 a) 6 :=
  ⟨⟨uMat X, uMat X, uMat_mul_self X, uMat_mul_self X⟩, uMat_mem_SU h hX⟩

theorem uSU_mem_centT {X : Matrix (Fin 3) (Fin 3) F} (hX : X ∈ skewHermMatrices h 3) :
    uSU h hX ∈ centT F a := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    coe_ggInvSU (unitaryInvolution F 2 a) (show 2 * 3 ≤ 6 by norm_num)]
  obtain ⟨h1, h2⟩ := uMat_blocks X
  exact commute_of_blocks h1 h2

theorem card_ker_centPi_ge : 2 ^ (9 * a) ≤ Nat.card (centPi h).ker := by
  have hc := card_skewHermMatrices (r := 3) h
  rw [← pow_mul, show a * 3 ^ 2 = 9 * a by ring] at hc
  rw [← hc]
  refine Nat.card_le_card_of_injective (fun X => ⟨⟨uSU h X.2, uSU_mem_centT h X.2⟩, ?_⟩) ?_
  · rw [MonoidHom.mem_ker]
    exact Subtype.ext (Units.ext (by
      rw [matrix_centPi]
      exact blockA_uMat _))
  · intro X Y hXY
    have hm := congrArg (fun g : (centPi h).ker => centMat (g : centT F a)) hXY
    change uMat (X : Matrix (Fin 3) (Fin 3) F) = uMat (Y : Matrix (Fin 3) (Fin 3) F) at hm
    apply Subtype.ext
    ext i j
    have := congrFun (congrFun hm (hi (Fin.rev i))) (lo j)
    rwa [uMat_hi_lo, uMat_hi_lo] at this

end Levi

end SUFacts

end CFSG.StandardType

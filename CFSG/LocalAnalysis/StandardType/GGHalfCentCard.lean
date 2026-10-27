module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentDefs

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL CFSG.RankThree.CALinearPlane Matrix

private theorem centCard_card_coordBlockSL {n : ℕ} {K : Type*} [Field K] (J : Finset (Fin n)) :
    Nat.card (coordBlockSL K J) = Nat.card (SpecialLinearGroup (Fin J.card) K) :=
  (Nat.card_congr ((MonoidHom.ofInjective (blockSLOn_injective (k := K) J)).trans
    (MulEquiv.subgroupCongr (range_blockSLOn (k := K) J))).toEquiv).symm

theorem natCard_zeroBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) :
    Nat.card (zeroBlk ε k) = Nat.card (SpecialLinearGroup (Fin (n + 1 - 2 * ones k)) F2) := by
  have hJ := card_zeroCoords ε k hk
  unfold zeroBlk
  rw [centCard_card_coordBlockSL (K := F2) (n := n + 1), hJ]

private noncomputable def centCard_SL_ringEquiv {K K' : Type*} [Field K] [Field K']
    (m : ℕ) (e : K ≃+* K') :
    SpecialLinearGroup (Fin m) K ≃* SpecialLinearGroup (Fin m) K' where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply (A i j)
  right_inv A := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (A i j)
  map_mul' := map_mul _

private theorem centCard_card_SL_field_eq {m : ℕ} {K K' : Type*} [Field K] [Field K']
    [Finite K] [Finite K'] (h : Nat.card K = Nat.card K') :
    Nat.card (SpecialLinearGroup (Fin m) K) = Nat.card (SpecialLinearGroup (Fin m) K') := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K' := Fintype.ofFinite K'
  have h' : Fintype.card K = Fintype.card K' := by
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    (centCard_SL_ringEquiv m (FiniteField.ringEquivOfCardEq h')).toEquiv

theorem natCard_classBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) :
    Nat.card (classBlk ε k) =
      Nat.card (SpecialLinearGroup (Fin (ones k)) (GaloisField 2 2)) := by
  have hS := card_classSet k hk
  haveI : Finite (AdjoinRoot phi3) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_adjoinRoot_phi3]; norm_num)
  have hmap : Nat.card (classBlk ε k) =
      Nat.card (coordBlockSL (AdjoinRoot phi3) (classSet (fun i => (k i : ZMod 3)) 1)) := by
    unfold classBlk
    exact Subgroup.card_map_of_injective (theta_injective (g := phi3) (ε := ε))
  have hcard0 :
      Nat.card (coordBlockSL (AdjoinRoot phi3) (classSet (fun i => (k i : ZMod 3)) 1)) =
        Nat.card (SpecialLinearGroup
          (Fin (classSet (fun i => (k i : ZMod 3)) 1).card) (AdjoinRoot phi3)) :=
    centCard_card_coordBlockSL (K := AdjoinRoot phi3) (n := s) _
  have hcard1 :
      Nat.card (SpecialLinearGroup (Fin (classSet (fun i => (k i : ZMod 3)) 1).card)
        (AdjoinRoot phi3)) =
        Nat.card (SpecialLinearGroup (Fin (ones k)) (AdjoinRoot phi3)) := by rw [hS]
  exact hmap.trans (hcard0.trans (hcard1.trans (centCard_card_SL_field_eq (m := ones k)
    (by rw [natCard_adjoinRoot_phi3, GaloisField.card 2 2 (by omega)]; norm_num))))

private theorem centCard_theta_col_not_mem {n s r : ℕ}
    {ε : Fin n ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r}
    {S : Finset (Fin s)} {M : SpecialLinearGroup (Fin s) (AdjoinRoot phi3)}
    (hM : M ∈ coordBlockSL (AdjoinRoot phi3) S) {i : Fin s} (hi : i ∉ S)
    (a : Fin (rootPB phi3).dim) (x : Fin n) :
    (theta phi3 ε M : Matrix (Fin n) (Fin n) F2) x (ε.symm (Sum.inl (a, i))) =
      if x = ε.symm (Sum.inl (a, i)) then 1 else 0 := by
  classical
  have hfix : (M : Matrix (Fin s) (Fin s) (AdjoinRoot phi3)) *ᵥ
      (Pi.single i ((rootPB phi3).basis a) : Fin s → AdjoinRoot phi3) =
      Pi.single i ((rootPB phi3).basis a) := by
    funext i'
    rw [mulVec_single_apply', mem_coordBlockSL_iff.mp hM i' i (Or.inr hi)]
    by_cases h : i' = i <;> simp [h]
  have hx : frameCoords phi3 ε
      ((Pi.single i ((rootPB phi3).basis a) : Fin s → AdjoinRoot phi3), (0 : Fin r → F2)) =
      Pi.single (ε.symm (Sum.inl (a, i))) 1 :=
    frameCoords_single_basis (g := phi3) ε a i
  have h := frameCoords_frameForm (g := phi3) (ε := ε)
    (u := (theta phi3 ε M : Matrix (Fin n) (Fin n) F2))
    ((Pi.single i ((rootPB phi3).basis a) : Fin s → AdjoinRoot phi3), (0 : Fin r → F2))
  rw [coe_theta, frameForm_thetaMat, blockAct_apply, hfix, hx] at h
  have h2 := congrFun h.symm x
  rw [Matrix.mulVec_single_one] at h2
  simpa [coe_theta, Matrix.col_apply, Pi.single_apply] using h2

private theorem centCard_theta_col_inr {n s r : ℕ}
    {ε : Fin n ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r}
    {M : SpecialLinearGroup (Fin s) (AdjoinRoot phi3)}
    (j : Fin r) (x : Fin n) :
    (theta phi3 ε M : Matrix (Fin n) (Fin n) F2) x (ε.symm (Sum.inr j)) =
      if x = ε.symm (Sum.inr j) then 1 else 0 := by
  classical
  have hx : frameCoords phi3 ε
      ((0 : Fin s → AdjoinRoot phi3), (Pi.single j 1 : Fin r → F2)) =
      Pi.single (ε.symm (Sum.inr j)) 1 := by
    funext y
    rw [frameCoords_apply]
    have h1 : y = ε.symm (Sum.inr j) ↔ ε y = Sum.inr j := Equiv.eq_symm_apply ε
    rcases hy : ε y with ⟨a', i'⟩ | j'
    · rw [hy] at h1
      have hyc : y ≠ ε.symm (Sum.inr j) := by rw [ne_eq, h1]; simp
      simp [Sum.elim_inl, hyc]
    · rw [hy] at h1
      simp only [Sum.elim_inr, Pi.single_apply, h1]
      by_cases hj : j' = j <;> simp [hj]
  have h := frameCoords_frameForm (g := phi3) (ε := ε)
    (u := (theta phi3 ε M : Matrix (Fin n) (Fin n) F2))
    ((0 : Fin s → AdjoinRoot phi3), (Pi.single j 1 : Fin r → F2))
  rw [coe_theta, frameForm_thetaMat, blockAct_apply] at h
  simp only [Matrix.mulVec_zero] at h
  rw [hx] at h
  have h2 := congrFun h.symm x
  rw [Matrix.mulVec_single_one] at h2
  simpa [coe_theta, Matrix.col_apply, Pi.single_apply] using h2

theorem disjoint_zeroBlk_classBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ) :
    Disjoint (zeroBlk ε k) (classBlk ε k) := by
  classical
  rw [Subgroup.disjoint_def]
  intro g hgZ hgC
  unfold zeroBlk at hgZ
  unfold classBlk at hgC
  rw [Subgroup.mem_map] at hgC
  obtain ⟨M, hM, hMg⟩ := hgC
  have hZ := mem_coordBlockSL_iff.mp hgZ
  have hstep : ∀ i j, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) i j =
      if i = j then 1 else 0 := by
    intro i j
    by_cases hj : j ∈ zeroCoords ε (fun i => (k i : ZMod 3))
    · rw [← hMg]
      rcases hje : ε j with ⟨a, jj⟩ | jj
      · have hβ : ((k jj : ZMod 3)) = 0 := (mem_zeroCoords_inl hje).mp hj
        have hjj : jj ∉ classSet (fun i => (k i : ZMod 3)) 1 := by
          rw [mem_classSet, hβ]
          exact zero_ne_one
        have hj_eq : j = ε.symm (Sum.inl (a, jj)) := by
          rw [← hje, Equiv.symm_apply_apply]
        rw [hj_eq, centCard_theta_col_not_mem hM hjj a i]
      · have hj_eq : j = ε.symm (Sum.inr jj) := by
          rw [← hje, Equiv.symm_apply_apply]
        rw [hj_eq, centCard_theta_col_inr (M := M) jj i]
    · rw [hZ i j (Or.inr hj)]
  apply Subtype.ext
  ext i j
  rw [hstep i j, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]

end CFSG.StandardType.GGHalf

end

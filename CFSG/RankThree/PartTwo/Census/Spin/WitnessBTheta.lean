module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierBTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessB

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierB

open TauCeti TauCeti.TypeBSpinCarrier Cliff RootData

section Generic

variable {n : ℕ} {K : Type} [Field K]

theorem fin_ne_of_val {m : ℕ} {a b : Fin m} (h : a.val ≠ b.val) : a ≠ b :=
  fun h' => h (by rw [h'])

theorem commute_block {i k : Fin (n + 1)} (hik : i ≠ k)
    {A B C D : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hA : IsIntOp n (crB n i * anB n k) A) (hB : IsIntOp n (crB n k * anB n i) B)
    (hC : IsIntOp n (crB n i * crB n k) C) (hD : IsIntOp n (anB n k * anB n i) D) :
    Commute (intMap K C) (intMap K A) ∧ Commute (intMap K C) (intMap K B) ∧
      Commute (intMap K D) (intMap K A) ∧ Commute (intMap K D) (intMap K B) :=
  ⟨intMap_commute_of hC hA ((P_E _).trans (E_P _ hik).symm),
    intMap_commute_of hC hB ((P_F _).trans (F_P _ hik).symm),
    intMap_commute_of hD hA ((N_E _ hik).trans (E_N _).symm),
    intMap_commute_of hD hB ((N_F _ hik).trans (F_N _).symm)⟩

theorem commute_of_two_le (j : Fin (n + 1)) (hj : 2 ≤ j.val) {x y x' y' : Fin (n + 1)}
    (hx : x.val < 2) (hy : y.val < 2) (hx' : x'.val < 2) (hy' : y'.val < 2)
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crB n x * crB n y) X) (hY : IsIntOp n (anB n x' * anB n y') Y) :
    Commute (intMap K X) ((rootData n K).E j) ∧ Commute (intMap K X) ((rootData n K).F j) ∧
      Commute (intMap K Y) ((rootData n K).E j) ∧ Commute (intMap K Y) ((rootData n K).F j) := by
  have h1 : x ≠ j := fin_ne_of_val (by omega)
  have h2 : y ≠ j := fin_ne_of_val (by omega)
  have h1' : x' ≠ j := fin_ne_of_val (by omega)
  have h2' : y' ≠ j := fin_ne_of_val (by omega)
  by_cases hjn : j.val < n
  · have hE := isIntOp_E_lt n j hjn
    have hF := isIntOp_F_lt n j hjn
    have h3 : x ≠ ⟨j.val + 1, by omega⟩ := fin_ne_of_val (by simp only; omega)
    have h4 : y ≠ ⟨j.val + 1, by omega⟩ := fin_ne_of_val (by simp only; omega)
    have h3' : x' ≠ ⟨j.val + 1, by omega⟩ := fin_ne_of_val (by simp only; omega)
    have h4' : y' ≠ ⟨j.val + 1, by omega⟩ := fin_ne_of_val (by simp only; omega)
    exact ⟨intMap_commute_of hX hE
        (commute_of_anticomm (cr_cr _ x j) (cr_an _ h3) (cr_cr _ y j) (cr_an _ h4)).eq,
      intMap_commute_of hX hF
        (commute_of_anticomm (cr_cr _ x _) (cr_an _ h1) (cr_cr _ y _) (cr_an _ h2)).eq,
      intMap_commute_of hY hE (commute_of_anticomm (an_cr _ h1'.symm) (an_an _ x' _)
        (an_cr _ h2'.symm) (an_an _ y' _)).eq,
      intMap_commute_of hY hF (commute_of_anticomm (an_cr _ h3'.symm) (an_an _ x' j)
        (an_cr _ h4'.symm) (an_an _ y' j)).eq⟩
  · have hjl : j = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hjl
    have hE := isIntOp_E_last n
    have hF := isIntOp_F_last n
    exact ⟨intMap_commute_of hX hE (commute_of_anticomm (cr_cr _ x _) (cr_zeta n x)
        (cr_cr _ y _) (cr_zeta n y)).eq,
      intMap_commute_of hX hF (commute_of_anticomm (cr_zeta n x) (cr_an _ h1)
        (cr_zeta n y) (cr_an _ h2)).eq,
      intMap_commute_of hY hE (commute_of_anticomm (an_cr _ h1'.symm) (an_zeta n x')
        (an_cr _ h2'.symm) (an_zeta n y')).eq,
      intMap_commute_of hY hF (commute_of_anticomm (an_zeta n x') (an_an _ x' _)
        (an_zeta n y') (an_an _ y' _)).eq⟩

theorem epsW_theta_zero (hn : 1 ≤ n) :
    epsW n 0 ⟨0, by omega⟩ + epsW n 1 ⟨0, by omega⟩ = 0 := by
  simp only [epsW]
  split_ifs <;> omega

variable {σ : K →+* K} {F : (rootData n K).G →* (rootData n K).G}

theorem hasWitness_three_gen (hR : (rootData n K).RootsInCommutator σ F) (h2 : (2 : K) ≠ 0)
    {p f : ℕ} [CharP K p] (hcard : Nat.card (RootData.fixedField σ) = p ^ f) (hn : 2 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * 3) := by
  have hDx : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    fun i u hu => (hR i u hu).1
  have hDy : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n K).y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    fun i u hu => (hR i u hu).2
  obtain ⟨Xt, hXt, hXtR⟩ := exists_rootOp_theta (H := fixedSubgroup F) (by omega) h2 hDx
  obtain ⟨Yt, hYt, hYtR⟩ := exists_rootOp_thetaY (H := fixedSubgroup F) (by omega) h2 hDy
  set z : Fin (n + 1) := ⟨0, by omega⟩
  set o : Fin (n + 1) := ⟨1, by omega⟩
  set t : Fin (n + 1) := ⟨2, by omega⟩
  have hzo : z ≠ o := fin_ne_of_val (by simp [z, o])
  have hzt : z ≠ t := fin_ne_of_val (by simp [z, t])
  have hE0 : IsIntOp n (crB n z * anB n o) (rootIntMatrix n (.inl z)) :=
    isIntOp_E_lt n z (by simp only [z]; omega)
  have hF0 : IsIntOp n (crB n o * anB n z) (rootIntMatrix n (.inr z)) :=
    isIntOp_F_lt n z (by simp only [z]; omega)
  obtain ⟨c1, c2, c3, c4⟩ := commute_block (K := K) hzo hE0 hF0 hXt hYt
  obtain ⟨d1, d2, d3, d4⟩ := commute_of_two_le (K := K) t (by simp [t]) (x := z) (y := o)
    (x' := o) (y' := z) (by simp [z]) (by simp [o]) (by simp [o]) (by simp [z]) hXt hYt
  have hCMzt : (rootData n K).CM z t = 0 := by
    rw [rootData_CM, Matrix.transpose_apply, B_apply']
    simp [z, t]
  have h := (rootData n K).rootOp_witness_h hR h2 hcard
    (X := ![(rootData n K).E z, (rootData n K).E t, intMap K Xt])
    (Y := ![(rootData n K).F z, (rootData n K).F t, intMap K Yt])
    (w := ![fun j => (rootData n K).CM j z, fun j => (rootData n K).CM j t,
      fun j => epsW n 0 j + epsW n 1 j])
    (wY := ![fun j => -(rootData n K).CM j z, fun j => -(rootData n K).CM j t,
      fun j => -(epsW n 0 j + epsW n 1 j)])
    (fun a => ?_) (fun a => ?_) (fun a => ?_) (fun a => ?_) (fun a a' haa => ?_)
    (fun a a' haa => ?_) z (fun a => ?_) o ?_
  · rwa [Fintype.card_fin] at h
  · fin_cases a
    · exact rootOp_E (R := rootData n K) z (hDx _)
    · exact rootOp_E (R := rootData n K) t (hDx _)
    · exact hXtR
  · fin_cases a
    · exact rootOp_F (R := rootData n K) z (hDy _)
    · exact rootOp_F (R := rootData n K) t (hDy _)
    · exact hYtR
  · fin_cases a
    · exact (rootData n K).sqZero z
    · exact (rootData n K).sqZero t
    · exact pair_sqZeroPair hzo hXt hYt hXtR.sq hYtR.sq
  · fin_cases a
    · exact (rootData n K).E_ne_zero z
    · exact (rootData n K).E_ne_zero t
    · exact pair_ne_zero (by simp [Fin.lt_def, z, o]) hXt
  · fin_cases a <;> fin_cases a' <;> simp at haa ⊢
    · exact (rootData n K).commute_EE z t hCMzt
    · exact c1.symm
    · exact ((rootData n K).commute_EE z t hCMzt).symm
    · exact d1.symm
    · exact c1
    · exact d1
  · fin_cases a <;> fin_cases a' <;> simp at haa ⊢
    · exact (rootData n K).commute_EF t z hzt.symm
    · exact c2
    · exact (rootData n K).commute_EF z t hzt
    · exact d2
    · exact c3.symm
    · exact d3.symm
  · fin_cases a
    · show Even ((rootData n K).CM z z)
      rw [rootData_CM, Matrix.transpose_apply, CartanMatrix.B_diag]
      exact even_two
    · show Even ((rootData n K).CM z t)
      rw [hCMzt]
      exact ⟨0, rfl⟩
    · show Even (epsW n 0 ⟨0, by omega⟩ + epsW n 1 ⟨0, by omega⟩)
      rw [epsW_theta_zero (by omega)]
      exact ⟨0, rfl⟩
  · rw [rootData_CM, Matrix.transpose_apply, B_apply']
    simp [z, o]

theorem hasWitness_four_gen (hR : (rootData n K).RootsInCommutator σ F) (h2 : (2 : K) ≠ 0)
    {p f : ℕ} [CharP K p] (hcard : Nat.card (RootData.fixedField σ) = p ^ f) (hn : 3 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * 4) := by
  have hDx : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    fun i u hu => (hR i u hu).1
  have hDy : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n K).y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    fun i u hu => (hR i u hu).2
  obtain ⟨Xt, hXt, hXtR⟩ := exists_rootOp_theta (H := fixedSubgroup F) (by omega) h2 hDx
  obtain ⟨Yt, hYt, hYtR⟩ := exists_rootOp_thetaY (H := fixedSubgroup F) (by omega) h2 hDy
  obtain ⟨Xs, hXs, hXsR⟩ := stage1 (H := fixedSubgroup F) (by omega) h2 hDx 0 (by omega)
  obtain ⟨Ys, hYs, hYsR⟩ := stage1N (H := fixedSubgroup F) (by omega) h2 hDy 0 (by omega)
  set z : Fin (n + 1) := ⟨0, by omega⟩
  set o : Fin (n + 1) := ⟨1, by omega⟩
  set q : Fin (n + 1) := ⟨n - 1, by omega⟩
  set l : Fin (n + 1) := ⟨n, by omega⟩
  have hq0 : (⟨n - 1 - 0, by omega⟩ : Fin (n + 1)) = q := Fin.ext (by simp [q])
  rw [hq0] at hXs hYs
  have hzo : z ≠ o := fin_ne_of_val (by simp [z, o])
  have hzq : z ≠ q := fin_ne_of_val (by simp [z, q]; omega)
  have hql : q ≠ l := fin_ne_of_val (by simp [q, l]; omega)
  have hzl : z ≠ l := fin_ne_of_val (by simp [z, l]; omega)
  have hoq : o ≠ q := fin_ne_of_val (by simp [o, q]; omega)
  have hol : o ≠ l := fin_ne_of_val (by simp [o, l]; omega)
  have hE0 : IsIntOp n (crB n z * anB n o) (rootIntMatrix n (.inl z)) :=
    isIntOp_E_lt n z (by simp only [z]; omega)
  have hF0 : IsIntOp n (crB n o * anB n z) (rootIntMatrix n (.inr z)) :=
    isIntOp_F_lt n z (by simp only [z]; omega)
  have hEq : IsIntOp n (crB n q * anB n l) (rootIntMatrix n (.inl q)) :=
    (isIntOp_E_lt n q (by simp only [q]; omega)).congr (by
      congr 2
      exact Fin.ext (by simp only [q, l]; omega))
  have hFq : IsIntOp n (crB n l * anB n q) (rootIntMatrix n (.inr q)) :=
    (isIntOp_F_lt n q (by simp only [q]; omega)).congr (by
      congr 2
      exact Fin.ext (by simp only [q, l]; omega))
  obtain ⟨c1, c2, c3, c4⟩ := commute_block (K := K) hzo hE0 hF0 hXt hYt
  obtain ⟨e1, e2, e3, e4⟩ := commute_block (K := K) hql hEq hFq hXs hYs
  obtain ⟨d1, d2, d3, d4⟩ := commute_of_two_le (K := K) q (by simp [q]; omega) (x := z)
    (y := o) (x' := o) (y' := z) (by simp [z]) (by simp [o]) (by simp [o]) (by simp [z]) hXt hYt
  have f1 : Commute (intMap K Xs) ((rootData n K).E z) := intMap_commute_of hXs hE0
    (commute_of_anticomm (cr_cr _ q z) (cr_an _ hoq.symm) (cr_cr _ l z) (cr_an _ hol.symm)).eq
  have f2 : Commute (intMap K Xs) (intMap K Xt) := intMap_commute_of hXs hXt
    (commute_of_anticomm (cr_cr _ q z) (cr_cr _ q o) (cr_cr _ l z) (cr_cr _ l o)).eq
  have f3 : Commute (intMap K Xs) ((rootData n K).F z) := intMap_commute_of hXs hF0
    (commute_of_anticomm (cr_cr _ q o) (cr_an _ hzq.symm) (cr_cr _ l o) (cr_an _ hzl.symm)).eq
  have f4 : Commute (intMap K Ys) ((rootData n K).E z) := intMap_commute_of hYs hE0
    (commute_of_anticomm (an_cr _ hzl) (an_an _ l o) (an_cr _ hzq) (an_an _ q o)).eq
  have f5 : Commute (intMap K Ys) (intMap K Xt) := intMap_commute_of hYs hXt
    (commute_of_anticomm (an_cr _ hzl) (an_cr _ hol) (an_cr _ hzq) (an_cr _ hoq)).eq
  have f6 : Commute (intMap K Xs) (intMap K Yt) := intMap_commute_of hXs hYt
    (commute_of_anticomm (cr_an _ hoq.symm) (cr_an _ hzq.symm) (cr_an _ hol.symm)
      (cr_an _ hzl.symm)).eq
  have hCMzq : (rootData n K).CM z q = 0 := by
    rw [rootData_CM, Matrix.transpose_apply, B_apply']
    simp only [z, q]
    split_ifs <;> omega
  have h := (rootData n K).rootOp_witness_h hR h2 hcard
    (X := ![(rootData n K).E z, (rootData n K).E q, intMap K Xs, intMap K Xt])
    (Y := ![(rootData n K).F z, (rootData n K).F q, intMap K Ys, intMap K Yt])
    (w := ![fun j => (rootData n K).CM j z, fun j => (rootData n K).CM j q,
      fun j => epsW n (n - 1 - 0) j + epsW n n j, fun j => epsW n 0 j + epsW n 1 j])
    (wY := ![fun j => -(rootData n K).CM j z, fun j => -(rootData n K).CM j q,
      fun j => -(epsW n (n - 1 - 0) j + epsW n n j), fun j => -(epsW n 0 j + epsW n 1 j)])
    (fun a => ?_) (fun a => ?_) (fun a => ?_) (fun a => ?_) (fun a a' haa => ?_)
    (fun a a' haa => ?_) z (fun a => ?_) o ?_
  · rwa [Fintype.card_fin] at h
  · fin_cases a
    · exact rootOp_E (R := rootData n K) z (hDx _)
    · exact rootOp_E (R := rootData n K) q (hDx _)
    · exact hXsR
    · exact hXtR
  · fin_cases a
    · exact rootOp_F (R := rootData n K) z (hDy _)
    · exact rootOp_F (R := rootData n K) q (hDy _)
    · exact hYsR
    · exact hYtR
  · fin_cases a
    · exact (rootData n K).sqZero z
    · exact (rootData n K).sqZero q
    · exact pair_sqZeroPair hql hXs hYs hXsR.sq hYsR.sq
    · exact pair_sqZeroPair hzo hXt hYt hXtR.sq hYtR.sq
  · fin_cases a
    · exact (rootData n K).E_ne_zero z
    · exact (rootData n K).E_ne_zero q
    · exact pair_ne_zero (by simp [Fin.lt_def, q, l]; omega) hXs
    · exact pair_ne_zero (by simp [Fin.lt_def, z, o]) hXt
  · fin_cases a <;> fin_cases a' <;> simp at haa ⊢
    · exact (rootData n K).commute_EE z q hCMzq
    · exact f1.symm
    · exact c1.symm
    · exact ((rootData n K).commute_EE z q hCMzq).symm
    · exact e1.symm
    · exact d1.symm
    · exact f1
    · exact e1
    · exact f2
    · exact c1
    · exact d1
    · exact f2.symm
  · fin_cases a <;> fin_cases a' <;> simp at haa ⊢
    · exact (rootData n K).commute_EF q z hzq.symm
    · exact f3
    · exact c2
    · exact (rootData n K).commute_EF z q hzq
    · exact e2
    · exact d2
    · exact f4.symm
    · exact e3.symm
    · exact f5.symm
    · exact c3.symm
    · exact d3.symm
    · exact f6
  · fin_cases a
    · show Even ((rootData n K).CM z z)
      rw [rootData_CM, Matrix.transpose_apply, CartanMatrix.B_diag]
      exact even_two
    · show Even ((rootData n K).CM z q)
      rw [hCMzq]
      exact ⟨0, rfl⟩
    · show Even (epsW n (n - 1 - 0) ⟨0, by omega⟩ + epsW n n ⟨0, by omega⟩)
      rw [show epsW n (n - 1 - 0) ⟨0, by omega⟩ + epsW n n ⟨0, by omega⟩ = 0 by
        simp only [epsW]
        split_ifs <;> omega]
      exact ⟨0, rfl⟩
    · show Even (epsW n 0 ⟨0, by omega⟩ + epsW n 1 ⟨0, by omega⟩)
      rw [epsW_theta_zero (by omega)]
      exact ⟨0, rfl⟩
  · rw [rootData_CM, Matrix.transpose_apply, B_apply']
    simp [z, o]

end Generic

variable (b : TypeBLieIndex)

theorem hasWitness_theta_three (hodd : b.1.characteristic ≠ 2) (h3 : 3 ≤ b.carrierRank + 1) :
    HasWitness b.Group b.1.characteristic (b.1.fieldExponent * 3) :=
  hasWitness_three_gen (rootsInCommutator_odd b hodd h3) (two_ne_zero_closure b hodd)
    (card_fixedField_frob b) (by omega)

theorem hasWitness_theta_four (hodd : b.1.characteristic ≠ 2) (h4 : 3 ≤ b.carrierRank) :
    HasWitness b.Group b.1.characteristic (b.1.fieldExponent * 4) :=
  hasWitness_four_gen (rootsInCommutator_odd b hodd (by omega)) (two_ne_zero_closure b hodd)
    (card_fixedField_frob b) h4

end CFSG.RankThree.PartTwo.Census.Spin.CarrierB

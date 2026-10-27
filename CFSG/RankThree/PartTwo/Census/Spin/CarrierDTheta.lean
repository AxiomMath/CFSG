module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDFork
public import CFSG.RankThree.PartTwo.Census.Spin.Clifford
public import CFSG.RankThree.PartTwo.Census.Spin.RootOp

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

variable (n : ℕ) (hn : 4 ≤ n)

abbrev Cl : Type := CliffordAlgebra (splitEvenForm ℚ n)

@[expose] def IsIntOp (c : Cl n) (X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) : Prop :=
  HasIntMatrix (latticeBasis n) (spinAction _ (polarization n) c) X

namespace IsIntOp

variable {n} {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}

theorem mul (h : IsIntOp n c X) (h' : IsIntOp n d Y) : IsIntOp n (c * d) (X * Y) := by
  unfold IsIntOp at *
  rw [map_mul]
  exact HasIntMatrix.mul h h'

theorem sub (h : IsIntOp n c X) (h' : IsIntOp n d Y) : IsIntOp n (c - d) (X - Y) := by
  unfold IsIntOp at *
  rw [map_sub]
  exact HasIntMatrix.sub h h'

theorem zero : IsIntOp n 0 0 := by
  unfold IsIntOp
  rw [map_zero]
  exact HasIntMatrix.zero

theorem neg (h : IsIntOp n c X) : IsIntOp n (-c) (-X) := by
  have := zero.sub h
  rwa [zero_sub, zero_sub] at this

theorem eq (h : IsIntOp n c X) (h' : IsIntOp n c Y) : X = Y := HasIntMatrix.unique h h'

theorem eq_zero (h : IsIntOp n c X) (hc : c = 0) : X = 0 := h.eq (hc ▸ zero)

theorem congr (h : IsIntOp n c X) (hc : c = d) : IsIntOp n d X := hc ▸ h

end IsIntOp

noncomputable abbrev crD (i : Fin n) : Cl n := cr (polarizationBasis n) i

noncomputable abbrev anD (i : Fin n) : Cl n := an (polarizationBasis n) i

theorem isIntOp_E (i : Fin n) : IsIntOp n
    ((polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) i)
    (rootIntMatrix n hn (.inl i)) := by
  unfold IsIntOp
  rw [← E_eq_spinAction n hn]
  exact hasIntMatrix_E n hn i

theorem isIntOp_F (i : Fin n) : IsIntOp n
    ((polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) i)
    (rootIntMatrix n hn (.inr i)) := by
  unfold IsIntOp
  rw [← F_eq_spinAction n hn]
  exact hasIntMatrix_F n hn i

omit hn in
theorem chainE_eq (h2 : 2 ≤ n) (i : Fin n) (hi : i.val + 1 < n) :
    (polarization n).typeDSimpleRootBivector (polarizationBasis n) h2 i =
      crD n i * anD n ⟨i.val + 1, hi⟩ := by
  rw [SpinPolarizationData.typeDSimpleRootBivector_def, dite_eq_left hi]

omit hn in
theorem chainF_eq (h2 : 2 ≤ n) (i : Fin n) (hi : i.val + 1 < n) :
    (polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) h2 i =
      crD n ⟨i.val + 1, hi⟩ * anD n i := by
  rw [SpinPolarizationData.typeDSimpleNegativeRootBivector_def, dite_eq_left hi]

@[expose] def epsW (m : ℕ) (j : Fin n) : ℤ :=
  if j.val + 1 < n then (if m = j.val then 1 else 0) - (if m = j.val + 1 then 1 else 0)
  else (if m + 2 = n then 1 else 0) + (if m + 1 = n then 1 else 0)

theorem D_apply' (m : ℕ) (i j : Fin m) : CartanMatrix.D m i j =
    if i.val = j.val then 2 else if m ≤ 2 then 0
    else if i.val + 1 = j.val ∧ j.val + 2 < m then -1
    else if j.val + 1 = i.val ∧ i.val + 2 < m then -1
    else if i.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m) then -1
    else if j.val + 3 = m ∧ (i.val + 2 = m ∨ i.val + 1 = m) then -1 else 0 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]

theorem col_chain (i : Fin n) (hi : i.val + 1 < n) :
    (fun j => CartanMatrix.D n j i) = fun j => epsW n i.val j - epsW n (i.val + 1) j := by
  funext j
  have := j.isLt
  rw [D_apply', epsW, epsW]
  split_ifs <;> omega

theorem col_fork :
    (fun j => CartanMatrix.D n j ⟨n - 1, by omega⟩) =
      fun j => epsW n (n - 2) j + epsW n (n - 1) j := by
  funext j
  have := j.isLt
  rw [D_apply', epsW, epsW]
  simp only
  split_ifs <;> omega

theorem intMap_sub' (K : Type*) [Field K] (Z W : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    intMap K (Z - W) = intMap K Z - intMap K W := by
  ext a b
  simp [intMap]

theorem intMap_neg' (K : Type*) [Field K] (Z : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    intMap K (-Z) = -intMap K Z := by
  ext a b
  simp [intMap]

section Chain

variable {n hn} {K : Type} [Field K] {H : Subgroup (rootData n hn K).G} {L : Subfield K}

theorem rootOp_bracket {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    {wc wd : Fin n → ℤ} (hc : IsIntOp n c X) (hd : IsIntOp n d Y)
    (hcR : (rootData n hn K).RootOp H L (intMap K X) wc)
    (hdR : (rootData n hn K).RootOp H L (intMap K Y) wd)
    (hcdc : c * d * c = 0) (hdcd : d * c * d = 0) :
    (rootData n hn K).RootOp H L (intMap K (X * Y - Y * X)) (wc + wd) := by
  have h1 : intMap K X * intMap K Y * intMap K X = 0 := by
    rw [← intMap_mul, ← intMap_mul, ((hc.mul hd).mul hc).eq_zero hcdc, intMap_zero]
  have h2 : intMap K Y * intMap K X * intMap K Y = 0 := by
    rw [← intMap_mul, ← intMap_mul, ((hd.mul hc).mul hd).eq_zero hdcd, intMap_zero]
  rw [intMap_sub', intMap_mul, intMap_mul]
  exact hcR.bracket hdR h1 h2

theorem rootOp_congr_w {X : Matrix (Fin (dimension n)) (Fin (dimension n)) K} {w w' : Fin n → ℤ}
    (h : (rootData n hn K).RootOp H L X w) (hw : w = w') : (rootData n hn K).RootOp H L X w' :=
  hw ▸ h

theorem stage1 (hDx : ∀ i u, u ∈ L → (rootData n hn K).x i u ∈ ⁅H, H⁆) (t : ℕ)
    (ht : t ≤ n - 2) :
    ∃ X, IsIntOp n (crD n ⟨n - 2 - t, by omega⟩ * crD n ⟨n - 1, by omega⟩) X ∧
      (rootData n hn K).RootOp H L (intMap K X)
        (fun j => epsW n (n - 2 - t) j + epsW n (n - 1) j) := by
  induction t with
  | zero =>
    refine ⟨rootIntMatrix n hn (.inl ⟨n - 1, by omega⟩), ?_, ?_⟩
    · exact (isIntOp_E n hn ⟨n - 1, by omega⟩).congr
        (Fork.Eb_eq (polarization n) (polarizationBasis n) (by omega))
    · refine rootOp_congr_w (rootOp_E (R := rootData n hn K) ⟨n - 1, by omega⟩
        (fun u hu => hDx _ u hu)) ?_
      rw [rootData_CM, col_fork n hn, Nat.sub_zero]
  | succ t ih =>
    obtain ⟨Y, hY, hYR⟩ := ih (by omega)
    have hidx : (⟨n - 2 - t, by omega⟩ : Fin n) = ⟨(n - 2 - (t + 1)) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hY
    have hnt : n - 2 - t = n - 2 - (t + 1) + 1 := by omega
    have hE := (isIntOp_E n hn ⟨n - 2 - (t + 1), by omega⟩).congr
      (chainE_eq n (by omega) ⟨n - 2 - (t + 1), by omega⟩ (by simp only; omega))
    have hER := rootOp_E (R := rootData n hn K) ⟨n - 2 - (t + 1), by omega⟩
      (fun u hu => hDx _ u hu)
    have hjk : (⟨(n - 2 - (t + 1)) + 1, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    have hij : (⟨n - 2 - (t + 1), by omega⟩ : Fin n) ≠ ⟨(n - 2 - (t + 1)) + 1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    refine ⟨rootIntMatrix n hn (.inl ⟨n - 2 - (t + 1), by omega⟩) * Y -
      Y * rootIntMatrix n hn (.inl ⟨n - 2 - (t + 1), by omega⟩), ?_, ?_⟩
    · exact ((hE.mul hY).sub (hY.mul hE)).congr (bracket_M_P _ hjk)
    · refine rootOp_congr_w (rootOp_bracket hE hY hER hYR (M_P_M _ hij) (P_M_P _ hjk)) ?_
      rw [rootData_CM, col_chain n _ (by simp only; omega), hnt]
      funext j
      simp only [Pi.add_apply]
      ring

theorem stage2 (hDx : ∀ i u, u ∈ L → (rootData n hn K).x i u ∈ ⁅H, H⁆) (t : ℕ)
    (ht : t ≤ n - 2) :
    ∃ X, IsIntOp n (crD n ⟨0, by omega⟩ * crD n ⟨n - 1 - t, by omega⟩) X ∧
      (rootData n hn K).RootOp H L (intMap K X)
        (fun j => epsW n 0 j + epsW n (n - 1 - t) j) := by
  induction t with
  | zero =>
    obtain ⟨X, hX, hXR⟩ := stage1 hDx (n - 2) le_rfl
    have h0 : (⟨n - 2 - (n - 2), by omega⟩ : Fin n) = ⟨0, by omega⟩ := Fin.ext (by simp)
    have h1 : (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 1 - 0, by omega⟩ := Fin.ext (by simp)
    rw [h0, h1] at hX
    refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
    rw [Nat.sub_self, Nat.sub_zero]
  | succ t ih =>
    obtain ⟨X, hX, hXR⟩ := ih (by omega)
    have hidx : (⟨n - 1 - t, by omega⟩ : Fin n) = ⟨(n - 2 - t) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hX
    have hnt : n - 1 - t = n - 2 - t + 1 := by omega
    have hnt' : n - 1 - (t + 1) = n - 2 - t := by omega
    set k : Fin n := ⟨n - 2 - t, by omega⟩
    set k1 : Fin n := ⟨(n - 2 - t) + 1, by omega⟩
    set z : Fin n := ⟨0, by omega⟩
    have hd : IsIntOp n (crD n k1 * crD n z) (-X) :=
      hX.neg.congr (by rw [cr_cr (polarizationBasis n) z k1, neg_neg])
    have hdR := hXR.neg
    rw [← intMap_neg'] at hdR
    have hE := (isIntOp_E n hn k).congr (chainE_eq n (by omega) k (by simp only [k]; omega))
    have hER := rootOp_E (R := rootData n hn K) k (fun u hu => hDx _ u hu)
    have hjk : k1 ≠ z := by
      intro h
      have := congrArg Fin.val h
      simp only [k1, z] at this
      omega
    have hij : k ≠ k1 := by
      intro h
      have := congrArg Fin.val h
      simp only [k, k1] at this
      omega
    have hB := rootOp_bracket hE hd hER hdR (M_P_M _ hij) (P_M_P _ hjk)
    have hBi := ((hE.mul hd).sub (hd.mul hE)).congr (bracket_M_P _ hjk)
    have hk' : (⟨n - 1 - (t + 1), by omega⟩ : Fin n) = k := Fin.ext (by simp only [k]; omega)
    refine ⟨-(rootIntMatrix n hn (.inl k) * -X - -X * rootIntMatrix n hn (.inl k)), ?_, ?_⟩
    · rw [hk']
      exact hBi.neg.congr (by rw [cr_cr (polarizationBasis n) k z, neg_neg])
    · rw [intMap_neg']
      refine rootOp_congr_w hB.neg ?_
      rw [rootData_CM, col_chain n k (by simp only [k]; omega), hnt, hnt']
      funext j
      simp only [Pi.add_apply, k]
      ring

theorem exists_rootOp_theta (hDx : ∀ i u, u ∈ L → (rootData n hn K).x i u ∈ ⁅H, H⁆) :
    ∃ X, IsIntOp n (crD n ⟨0, by omega⟩ * crD n ⟨1, by omega⟩) X ∧
      (rootData n hn K).RootOp H L (intMap K X) (fun j => epsW n 0 j + epsW n 1 j) := by
  obtain ⟨X, hX, hXR⟩ := stage2 hDx (n - 2) le_rfl
  have h1 : (⟨n - 1 - (n - 2), by omega⟩ : Fin n) = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
  rw [h1] at hX
  refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
  rw [show n - 1 - (n - 2) = 1 by omega]

theorem stage1N (hDy : ∀ i u, u ∈ L → (rootData n hn K).y i u ∈ ⁅H, H⁆) (t : ℕ)
    (ht : t ≤ n - 2) :
    ∃ X, IsIntOp n (anD n ⟨n - 1, by omega⟩ * anD n ⟨n - 2 - t, by omega⟩) X ∧
      (rootData n hn K).RootOp H L (intMap K X)
        (fun j => -(epsW n (n - 2 - t) j + epsW n (n - 1) j)) := by
  induction t with
  | zero =>
    refine ⟨rootIntMatrix n hn (.inr ⟨n - 1, by omega⟩), ?_, ?_⟩
    · exact (isIntOp_F n hn ⟨n - 1, by omega⟩).congr
        (Fork.Fb_eq (polarization n) (polarizationBasis n) (by omega))
    · refine rootOp_congr_w (rootOp_F (R := rootData n hn K) ⟨n - 1, by omega⟩
        (fun u hu => hDy _ u hu)) ?_
      funext j
      rw [rootData_CM]
      have := congrFun (col_fork n hn) j
      rw [this, Nat.sub_zero]
  | succ t ih =>
    obtain ⟨Y, hY, hYR⟩ := ih (by omega)
    have hidx : (⟨n - 2 - t, by omega⟩ : Fin n) = ⟨(n - 2 - (t + 1)) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hY
    have hnt : n - 2 - t = n - 2 - (t + 1) + 1 := by omega
    set i : Fin n := ⟨n - 2 - (t + 1), by omega⟩
    set j : Fin n := ⟨(n - 2 - (t + 1)) + 1, by omega⟩
    set l : Fin n := ⟨n - 1, by omega⟩
    have hF := (isIntOp_F n hn i).congr (chainF_eq n (by omega) i (by simp only [i]; omega))
    have hFR := rootOp_F (R := rootData n hn K) i (fun u hu => hDy _ u hu)
    have hjk : j ≠ l := by
      intro h
      have := congrArg Fin.val h
      simp only [j, l] at this
      omega
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp only [i, j] at this
      omega
    refine ⟨Y * rootIntMatrix n hn (.inr i) - rootIntMatrix n hn (.inr i) * Y, ?_, ?_⟩
    · exact ((hY.mul hF).sub (hF.mul hY)).congr (bracket_N_M _ hjk)
    · refine rootOp_congr_w (rootOp_bracket hY hF hYR hFR (N_M_N _ hjk) (M_N_M _ hij)) ?_
      funext m
      rw [rootData_CM]
      have := congrFun (col_chain n i (by simp only [i]; omega)) m
      simp only [Pi.add_apply, this, hnt, i]
      ring

theorem stage2N (hDy : ∀ i u, u ∈ L → (rootData n hn K).y i u ∈ ⁅H, H⁆) (t : ℕ)
    (ht : t ≤ n - 2) :
    ∃ X, IsIntOp n (anD n ⟨n - 1 - t, by omega⟩ * anD n ⟨0, by omega⟩) X ∧
      (rootData n hn K).RootOp H L (intMap K X)
        (fun j => -(epsW n 0 j + epsW n (n - 1 - t) j)) := by
  induction t with
  | zero =>
    obtain ⟨X, hX, hXR⟩ := stage1N hDy (n - 2) le_rfl
    have h0 : (⟨n - 2 - (n - 2), by omega⟩ : Fin n) = ⟨0, by omega⟩ := Fin.ext (by simp)
    have h1 : (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 1 - 0, by omega⟩ := Fin.ext (by simp)
    rw [h0, h1] at hX
    refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
    rw [Nat.sub_self, Nat.sub_zero]
  | succ t ih =>
    obtain ⟨X, hX, hXR⟩ := ih (by omega)
    have hidx : (⟨n - 1 - t, by omega⟩ : Fin n) = ⟨(n - 2 - t) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hX
    have hnt : n - 1 - t = n - 2 - t + 1 := by omega
    have hnt' : n - 1 - (t + 1) = n - 2 - t := by omega
    set k : Fin n := ⟨n - 2 - t, by omega⟩
    set k1 : Fin n := ⟨(n - 2 - t) + 1, by omega⟩
    set z : Fin n := ⟨0, by omega⟩
    have hA : IsIntOp n (anD n z * anD n k1) (-X) :=
      hX.neg.congr (by rw [an_an (polarizationBasis n) k1 z, neg_neg])
    have hAR := hXR.neg
    rw [← intMap_neg'] at hAR
    have hF := (isIntOp_F n hn k).congr (chainF_eq n (by omega) k (by simp only [k]; omega))
    have hFR := rootOp_F (R := rootData n hn K) k (fun u hu => hDy _ u hu)
    have hjk : k1 ≠ z := by
      intro h
      have := congrArg Fin.val h
      simp only [k1, z] at this
      omega
    have hij : k ≠ k1 := by
      intro h
      have := congrArg Fin.val h
      simp only [k, k1] at this
      omega
    have hB := rootOp_bracket hA hF hAR hFR (N_M_N _ hjk) (M_N_M _ hij)
    have hBi := ((hA.mul hF).sub (hF.mul hA)).congr (bracket_N_M _ hjk)
    have hk' : (⟨n - 1 - (t + 1), by omega⟩ : Fin n) = k := Fin.ext (by simp only [k]; omega)
    refine ⟨-(-X * rootIntMatrix n hn (.inr k) - rootIntMatrix n hn (.inr k) * -X), ?_, ?_⟩
    · rw [hk']
      exact hBi.neg.congr (by rw [an_an (polarizationBasis n) z k, neg_neg])
    · rw [intMap_neg']
      refine rootOp_congr_w hB.neg ?_
      funext m
      rw [rootData_CM]
      have := congrFun (col_chain n k (by simp only [k]; omega)) m
      simp only [Pi.add_apply, this, hnt, hnt', k]
      ring

theorem exists_rootOp_thetaY (hDy : ∀ i u, u ∈ L → (rootData n hn K).y i u ∈ ⁅H, H⁆) :
    ∃ Y, IsIntOp n (anD n ⟨1, by omega⟩ * anD n ⟨0, by omega⟩) Y ∧
      (rootData n hn K).RootOp H L (intMap K Y) (fun j => -(epsW n 0 j + epsW n 1 j)) := by
  obtain ⟨X, hX, hXR⟩ := stage2N hDy (n - 2) le_rfl
  have h1 : (⟨n - 1 - (n - 2), by omega⟩ : Fin n) = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
  rw [h1] at hX
  refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
  rw [show n - 1 - (n - 2) = 1 by omega]

end Chain

section Theta

variable {n} {K : Type} [Field K]

theorem intMap_eq_of {c d e : Cl n} {X Y Z : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : IsIntOp n c X) (hd : IsIntOp n d Y) (he : IsIntOp n e Z) (h : c * d * c = e) :
    intMap K X * intMap K Y * intMap K X = intMap K Z := by
  rw [← intMap_mul, ← intMap_mul, ((hc.mul hd).mul hc).eq (h ▸ he)]

theorem intMap_commute_of {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : IsIntOp n c X) (hd : IsIntOp n d Y) (h : c * d = d * c) :
    Commute (intMap K X) (intMap K Y) := by
  show intMap K X * intMap K Y = intMap K Y * intMap K X
  rw [← intMap_mul, ← intMap_mul, (hc.mul hd).eq ((hd.mul hc).congr h.symm)]

theorem intMap_commute_of_zero {c d : Cl n}
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : IsIntOp n c X) (hd : IsIntOp n d Y) (h1 : c * d = 0) (h2 : d * c = 0) :
    Commute (intMap K X) (intMap K Y) :=
  intMap_commute_of hc hd (h1.trans h2.symm)

theorem theta_sqZeroPair {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crD n ⟨0, by omega⟩ * crD n ⟨1, by omega⟩) X)
    (hY : IsIntOp n (anD n ⟨1, by omega⟩ * anD n ⟨0, by omega⟩) Y)
    (hXsq : intMap K X * intMap K X = 0) (hYsq : intMap K Y * intMap K Y = 0) :
    SqZeroPair (intMap K X) (intMap K Y) where
  ee := hXsq
  ff := hYsq
  efe := intMap_eq_of hX hY hX (P_N_P _ (by simp))
  fef := intMap_eq_of hY hX hY (N_P_N _ (by simp))

noncomputable abbrev vac : Fin (dimension n) := Fintype.equivFin (Finset (Fin n)) ∅

theorem latticeBasis_vac : ((latticeBasis n (vac (n := n)) : (lattice n).toAddSubgroup) :
    ExteriorAlgebra ℚ (polarization n).W) = 1 := by
  rw [coe_latticeBasis, signSet, Equiv.symm_apply_apply, ExteriorAlgebra.basis_apply]
  simp

theorem theta_ne_zero {X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crD n ⟨0, by omega⟩ * crD n ⟨1, by omega⟩) X) : intMap K X ≠ 0 := by
  set i01 : Fin (dimension n) :=
    Fintype.equivFin (Finset (Fin n)) {⟨0, by omega⟩, ⟨1, by omega⟩}
  have hact : spinAction _ (polarization n) (crD n ⟨0, by omega⟩ * crD n ⟨1, by omega⟩)
      ((latticeBasis n vac : (lattice n).toAddSubgroup) : ExteriorAlgebra ℚ (polarization n).W) =
      ((latticeBasis n i01 : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
    rw [latticeBasis_vac, coe_latticeBasis, signSet, Equiv.symm_apply_apply,
      TauCeti.ExteriorAlgebra.basis_pair _ (show (⟨0, by omega⟩ : Fin n) < ⟨1, by omega⟩ by
        simp [Fin.lt_def]), map_mul, Module.End.mul_apply, spinAction_ι_wedge,
      spinAction_ι_wedge, mul_one]
  have h1 := hX vac
  rw [hact] at h1
  have hM : ∑ r, X r vac • latticeBasis n r = latticeBasis n i01 := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_zsmul] using h1.symm
  have h2 := congrArg (fun x => (latticeBasis n).repr x i01) hM
  simp only [map_sum, map_zsmul, Module.Basis.repr_self] at h2
  rw [Finsupp.finsetSum_apply] at h2
  simp [Finsupp.single_apply] at h2
  intro h0
  have h3 := congrFun (congrFun h0 i01) vac
  change ((X i01 vac : ℤ) : K) = 0 at h3
  rw [h2, Int.cast_one] at h3
  exact one_ne_zero h3

theorem fin_ne {m : ℕ} {a b : Fin m} (h : a.val ≠ b.val) : a ≠ b := fun h' => h (by rw [h'])

theorem commute_simple_of_two_le (j : Fin n) (hj : 2 ≤ j.val) (x y : Fin n) (hx : x.val < 2)
    (hy : y.val < 2) :
    Commute (crD n x * crD n y)
        ((polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) j) ∧
      Commute (crD n x * crD n y)
        ((polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) j) ∧
      Commute (anD n x * anD n y)
        ((polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) j) ∧
      Commute (anD n x * anD n y)
        ((polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) j) := by
  rw [SpinPolarizationData.typeDSimpleRootBivector_def,
    SpinPolarizationData.typeDSimpleNegativeRootBivector_def]
  split_ifs with h
  · have h1 : x ≠ j := fin_ne (by omega)
    have h2 : y ≠ j := fin_ne (by omega)
    have h3 : x ≠ ⟨j.val + 1, h⟩ := fin_ne (by simp only; omega)
    have h4 : y ≠ ⟨j.val + 1, h⟩ := fin_ne (by simp only; omega)
    refine ⟨commute_of_anticomm (cr_cr _ x j) (cr_an _ h3) (cr_cr _ y j) (cr_an _ h4),
      commute_of_anticomm (cr_cr _ x _) (cr_an _ h1) (cr_cr _ y _) (cr_an _ h2),
      commute_of_anticomm (an_cr _ h1.symm) (an_an _ x _) (an_cr _ h2.symm) (an_an _ y _),
      commute_of_anticomm (an_cr _ h3.symm) (an_an _ x j) (an_cr _ h4.symm) (an_an _ y j)⟩
  · have h1 : x ≠ ⟨n - 2, by omega⟩ := fin_ne (by simp only; omega)
    have h2 : y ≠ ⟨n - 2, by omega⟩ := fin_ne (by simp only; omega)
    have h3 : x ≠ ⟨n - 1, by omega⟩ := fin_ne (by simp only; omega)
    have h4 : y ≠ ⟨n - 1, by omega⟩ := fin_ne (by simp only; omega)
    refine ⟨commute_of_anticomm (cr_cr _ x _) (cr_cr _ x _) (cr_cr _ y _) (cr_cr _ y _),
      commute_of_anticomm (cr_an _ h3) (cr_an _ h1) (cr_an _ h4) (cr_an _ h2),
      commute_of_anticomm (an_cr _ h1.symm) (an_cr _ h3.symm) (an_cr _ h2.symm) (an_cr _ h4.symm),
      commute_of_anticomm (an_an _ x _) (an_an _ x _) (an_an _ y _) (an_an _ y _)⟩

end Theta

end CFSG.RankThree.PartTwo.Census.Spin.CarrierD

module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierB
public import CFSG.RankThree.PartTwo.Census.Spin.Clifford
public import CFSG.RankThree.PartTwo.Census.Spin.RootOpSandwich

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

theorem mul_anticomm_three {A : Type*} [Ring A] {g x y w : A} (hx : g * x = -(x * g))
    (hy : g * y = -(y * g)) (hw : g * w = -(w * g)) : g * (x * y * w) = -(x * y * w * g) := by
  calc g * (x * y * w) = g * x * y * w := by noncomm_ring
    _ = -(x * (g * y) * w) := by rw [hx]; noncomm_ring
    _ = x * y * (g * w) := by rw [hy]; noncomm_ring
    _ = -(x * y * w * g) := by rw [hw]; noncomm_ring

namespace CarrierB

open TauCeti TauCeti.TypeBSpinCarrier Cliff RootData

variable (n : ℕ)

abbrev Cl : Type := CliffordAlgebra (splitOddForm ℚ (n + 1))

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

noncomputable abbrev crB (i : Fin (n + 1)) : Cl n := cr (polarizationBasis n) i

noncomputable abbrev anB (i : Fin (n + 1)) : Cl n := an (polarizationBasis n) i

noncomputable abbrev zeta : Cl n :=
  CliffordAlgebra.ι _ ((remainderOne n : (polarization n).line) : SplitOddSpace ℚ (n + 1))

theorem zeta_sq : zeta n * zeta n = 1 := by
  rw [CliffordAlgebra.ι_sq_scalar, splitOddForm_remainderOne, map_one]

theorem cr_zeta (i : Fin (n + 1)) : crB n i * zeta n = -(zeta n * crB n i) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ((polarization n).isOrtho_W_line _ _)

theorem zeta_cr (i : Fin (n + 1)) : zeta n * crB n i = -(crB n i * zeta n) :=
  anticomm_symm (cr_zeta n i)

theorem zeta_an (i : Fin (n + 1)) : zeta n * anB n i = -(anB n i * zeta n) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho ((polarization n).isOrtho_line_W' _ _)

theorem an_zeta (i : Fin (n + 1)) : anB n i * zeta n = -(zeta n * anB n i) :=
  anticomm_symm (zeta_an n i)

theorem spinAction_zeta (x : ExteriorAlgebra ℚ (polarization n).W) :
    spinAction _ (polarization n) (zeta n) x = CliffordAlgebra.involute x := by
  have h := spinAction_ι_lineOperator (polarization n) (remainderOne n) x
  have h1 := splitOddPolarization_lineCoordinate_remainderOne ℚ (n + 1)
  simp only [h1, one_smul] at h
  exact h

theorem E_castSucc (j : Fin n) :
    E n j.castSucc = spinAction _ (polarization n) (crB n j.castSucc * anB n j.succ) :=
  LinearMap.ext fun x => by
    rw [E_eq, rep_rootGenerator_inl_castSucc, map_mul, Module.End.mul_apply]
    have h1 := spinAction_ι_contract (polarization n)
      ((polarization n).dualVector (polarizationBasis n) j.succ) x
    have h2 := spinAction_ι_wedge (polarization n) (polarizationBasis n j.castSucc)
    have h3 := SpinPolarizationData.pairingEquiv_dualVector (polarization n)
      (polarizationBasis n) j.succ
    simp only [h1, h2, h3]

theorem F_castSucc (j : Fin n) :
    F n j.castSucc = spinAction _ (polarization n) (crB n j.succ * anB n j.castSucc) :=
  LinearMap.ext fun x => by
    rw [F_eq, rep_rootGenerator_inr_castSucc, map_mul, Module.End.mul_apply]
    have h1 := spinAction_ι_contract (polarization n)
      ((polarization n).dualVector (polarizationBasis n) j.castSucc) x
    have h2 := spinAction_ι_wedge (polarization n) (polarizationBasis n j.succ)
    have h3 := SpinPolarizationData.pairingEquiv_dualVector (polarization n)
      (polarizationBasis n) j.castSucc
    simp only [h1, h2, h3]

theorem E_last :
    E n (Fin.last n) = spinAction _ (polarization n) (crB n (Fin.last n) * zeta n) :=
  LinearMap.ext fun x => by
    rw [E_eq, rep_rootGenerator_inl_last, map_mul, Module.End.mul_apply]
    have h1 := spinAction_zeta n x
    have h2 := spinAction_ι_wedge (polarization n) (polarizationBasis n (Fin.last n))
    simp only [h1, h2]

theorem F_last :
    F n (Fin.last n) = spinAction _ (polarization n) (zeta n * anB n (Fin.last n)) :=
  LinearMap.ext fun x => by
    simp only [F_eq, rep_rootGenerator_inr_last, map_mul, Module.End.mul_apply]
    have h1 := spinAction_ι_contract (polarization n)
      ((polarization n).dualVector (polarizationBasis n) (Fin.last n)) x
    have h3 := SpinPolarizationData.pairingEquiv_dualVector (polarization n)
      (polarizationBasis n) (Fin.last n)
    simp only [h1, h3, spinAction_zeta]

theorem hasIntMatrix_E (i : Fin (n + 1)) :
    HasIntMatrix (latticeBasis n) (E n i) (rootIntMatrix n (.inl i)) := fun s => by
  rw [E_eq]
  exact rep_rootGenerator_latticeBasis_eq_sum n (.inl i) s

theorem hasIntMatrix_F (i : Fin (n + 1)) :
    HasIntMatrix (latticeBasis n) (F n i) (rootIntMatrix n (.inr i)) := fun s => by
  rw [F_eq]
  exact rep_rootGenerator_latticeBasis_eq_sum n (.inr i) s

theorem isIntOp_E_lt (i : Fin (n + 1)) (hi : i.val < n) :
    IsIntOp n (crB n i * anB n ⟨i.val + 1, by omega⟩) (rootIntMatrix n (.inl i)) := by
  have h := hasIntMatrix_E n (⟨i.val, hi⟩ : Fin n).castSucc
  rw [E_castSucc] at h
  have e1 : (⟨i.val, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
  have e2 : (⟨i.val, hi⟩ : Fin n).succ = ⟨i.val + 1, by omega⟩ := Fin.ext rfl
  rw [e1, e2] at h
  exact h

theorem isIntOp_F_lt (i : Fin (n + 1)) (hi : i.val < n) :
    IsIntOp n (crB n ⟨i.val + 1, by omega⟩ * anB n i) (rootIntMatrix n (.inr i)) := by
  have h := hasIntMatrix_F n (⟨i.val, hi⟩ : Fin n).castSucc
  rw [F_castSucc] at h
  have e1 : (⟨i.val, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
  have e2 : (⟨i.val, hi⟩ : Fin n).succ = ⟨i.val + 1, by omega⟩ := Fin.ext rfl
  rw [e1, e2] at h
  exact h

theorem isIntOp_E_last :
    IsIntOp n (crB n (Fin.last n) * zeta n) (rootIntMatrix n (.inl (Fin.last n))) := by
  unfold IsIntOp
  rw [← E_last]
  exact hasIntMatrix_E n _

theorem isIntOp_F_last :
    IsIntOp n (zeta n * anB n (Fin.last n)) (rootIntMatrix n (.inr (Fin.last n))) := by
  unfold IsIntOp
  rw [← F_last]
  exact hasIntMatrix_F n _

@[expose] def epsW (m : ℕ) (j : Fin (n + 1)) : ℤ :=
  if j.val < n then (if m = j.val then 1 else 0) - (if m = j.val + 1 then 1 else 0)
  else if m = n then 2 else 0

omit n in
theorem B_apply' (m : ℕ) (i j : Fin m) : CartanMatrix.B m i j =
    if i.val = j.val then 2 else if i.val + 1 = j.val then (if j.val = m - 1 then -2 else -1)
    else if j.val + 1 = i.val then -1 else 0 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]

theorem col_chain (K : Type) [Field K] (i : Fin (n + 1)) (hi : i.val < n) :
    (fun j => (rootData n K).CM j i) = fun j => epsW n i.val j - epsW n (i.val + 1) j := by
  funext j
  have := j.isLt
  rw [rootData_CM, Matrix.transpose_apply, B_apply', epsW, epsW]
  split_ifs <;> omega

theorem col_last (K : Type) [Field K] :
    (fun j => (rootData n K).CM j (Fin.last n)) = fun j => epsW n n j := by
  funext j
  have := j.isLt
  rw [rootData_CM, Matrix.transpose_apply, B_apply', epsW]
  simp only [Fin.val_last]
  split_ifs <;> omega

theorem CM_chain (K : Type) [Field K] (i : Fin (n + 1)) (hi : i.val < n) (j : Fin (n + 1)) :
    (rootData n K).CM j i = epsW n i.val j - epsW n (i.val + 1) j :=
  congrFun (col_chain n K i hi) j

theorem CM_last (K : Type) [Field K] (j : Fin (n + 1)) :
    (rootData n K).CM j (Fin.last n) = epsW n n j :=
  congrFun (col_last n K) j

theorem sandwich_eq (i k : Fin (n + 1)) :
    crB n k * zeta n * (crB n i * anB n k) * (crB n k * zeta n) = crB n i * crB n k := by
  calc crB n k * zeta n * (crB n i * anB n k) * (crB n k * zeta n)
      = crB n k * (zeta n * (crB n i * anB n k * crB n k)) * zeta n := by noncomm_ring
    _ = -(crB n k * crB n i * anB n k * crB n k * (zeta n * zeta n)) := by
        rw [mul_anticomm_three (zeta_cr n i) (zeta_an n k) (zeta_cr n k)]
        noncomm_ring
    _ = crB n i * (crB n k * anB n k * crB n k) := by
        rw [zeta_sq, mul_one, cr_cr (polarizationBasis n) k i]
        noncomm_ring
    _ = crB n i * crB n k := by rw [cr_an_cr]

theorem sandwich_zero {i k : Fin (n + 1)} (hik : i ≠ k) :
    crB n i * anB n k * (crB n k * zeta n) * (crB n i * anB n k) = 0 := by
  have h := sandwich₃_eq_zero (cr_an (polarizationBasis n) hik)
    (cr_cr (polarizationBasis n) i k) (cr_zeta n i) (cr_sq (polarizationBasis n) i)
  calc crB n i * anB n k * (crB n k * zeta n) * (crB n i * anB n k)
      = crB n i * anB n k * crB n k * zeta n * crB n i * anB n k := by noncomm_ring
    _ = 0 := by rw [h, zero_mul]

theorem sandwichN_eq (i k : Fin (n + 1)) :
    zeta n * anB n k * (crB n k * anB n i) * (zeta n * anB n k) = anB n k * anB n i := by
  calc zeta n * anB n k * (crB n k * anB n i) * (zeta n * anB n k)
      = zeta n * (anB n k * crB n k * anB n i) * zeta n * anB n k := by noncomm_ring
    _ = -(anB n k * crB n k * anB n i * (zeta n * zeta n) * anB n k) := by
        rw [mul_anticomm_three (zeta_an n k) (zeta_cr n k) (zeta_an n i)]
        noncomm_ring
    _ = anB n k * crB n k * anB n k * anB n i := by
        rw [zeta_sq, mul_one, mul_assoc (anB n k * crB n k), an_an (polarizationBasis n) i k]
        noncomm_ring
    _ = anB n k * anB n i := by rw [an_cr_an]

theorem sandwichN_zero {i k : Fin (n + 1)} (hik : i ≠ k) :
    crB n k * anB n i * (zeta n * anB n k) * (crB n k * anB n i) = 0 := by
  have h := sandwich₃_eq_zero (an_zeta n i) (an_an (polarizationBasis n) i k)
    (an_cr (polarizationBasis n) hik.symm) (an_sq (polarizationBasis n) i)
  calc crB n k * anB n i * (zeta n * anB n k) * (crB n k * anB n i)
      = crB n k * (anB n i * zeta n * anB n k * crB n k * anB n i) := by noncomm_ring
    _ = 0 := by rw [h, mul_zero]

theorem intMap_sub' (K : Type*) [Field K]
    (Z W : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    intMap K (Z - W) = intMap K Z - intMap K W := by
  ext a b
  simp [intMap]

theorem intMap_neg' (K : Type*) [Field K]
    (Z : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) :
    intMap K (-Z) = -intMap K Z := by
  ext a b
  simp [intMap]

section Chain

variable {n} {K : Type} [Field K] {H : Subgroup (rootData n K).G} {L : Subfield K}

theorem rootOp_bracket {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    {wc wd : Fin (n + 1) → ℤ} (hc : IsIntOp n c X) (hd : IsIntOp n d Y)
    (hcR : (rootData n K).RootOp H L (intMap K X) wc)
    (hdR : (rootData n K).RootOp H L (intMap K Y) wd)
    (hcdc : c * d * c = 0) (hdcd : d * c * d = 0) :
    (rootData n K).RootOp H L (intMap K (X * Y - Y * X)) (wc + wd) := by
  have h1 : intMap K X * intMap K Y * intMap K X = 0 := by
    rw [← intMap_mul, ← intMap_mul, ((hc.mul hd).mul hc).eq_zero hcdc, intMap_zero]
  have h2 : intMap K Y * intMap K X * intMap K Y = 0 := by
    rw [← intMap_mul, ← intMap_mul, ((hd.mul hc).mul hd).eq_zero hdcd, intMap_zero]
  rw [intMap_sub', intMap_mul, intMap_mul]
  exact hcR.bracket hdR h1 h2

theorem rootOp_sandwich (h2 : (2 : K) ≠ 0) {c d : Cl n}
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ} {wc wd : Fin (n + 1) → ℤ}
    (hc : IsIntOp n c X) (hd : IsIntOp n d Y)
    (hcR : (rootData n K).RootOp H L (intMap K X) wc)
    (hdR : (rootData n K).RootOp H L (intMap K Y) wd) (hcdc : c * d * c = 0) :
    (rootData n K).RootOp H L (intMap K (Y * X * Y)) (wc + wd + wd) := by
  have h1 : intMap K X * intMap K Y * intMap K X = 0 := by
    rw [← intMap_mul, ← intMap_mul, ((hc.mul hd).mul hc).eq_zero hcdc, intMap_zero]
  rw [intMap_mul, intMap_mul]
  exact hcR.sandwich h2 hdR h1

theorem rootOp_congr_w {X : Matrix (Fin (dimension n)) (Fin (dimension n)) K}
    {w w' : Fin (n + 1) → ℤ} (h : (rootData n K).RootOp H L X w) (hw : w = w') :
    (rootData n K).RootOp H L X w' :=
  hw ▸ h

theorem fin_last_eq : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl

theorem stage1 (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0)
    (hDx : ∀ i u, u ∈ L → (rootData n K).x i u ∈ ⁅H, H⁆) (t : ℕ) (ht : t ≤ n - 1) :
    ∃ X, IsIntOp n (crB n ⟨n - 1 - t, by omega⟩ * crB n ⟨n, by omega⟩) X ∧
      (rootData n K).RootOp H L (intMap K X) (fun j => epsW n (n - 1 - t) j + epsW n n j) := by
  induction t with
  | zero =>
    set i : Fin (n + 1) := ⟨n - 1, by omega⟩
    have hi : i.val < n := by simp only [i]; omega
    have hi1 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by
      simp only [i, Fin.val_last]; omega)
    have hc := isIntOp_E_lt n i hi
    rw [hi1] at hc
    have hd := isIntOp_E_last n
    have hik : i ≠ Fin.last n := fun h => by
      have := congrArg Fin.val h
      simp only [i, Fin.val_last] at this
      omega
    have hcR := rootOp_E (R := rootData n K) i (fun u hu => hDx _ u hu)
    have hdR := rootOp_E (R := rootData n K) (Fin.last n) (fun u hu => hDx _ u hu)
    refine ⟨rootIntMatrix n (.inl (Fin.last n)) * rootIntMatrix n (.inl i) *
      rootIntMatrix n (.inl (Fin.last n)), ?_, ?_⟩
    · rw [fin_last_eq]
      exact ((hd.mul hc).mul hd).congr (sandwich_eq n i (Fin.last n))
    · refine rootOp_congr_w (rootOp_sandwich h2 hc hd hcR hdR (sandwich_zero n hik)) ?_
      rw [col_chain n K i hi, col_last n K]
      funext j
      simp only [Pi.add_apply, i, Nat.sub_zero]
      have : n - 1 + 1 = n := by omega
      rw [this]
      ring
  | succ t ih =>
    obtain ⟨Y, hY, hYR⟩ := ih (by omega)
    have hidx : (⟨n - 1 - t, by omega⟩ : Fin (n + 1)) = ⟨(n - 1 - (t + 1)) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hY
    have hnt : n - 1 - t = n - 1 - (t + 1) + 1 := by omega
    set i : Fin (n + 1) := ⟨n - 1 - (t + 1), by omega⟩
    have hi : i.val < n := by simp only [i]; omega
    have hE := isIntOp_E_lt n i hi
    have hER := rootOp_E (R := rootData n K) i (fun u hu => hDx _ u hu)
    have hjk : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) ≠ ⟨n, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [i] at this
      omega
    have hij : i ≠ ⟨i.val + 1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    refine ⟨rootIntMatrix n (.inl i) * Y - Y * rootIntMatrix n (.inl i), ?_, ?_⟩
    · exact ((hE.mul hY).sub (hY.mul hE)).congr (bracket_M_P _ hjk)
    · refine rootOp_congr_w (rootOp_bracket hE hY hER hYR (M_P_M _ hij) (P_M_P _ hjk)) ?_
      rw [col_chain n K i hi]
      funext j
      simp only [Pi.add_apply, i]
      rw [hnt]
      ring

theorem stage2 (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0)
    (hDx : ∀ i u, u ∈ L → (rootData n K).x i u ∈ ⁅H, H⁆) (t : ℕ) (ht : t ≤ n - 1) :
    ∃ X, IsIntOp n (crB n ⟨0, by omega⟩ * crB n ⟨n - t, by omega⟩) X ∧
      (rootData n K).RootOp H L (intMap K X) (fun j => epsW n 0 j + epsW n (n - t) j) := by
  induction t with
  | zero =>
    obtain ⟨X, hX, hXR⟩ := stage1 hn h2 hDx (n - 1) le_rfl
    have h0 : (⟨n - 1 - (n - 1), by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
    have h1 : (⟨n, by omega⟩ : Fin (n + 1)) = ⟨n - 0, by omega⟩ := Fin.ext (by simp)
    rw [h0, h1] at hX
    refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
    rw [Nat.sub_self, Nat.sub_zero]
  | succ t ih =>
    obtain ⟨X, hX, hXR⟩ := ih (by omega)
    have hidx : (⟨n - t, by omega⟩ : Fin (n + 1)) = ⟨(n - 1 - t) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hX
    have hnt : n - t = n - 1 - t + 1 := by omega
    have hnt' : n - (t + 1) = n - 1 - t := by omega
    set k : Fin (n + 1) := ⟨n - 1 - t, by omega⟩
    set k1 : Fin (n + 1) := ⟨(n - 1 - t) + 1, by omega⟩
    set z : Fin (n + 1) := ⟨0, by omega⟩
    have hk : k.val < n := by simp only [k]; omega
    have hk1 : (⟨k.val + 1, by omega⟩ : Fin (n + 1)) = k1 := Fin.ext (by simp only [k, k1])
    have hd : IsIntOp n (crB n k1 * crB n z) (-X) :=
      hX.neg.congr (by rw [cr_cr (polarizationBasis n) z k1, neg_neg])
    have hdR := hXR.neg
    rw [← intMap_neg'] at hdR
    have hE := isIntOp_E_lt n k hk
    rw [hk1] at hE
    have hER := rootOp_E (R := rootData n K) k (fun u hu => hDx _ u hu)
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
    have hk' : (⟨n - (t + 1), by omega⟩ : Fin (n + 1)) = k := Fin.ext (by simp only [k]; omega)
    refine ⟨-(rootIntMatrix n (.inl k) * -X - -X * rootIntMatrix n (.inl k)), ?_, ?_⟩
    · rw [hk']
      exact hBi.neg.congr (by rw [cr_cr (polarizationBasis n) k z, neg_neg])
    · rw [intMap_neg']
      refine rootOp_congr_w hB.neg ?_
      rw [col_chain n K k hk]
      funext j
      simp only [Pi.add_apply, k]
      rw [hnt, hnt']
      ring

theorem exists_rootOp_theta (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0)
    (hDx : ∀ i u, u ∈ L → (rootData n K).x i u ∈ ⁅H, H⁆) :
    ∃ X, IsIntOp n (crB n ⟨0, by omega⟩ * crB n ⟨1, by omega⟩) X ∧
      (rootData n K).RootOp H L (intMap K X) (fun j => epsW n 0 j + epsW n 1 j) := by
  obtain ⟨X, hX, hXR⟩ := stage2 hn h2 hDx (n - 1) le_rfl
  have h1 : (⟨n - (n - 1), by omega⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
  rw [h1] at hX
  refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
  rw [show n - (n - 1) = 1 by omega]

theorem stage1N (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0)
    (hDy : ∀ i u, u ∈ L → (rootData n K).y i u ∈ ⁅H, H⁆) (t : ℕ) (ht : t ≤ n - 1) :
    ∃ X, IsIntOp n (anB n ⟨n, by omega⟩ * anB n ⟨n - 1 - t, by omega⟩) X ∧
      (rootData n K).RootOp H L (intMap K X)
        (fun j => -(epsW n (n - 1 - t) j + epsW n n j)) := by
  induction t with
  | zero =>
    set i : Fin (n + 1) := ⟨n - 1, by omega⟩
    have hi : i.val < n := by simp only [i]; omega
    have hi1 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by
      simp only [i, Fin.val_last]; omega)
    have hc := isIntOp_F_lt n i hi
    rw [hi1] at hc
    have hd := isIntOp_F_last n
    have hik : i ≠ Fin.last n := fun h => by
      have := congrArg Fin.val h
      simp only [i, Fin.val_last] at this
      omega
    have hcR := rootOp_F (R := rootData n K) i (fun u hu => hDy _ u hu)
    have hdR := rootOp_F (R := rootData n K) (Fin.last n) (fun u hu => hDy _ u hu)
    refine ⟨rootIntMatrix n (.inr (Fin.last n)) * rootIntMatrix n (.inr i) *
      rootIntMatrix n (.inr (Fin.last n)), ?_, ?_⟩
    · rw [fin_last_eq]
      exact ((hd.mul hc).mul hd).congr (sandwichN_eq n i (Fin.last n))
    · refine rootOp_congr_w (rootOp_sandwich h2 hc hd hcR hdR (sandwichN_zero n hik)) ?_
      funext j
      simp only [Pi.add_apply, CM_chain n K i hi, CM_last n K]
      have hiv : i.val = n - 1 := rfl
      have hiv1 : i.val + 1 = n := by omega
      rw [hiv1, hiv, Nat.sub_zero]
      ring
  | succ t ih =>
    obtain ⟨Y, hY, hYR⟩ := ih (by omega)
    have hidx : (⟨n - 1 - t, by omega⟩ : Fin (n + 1)) = ⟨(n - 1 - (t + 1)) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hY
    have hnt : n - 1 - t = n - 1 - (t + 1) + 1 := by omega
    set i : Fin (n + 1) := ⟨n - 1 - (t + 1), by omega⟩
    set j : Fin (n + 1) := ⟨(n - 1 - (t + 1)) + 1, by omega⟩
    set l : Fin (n + 1) := ⟨n, by omega⟩
    have hi : i.val < n := by simp only [i]; omega
    have hij1 : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp only [i, j])
    have hF := isIntOp_F_lt n i hi
    rw [hij1] at hF
    have hFR := rootOp_F (R := rootData n K) i (fun u hu => hDy _ u hu)
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
    refine ⟨Y * rootIntMatrix n (.inr i) - rootIntMatrix n (.inr i) * Y, ?_, ?_⟩
    · exact ((hY.mul hF).sub (hF.mul hY)).congr (bracket_N_M _ hjk)
    · refine rootOp_congr_w (rootOp_bracket hY hF hYR hFR (N_M_N _ hjk) (M_N_M _ hij)) ?_
      funext m
      simp only [Pi.add_apply, CM_chain n K i hi]
      have hiv : i.val = n - 1 - (t + 1) := rfl
      rw [hiv, hnt]
      ring

theorem stage2N (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0)
    (hDy : ∀ i u, u ∈ L → (rootData n K).y i u ∈ ⁅H, H⁆) (t : ℕ) (ht : t ≤ n - 1) :
    ∃ X, IsIntOp n (anB n ⟨n - t, by omega⟩ * anB n ⟨0, by omega⟩) X ∧
      (rootData n K).RootOp H L (intMap K X) (fun j => -(epsW n 0 j + epsW n (n - t) j)) := by
  induction t with
  | zero =>
    obtain ⟨X, hX, hXR⟩ := stage1N hn h2 hDy (n - 1) le_rfl
    have h0 : (⟨n - 1 - (n - 1), by omega⟩ : Fin (n + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
    have h1 : (⟨n, by omega⟩ : Fin (n + 1)) = ⟨n - 0, by omega⟩ := Fin.ext (by simp)
    rw [h0, h1] at hX
    refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
    rw [Nat.sub_self, Nat.sub_zero]
  | succ t ih =>
    obtain ⟨X, hX, hXR⟩ := ih (by omega)
    have hidx : (⟨n - t, by omega⟩ : Fin (n + 1)) = ⟨(n - 1 - t) + 1, by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hidx] at hX
    have hnt : n - t = n - 1 - t + 1 := by omega
    have hnt' : n - (t + 1) = n - 1 - t := by omega
    set k : Fin (n + 1) := ⟨n - 1 - t, by omega⟩
    set k1 : Fin (n + 1) := ⟨(n - 1 - t) + 1, by omega⟩
    set z : Fin (n + 1) := ⟨0, by omega⟩
    have hk : k.val < n := by simp only [k]; omega
    have hk1 : (⟨k.val + 1, by omega⟩ : Fin (n + 1)) = k1 := Fin.ext (by simp only [k, k1])
    have hA : IsIntOp n (anB n z * anB n k1) (-X) :=
      hX.neg.congr (by rw [an_an (polarizationBasis n) k1 z, neg_neg])
    have hAR := hXR.neg
    rw [← intMap_neg'] at hAR
    have hF := isIntOp_F_lt n k hk
    rw [hk1] at hF
    have hFR := rootOp_F (R := rootData n K) k (fun u hu => hDy _ u hu)
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
    have hk' : (⟨n - (t + 1), by omega⟩ : Fin (n + 1)) = k := Fin.ext (by simp only [k]; omega)
    refine ⟨-(-X * rootIntMatrix n (.inr k) - rootIntMatrix n (.inr k) * -X), ?_, ?_⟩
    · rw [hk']
      exact hBi.neg.congr (by rw [an_an (polarizationBasis n) z k, neg_neg])
    · rw [intMap_neg']
      refine rootOp_congr_w hB.neg ?_
      funext m
      simp only [Pi.add_apply, CM_chain n K k hk]
      have hkv : k.val = n - 1 - t := rfl
      rw [hkv, hnt', hnt]
      ring

theorem exists_rootOp_thetaY (hn : 1 ≤ n) (h2 : (2 : K) ≠ 0)
    (hDy : ∀ i u, u ∈ L → (rootData n K).y i u ∈ ⁅H, H⁆) :
    ∃ Y, IsIntOp n (anB n ⟨1, by omega⟩ * anB n ⟨0, by omega⟩) Y ∧
      (rootData n K).RootOp H L (intMap K Y) (fun j => -(epsW n 0 j + epsW n 1 j)) := by
  obtain ⟨X, hX, hXR⟩ := stage2N hn h2 hDy (n - 1) le_rfl
  have h1 : (⟨n - (n - 1), by omega⟩ : Fin (n + 1)) = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
  rw [h1] at hX
  refine ⟨X, hX, rootOp_congr_w hXR ?_⟩
  rw [show n - (n - 1) = 1 by omega]

end Chain

section Pair

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

theorem pair_sqZeroPair {i k : Fin (n + 1)} (hik : i ≠ k)
    {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crB n i * crB n k) X) (hY : IsIntOp n (anB n k * anB n i) Y)
    (hXsq : intMap K X * intMap K X = 0) (hYsq : intMap K Y * intMap K Y = 0) :
    SqZeroPair (intMap K X) (intMap K Y) where
  ee := hXsq
  ff := hYsq
  efe := intMap_eq_of hX hY hX (P_N_P _ hik)
  fef := intMap_eq_of hY hX hY (N_P_N _ hik)

theorem coeff_eq_one {c : Cl n} {X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (h : IsIntOp n c X) {s r : Fin (dimension n)}
    (hT : spinAction _ (polarization n) c
      (latticeBasis n s : ExteriorAlgebra ℚ (polarization n).W) = latticeBasis n r) :
    X r s = 1 := by
  have h1 := h s
  rw [hT] at h1
  have hM : ∑ r', X r' s • latticeBasis n r' = latticeBasis n r := by
    apply Subtype.ext
    rw [h1]
    simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_zsmul]
  have h2 := congrArg (fun x => (latticeBasis n).repr x r) hM
  simp only [map_sum, map_zsmul, Module.Basis.repr_self] at h2
  rw [Finsupp.finsetSum_apply] at h2
  simpa [Finsupp.single_apply] using h2

noncomputable abbrev vac : Fin (dimension n) := Fintype.equivFin (Finset (Fin (n + 1))) ∅

theorem latticeBasis_vac : ((latticeBasis n (vac (n := n)) : (lattice n).toAddSubgroup) :
    ExteriorAlgebra ℚ (polarization n).W) = 1 := by
  rw [coe_latticeBasis, signSet, Equiv.symm_apply_apply, ExteriorAlgebra.basis_apply]
  simp

theorem pair_ne_zero {i k : Fin (n + 1)} (hik : i < k)
    {X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hX : IsIntOp n (crB n i * crB n k) X) : intMap K X ≠ 0 := by
  set i01 : Fin (dimension n) := Fintype.equivFin (Finset (Fin (n + 1))) {i, k}
  have hact : spinAction _ (polarization n) (crB n i * crB n k)
      ((latticeBasis n vac : (lattice n).toAddSubgroup) : ExteriorAlgebra ℚ (polarization n).W) =
      ((latticeBasis n i01 : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
    rw [latticeBasis_vac, coe_latticeBasis, signSet, Equiv.symm_apply_apply,
      TauCeti.ExteriorAlgebra.basis_pair _ hik, map_mul, Module.End.mul_apply,
      spinAction_ι_wedge, spinAction_ι_wedge, mul_one]
  have h2 := coeff_eq_one hX hact
  intro h0
  have h3 := congrFun (congrFun h0 i01) vac
  change ((X i01 vac : ℤ) : K) = 0 at h3
  rw [h2, Int.cast_one] at h3
  exact one_ne_zero h3

end Pair

end CarrierB

end CFSG.RankThree.PartTwo.Census.Spin

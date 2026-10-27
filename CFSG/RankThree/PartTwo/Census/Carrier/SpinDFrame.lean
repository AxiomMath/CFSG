module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame
public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDTheta

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier CFSG.RankThree.PartTwo.Census.Spin SpinFrame
open CFSG.RankThree.PartTwo.Census.Spin.CarrierD (Cl IsIntOp crD anD isIntOp_E isIntOp_F
  chainE_eq chainF_eq)

variable (n : ℕ)

abbrev Sp : Type :=
  ExteriorAlgebra ℚ (polarization n).W

@[expose] noncomputable def gen : DI n → Cl n
  | .inl i => crD n i
  | .inr i => anD n i

@[simp] theorem gen_inl (i : Fin n) : gen n (.inl i) = crD n i := rfl
@[simp] theorem gen_inr (i : Fin n) : gen n (.inr i) = anD n i := rfl

theorem act_crD (i : Fin n) (x : Sp n) :
    spinAction _ (polarization n) (crD n i) x = ExteriorAlgebra.ι ℚ (polarizationBasis n i) * x :=
  spinAction_ι_wedge (polarization n) (polarizationBasis n i) x

theorem act_anD (i : Fin n) (x : Sp n) :
    spinAction _ (polarization n) (anD n i) x =
      CliffordAlgebra.contractLeft ((polarizationBasis n).coord i) x := by
  have h1 := spinAction_ι_contract (polarization n)
    ((polarization n).dualVector (polarizationBasis n) i) x
  have h3 := SpinPolarizationData.pairingEquiv_dualVector (polarization n)
    (polarizationBasis n) i
  rw [h3] at h1
  exact h1

theorem act_gen_mem (a : DI n) {x : Sp n} (hx : x ∈ lattice n) :
    spinAction _ (polarization n) (gen n a) x ∈ lattice n := by
  rcases a with i | i
  · rw [gen, act_crD]
    exact TauCeti.ExteriorAlgebra.ι_basis_mul_mem_integralLattice _ i hx
  · rw [gen, act_anD]
    exact TauCeti.ExteriorAlgebra.contractLeft_coord_mem_integralLattice _ i hx

section IntMat

variable {n}

@[expose] noncomputable def intMat (T : Module.End ℚ (Sp n))
    (hT : ∀ s, T (latticeBasis n s : Sp n) ∈ (lattice n).toAddSubgroup) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  fun r s => (latticeBasis n).repr ⟨T (latticeBasis n s : Sp n), hT s⟩ r

theorem hasIntMatrix_intMat (T : Module.End ℚ (Sp n))
    (hT : ∀ s, T (latticeBasis n s : Sp n) ∈ (lattice n).toAddSubgroup) :
    HasIntMatrix (latticeBasis n) T (intMat T hT) := fun s => by
  have h := (latticeBasis n).sum_repr ⟨T (latticeBasis n s : Sp n), hT s⟩
  have h' := congrArg (fun y : (lattice n).toAddSubgroup => (y : Sp n)) h
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroup.coe_zsmul] at h'
  exact h'.symm

theorem intMat_apply_of_eq {T : Module.End ℚ (Sp n)}
    {hT : ∀ s, T (latticeBasis n s : Sp n) ∈ (lattice n).toAddSubgroup} {s a : Fin (dimension n)}
    {c : ℤ} (h : T (latticeBasis n s : Sp n) = c • (latticeBasis n a : Sp n))
    (r : Fin (dimension n)) : intMat T hT r s = if r = a then c else 0 := by
  have e : (⟨T (latticeBasis n s : Sp n), hT s⟩ : (lattice n).toAddSubgroup) =
      c • latticeBasis n a := by
    apply Subtype.ext
    show T (latticeBasis n s : Sp n) = ((c • latticeBasis n a : (lattice n).toAddSubgroup) : Sp n)
    rw [AddSubgroup.coe_zsmul]
    exact h
  rw [intMat, e, map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases hr : r = a
  · subst hr
    simp
  · simp [Ne.symm hr, hr]

theorem intMat_apply_of_eq_zero {T : Module.End ℚ (Sp n)}
    {hT : ∀ s, T (latticeBasis n s : Sp n) ∈ (lattice n).toAddSubgroup} {s : Fin (dimension n)}
    (h : T (latticeBasis n s : Sp n) = 0) (r : Fin (dimension n)) : intMat T hT r s = 0 := by
  have e : (⟨T (latticeBasis n s : Sp n), hT s⟩ : (lattice n).toAddSubgroup) = 0 := by
    apply Subtype.ext
    show T (latticeBasis n s : Sp n) = ((0 : (lattice n).toAddSubgroup) : Sp n)
    rw [h]
    rfl
  rw [intMat, e, map_zero, Finsupp.zero_apply]

end IntMat

@[expose] noncomputable def gamD (a : DI n) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  intMat (spinAction _ (polarization n) (gen n a)) fun s => act_gen_mem n a (latticeBasis n s).2

theorem isIntOp_gen (a : DI n) : IsIntOp n (gen n a) (gamD n a) :=
  hasIntMatrix_intMat _ _

theorem isIntOp_one : IsIntOp n 1 (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) := by
  unfold IsIntOp
  rw [map_one]
  exact HasIntMatrix.one

theorem isIntOp_add {c d : Cl n} {X Y : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (h : IsIntOp n c X) (h' : IsIntOp n d Y) : IsIntOp n (c + d) (X + Y) := by
  unfold IsIntOp at *
  rw [map_add]
  exact HasIntMatrix.add h h'

theorem gamD_anticomm_of {a b : DI n} {c : Cl n}
    {X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : gen n a * gen n b + gen n b * gen n a = c) (hX : IsIntOp n c X) :
    gamD n a * gamD n b + gamD n b * gamD n a = X :=
  ((isIntOp_add n ((isIntOp_gen n a).mul (isIntOp_gen n b))
    ((isIntOp_gen n b).mul (isIntOp_gen n a))).congr hc).eq hX

theorem gamD_anticomm (a b : DI n) :
    gamD n a * gamD n b + gamD n b * gamD n a =
      bmD n a b • (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) := by
  rcases a with i | i <;> rcases b with j | j
  · rw [gamD_anticomm_of n (by rw [gen_inl, gen_inl, Cliff.cr_cr, neg_add_cancel]) IsIntOp.zero,
      bmD_inl_inl, zero_smul]
  · by_cases hij : i = j
    · subst hij
      rw [gamD_anticomm_of n (by rw [gen_inl, gen_inr, Cliff.cr_an_self]) (isIntOp_one n),
        bmD_inl_inr, ite_eq_left rfl, one_smul]
    · rw [gamD_anticomm_of n (by rw [gen_inl, gen_inr, Cliff.cr_an _ hij, neg_add_cancel])
        IsIntOp.zero, bmD_inl_inr, ite_eq_right hij, zero_smul]
  · by_cases hij : i = j
    · subst hij
      rw [gamD_anticomm_of n (by rw [gen_inr, gen_inl, Cliff.an_cr_self]) (isIntOp_one n),
        bmD_inr_inl, ite_eq_left rfl, one_smul]
    · rw [gamD_anticomm_of n (by rw [gen_inr, gen_inl, Cliff.an_cr _ (Ne.symm hij),
        neg_add_cancel]) IsIntOp.zero, bmD_inr_inl, ite_eq_right hij, zero_smul]
  · rw [gamD_anticomm_of n (by rw [gen_inr, gen_inr, Cliff.an_an, neg_add_cancel]) IsIntOp.zero,
      bmD_inr_inr, zero_smul]

theorem gamD_sq (a : DI n) :
    gamD n a * gamD n a =
      qdD n a • (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) := by
  rcases a with i | i
  · rw [((isIntOp_gen n (.inl i)).mul (isIntOp_gen n (.inl i))).eq
      (IsIntOp.zero.congr (by rw [gen_inl, Cliff.cr_sq])), qdD_apply, zero_smul]
  · rw [((isIntOp_gen n (.inr i)).mul (isIntOp_gen n (.inr i))).eq
      (IsIntOp.zero.congr (by rw [gen_inr, Cliff.an_sq])), qdD_apply, zero_smul]

@[expose] noncomputable def posS (S : Finset (Fin n)) : Fin (dimension n) :=
  Fintype.equivFin (Finset (Fin n)) S

theorem signSet_posS (S : Finset (Fin n)) : signSet n (posS n S) = S :=
  (Fintype.equivFin (Finset (Fin n))).symm_apply_apply S

theorem posS_signSet (s : Fin (dimension n)) : posS n (signSet n s) = s :=
  (Fintype.equivFin (Finset (Fin n))).apply_symm_apply s

theorem posS_injective : Function.Injective (posS n) :=
  (Fintype.equivFin (Finset (Fin n))).injective

theorem coe_latticeBasis_posS (S : Finset (Fin n)) :
    (latticeBasis n (posS n S) : Sp n) = (polarizationBasis n).ExteriorAlgebra S := by
  rw [coe_latticeBasis, signSet_posS]

theorem exteriorBasis_empty : (polarizationBasis n).ExteriorAlgebra ∅ = (1 : Sp n) := by
  rw [ExteriorAlgebra.basis_apply]
  simp

@[expose] noncomputable def posD : DI n → Fin (dimension n) × Fin (dimension n)
  | .inl i => (posS n {i}, posS n ∅)
  | .inr i => (posS n ∅, posS n {i})

@[simp] theorem posD_inl (i : Fin n) : posD n (.inl i) = (posS n {i}, posS n ∅) := rfl
@[simp] theorem posD_inr (i : Fin n) : posD n (.inr i) = (posS n ∅, posS n {i}) := rfl

theorem act_cr_empty (j : Fin n) :
    spinAction _ (polarization n) (gen n (.inl j)) (latticeBasis n (posS n ∅) : Sp n) =
      (1 : ℤ) • (latticeBasis n (posS n {j}) : Sp n) := by
  show spinAction _ (polarization n) (crD n j) _ = _
  rw [act_crD, coe_latticeBasis_posS, coe_latticeBasis_posS, exteriorBasis_empty, mul_one,
    TauCeti.ExteriorAlgebra.basis_singleton, one_smul]

theorem act_an_empty (j : Fin n) :
    spinAction _ (polarization n) (gen n (.inr j)) (latticeBasis n (posS n ∅) : Sp n) = 0 := by
  show spinAction _ (polarization n) (anD n j) _ = _
  rw [act_anD, coe_latticeBasis_posS, TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
    ite_eq_right (Finset.notMem_empty j)]

theorem latticeBasis_single (i : Fin n) :
    (latticeBasis n (posS n {i}) : Sp n) =
      spinAction _ (polarization n) (gen n (.inl i)) (latticeBasis n (posS n ∅) : Sp n) := by
  rw [act_cr_empty, one_smul]

theorem act_act (c d : Cl n) (x : Sp n) :
    spinAction _ (polarization n) c (spinAction _ (polarization n) d x) =
      spinAction _ (polarization n) (c * d) x := by
  rw [map_mul, Module.End.mul_apply]

theorem act_add_eq {c d e : Cl n} (h : c + d = e) (x : Sp n) :
    spinAction _ (polarization n) c x + spinAction _ (polarization n) d x =
      spinAction _ (polarization n) e x := by
  rw [← h, map_add, LinearMap.add_apply]

theorem act_one (x : Sp n) :
    spinAction (splitEvenForm ℚ n) (polarization n) (1 : Cl n) x = x := by
  rw [map_one, Module.End.one_apply]

theorem act_zero (x : Sp n) :
    spinAction (splitEvenForm ℚ n) (polarization n) (0 : Cl n) x = 0 := by
  rw [map_zero, LinearMap.zero_apply]

theorem act_cr_an_empty (i j : Fin n) :
    spinAction _ (polarization n) (gen n (.inl i) * gen n (.inr j))
      (latticeBasis n (posS n ∅) : Sp n) = 0 := by
  rw [← act_act, act_an_empty, LinearMap.map_zero]

theorem act_an_single (i j : Fin n) :
    spinAction _ (polarization n) (gen n (.inr j)) (latticeBasis n (posS n {i}) : Sp n) =
      (if j = i then 1 else 0 : ℤ) • (latticeBasis n (posS n ∅) : Sp n) := by
  rw [latticeBasis_single, act_act]
  by_cases h : j = i
  · subst h
    have e := (act_add_eq n (Cliff.an_cr_self (polarizationBasis n) j)
      (latticeBasis n (posS n ∅) : Sp n)).trans (act_one n _)
    have h0 := act_cr_an_empty n j j
    simp only [gen_inl, gen_inr] at h0
    simp only [h0, add_zero] at e
    simp only [ite_eq_left, one_smul]
    exact e
  · have hr : gen n (.inr j) * gen n (.inl i) + gen n (.inl i) * gen n (.inr j) = 0 := by
      show anD n j * crD n i + crD n i * anD n j = 0
      rw [Cliff.an_cr _ (Ne.symm h), neg_add_cancel]
    have e := (act_add_eq n hr (latticeBasis n (posS n ∅) : Sp n)).trans (act_zero n _)
    have h0 := act_cr_an_empty n i j
    simp only [h0, add_zero] at e
    simp only [h, ite_false, zero_smul]
    exact e

theorem act_cr_basis (j : Fin n) (S : Finset (Fin n)) :
    spinAction _ (polarization n) (gen n (.inl j)) (latticeBasis n (posS n S) : Sp n) =
      if j ∈ S then 0 else
        ((TauCeti.ExteriorAlgebra.basisEraseSign j (insert j S) : ℤˣ) : ℤ) •
          (latticeBasis n (posS n (insert j S)) : Sp n) := by
  show spinAction _ (polarization n) (crD n j) _ = _
  rw [act_crD, coe_latticeBasis_posS, coe_latticeBasis_posS,
    TauCeti.ExteriorAlgebra.ι_mul_basis, Units.smul_def]

theorem gamD_cr_single_empty (i j : Fin n) :
    gamD n (.inl j) (posS n ∅) (posS n {i}) = 0 := by
  have h := act_cr_basis n j {i}
  by_cases hji : j ∈ ({i} : Finset (Fin n))
  · rw [ite_eq_left hji] at h
    exact intMat_apply_of_eq_zero h _
  · rw [ite_eq_right hji] at h
    rw [gamD, intMat_apply_of_eq h, ite_eq_right]
    intro he
    have := congrArg (signSet n) he
    rw [signSet_posS, signSet_posS] at this
    exact Finset.insert_ne_empty j {i} this.symm

theorem posS_ne_empty_single (i : Fin n) : posS n {i} ≠ posS n ∅ := fun h => by
  have := congrArg (signSet n) h
  rw [signSet_posS, signSet_posS] at this
  exact Finset.singleton_ne_empty i this

theorem gamD_pos (a b : DI n) :
    gamD n b (posD n a).1 (posD n a).2 = if a = b then 1 else 0 := by
  rcases a with i | i <;> rcases b with j | j
  · rw [posD_inl, gamD, intMat_apply_of_eq (act_cr_empty n j)]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right (fun h => hij (Finset.singleton_injective (posS_injective n h))),
        ite_eq_right (fun h => hij (Sum.inl_injective h))]
  · rw [posD_inl, gamD, intMat_apply_of_eq_zero (act_an_empty n j), ite_eq_right Sum.inl_ne_inr]
  · rw [posD_inr, gamD_cr_single_empty, ite_eq_right Sum.inr_ne_inl]
  · rw [posD_inr, gamD, intMat_apply_of_eq (act_an_single n i j), ite_eq_left rfl]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij), ite_eq_right (fun h => hij (Sum.inr_injective h))]

@[expose] noncomputable def frame : Frame (bmD n) (qdD n) (Fin (dimension n)) where
  gam := gamD n
  anticomm := gamD_anticomm n
  sq := gamD_sq n
  pos := posD n
  gam_pos := gamD_pos n

theorem frame_gam : (frame n).gam = gamD n :=
  rfl

section Roots

variable (hn : 4 ≤ n)

theorem rootIntMatrix_inl_lt (i : Fin n) (hi : i.val + 1 < n) :
    rootIntMatrix n hn (.inl i) = gamD n (.inl i) * gamD n (.inr ⟨i.val + 1, hi⟩) :=
  ((isIntOp_E n hn i).congr (chainE_eq n (by omega) i hi)).eq
    ((isIntOp_gen n (.inl i)).mul (isIntOp_gen n (.inr ⟨i.val + 1, hi⟩)))

theorem rootIntMatrix_inr_lt (i : Fin n) (hi : i.val + 1 < n) :
    rootIntMatrix n hn (.inr i) = gamD n (.inl ⟨i.val + 1, hi⟩) * gamD n (.inr i) :=
  ((isIntOp_F n hn i).congr (chainF_eq n (by omega) i hi)).eq
    ((isIntOp_gen n (.inl ⟨i.val + 1, hi⟩)).mul (isIntOp_gen n (.inr i)))

theorem rootIntMatrix_inl_fork :
    rootIntMatrix n hn (.inl ⟨n - 1, by omega⟩) =
      gamD n (.inl ⟨n - 2, by omega⟩) * gamD n (.inl ⟨n - 1, by omega⟩) :=
  ((isIntOp_E n hn ⟨n - 1, by omega⟩).congr
    (Fork.Eb_eq (polarization n) (polarizationBasis n) (by omega))).eq
    ((isIntOp_gen n (.inl ⟨n - 2, by omega⟩)).mul (isIntOp_gen n (.inl ⟨n - 1, by omega⟩)))

theorem rootIntMatrix_inr_fork :
    rootIntMatrix n hn (.inr ⟨n - 1, by omega⟩) =
      gamD n (.inr ⟨n - 1, by omega⟩) * gamD n (.inr ⟨n - 2, by omega⟩) :=
  ((isIntOp_F n hn ⟨n - 1, by omega⟩).congr
    (Fork.Fb_eq (polarization n) (polarizationBasis n) (by omega))).eq
    ((isIntOp_gen n (.inr ⟨n - 1, by omega⟩)).mul (isIntOp_gen n (.inr ⟨n - 2, by omega⟩)))

end Roots

theorem act_an_basis (j : Fin n) (S : Finset (Fin n)) :
    spinAction _ (polarization n) (gen n (.inr j)) (latticeBasis n (posS n S) : Sp n) =
      if j ∈ S then
        ((TauCeti.ExteriorAlgebra.basisEraseSign j S : ℤˣ) : ℤ) •
          (latticeBasis n (posS n (S.erase j)) : Sp n)
      else 0 := by
  show spinAction _ (polarization n) (anD n j) _ = _
  rw [act_anD, coe_latticeBasis_posS, coe_latticeBasis_posS,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis, Units.smul_def]

theorem act_cr_an_basis (i : Fin n) (S : Finset (Fin n)) :
    spinAction _ (polarization n) (gen n (.inl i) * gen n (.inr i))
        (latticeBasis n (posS n S) : Sp n) =
      (if i ∈ S then 1 else 0 : ℤ) • (latticeBasis n (posS n S) : Sp n) := by
  rw [← act_act]
  by_cases hi : i ∈ S
  · have hσ : ((TauCeti.ExteriorAlgebra.basisEraseSign i S : ℤˣ) : ℤ) *
        ((TauCeti.ExteriorAlgebra.basisEraseSign i S : ℤˣ) : ℤ) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
    simp only [act_an_basis, hi, ite_true, map_zsmul, act_cr_basis, Finset.notMem_erase,
      ite_false, Finset.insert_erase hi, smul_smul, hσ]
  · simp only [act_an_basis, hi, ite_false, map_zero, zero_smul]

theorem gamD_cr_mul_gamD_an (i : Fin n) :
    gamD n (.inl i) * gamD n (.inr i) =
      Matrix.diagonal fun s => if i ∈ signSet n s then (1 : ℤ) else 0 := by
  refine ((isIntOp_gen n (.inl i)).mul (isIntOp_gen n (.inr i))).eq fun s => ?_
  have h := act_cr_an_basis n i (signSet n s)
  rw [posS_signSet n s] at h
  refine h.trans ?_
  rw [Finset.sum_eq_single s (fun r _ hr => by rw [Matrix.diagonal_apply_ne _ hr, zero_smul])
    (by simp), Matrix.diagonal_apply_eq]

theorem gamD_cr_apply (i : Fin n) {s : Fin (dimension n)} (hi : i ∉ signSet n s)
    (r : Fin (dimension n)) :
    gamD n (.inl i) r s = if r = posS n (insert i (signSet n s)) then
      ((TauCeti.ExteriorAlgebra.basisEraseSign i (insert i (signSet n s)) : ℤˣ) : ℤ) else 0 := by
  have h := act_cr_basis n i (signSet n s)
  rw [ite_eq_right hi, posS_signSet] at h
  exact intMat_apply_of_eq h r

theorem eq_smul_one_of_commute {K : Type*} [CommRing K]
    (g : Matrix (Fin (dimension n)) (Fin (dimension n)) K)
    (hg : ∀ a, g * (frame n).gamA K a = (frame n).gamA K a * g) :
    g = g (posS n ∅) (posS n ∅) • (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) K) := by
  have hD : ∀ i, g * Matrix.diagonal (fun s => if i ∈ signSet n s then (1 : K) else 0) =
      Matrix.diagonal (fun s => if i ∈ signSet n s then (1 : K) else 0) * g := fun i => by
    have e : (frame n).gamA K (.inl i) * (frame n).gamA K (.inr i) =
        Matrix.diagonal (fun s => if i ∈ signSet n s then (1 : K) else 0) := by
      rw [Frame.gamA, Frame.gamA, frame_gam, ← map_mul, gamD_cr_mul_gamD_an]
      ext r s
      by_cases hrs : r = s
      · subst hrs
        simp [apply_ite (Int.cast : ℤ → K)]
      · simp [Matrix.diagonal_apply_ne _ hrs]
    rw [← e, ← mul_assoc, hg, mul_assoc, hg, mul_assoc]
  have hoff : ∀ r s, r ≠ s → g r s = 0 := by
    intro r s hrs
    have hS : signSet n r ≠ signSet n s := fun h => hrs (by
      rw [← posS_signSet n r, ← posS_signSet n s, h])
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ signSet n r ↔ i ∈ signSet n s) := by
      by_contra h
      push Not at h
      exact hS (Finset.ext h)
    have h := congrFun (congrFun (hD i) r) s
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    by_cases hr : i ∈ signSet n r
    · have hs : i ∉ signSet n s := fun hs => hi ⟨fun _ => hs, fun _ => hr⟩
      rw [ite_eq_left hr, ite_eq_right hs, mul_zero, one_mul] at h
      exact h.symm
    · have hs : i ∈ signSet n s := by
        by_contra hs
        exact hi ⟨fun h => absurd h hr, fun h => absurd h hs⟩
      rw [ite_eq_right hr, ite_eq_left hs, mul_one, zero_mul] at h
      exact h
  have hstep : ∀ (S : Finset (Fin n)) (i : Fin n), i ∉ S →
      g (posS n (insert i S)) (posS n (insert i S)) = g (posS n S) (posS n S) := by
    intro S i hi
    have hi' : i ∉ signSet n (posS n S) := by rwa [signSet_posS]
    have h := congrFun (congrFun (hg (.inl i)) (posS n (insert i S))) (posS n S)
    rw [Matrix.mul_apply, Matrix.mul_apply,
      Finset.sum_eq_single (posS n (insert i S)) (fun t _ ht => by rw [hoff _ _ (Ne.symm ht),
        zero_mul]) (by simp),
      Finset.sum_eq_single (posS n S) (fun t _ ht => by rw [hoff _ _ ht, mul_zero]) (by simp)] at h
    rw [Frame.gamA, frame_gam, RingHom.mapMatrix_apply, Matrix.map_apply,
      gamD_cr_apply n i hi', signSet_posS, ite_eq_left rfl] at h
    set σ := ((TauCeti.ExteriorAlgebra.basisEraseSign i (insert i S) : ℤˣ) : ℤ)
    have hσ : ((σ : ℤ) : K) * (σ : K) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    calc g (posS n (insert i S)) (posS n (insert i S))
        = g (posS n (insert i S)) (posS n (insert i S)) * ((σ : K) * (σ : K)) := by
          rw [hσ, mul_one]
      _ = (σ : K) * g (posS n S) (posS n S) * (σ : K) := by
          rw [← mul_assoc]
          simp only [Int.coe_castRingHom] at h
          rw [h]
      _ = g (posS n S) (posS n S) := by
          rw [mul_comm (σ : K), mul_assoc, hσ, mul_one]
  have hdiag : ∀ S : Finset (Fin n), g (posS n S) (posS n S) = g (posS n ∅) (posS n ∅) := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert i S hi ih => rw [hstep S i hi, ih]
  ext r s
  rw [Matrix.smul_apply, smul_eq_mul]
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.one_apply_eq, mul_one, ← hdiag (signSet n r), posS_signSet]
  · rw [Matrix.one_apply_ne hrs, mul_zero, hoff r s hrs]

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD

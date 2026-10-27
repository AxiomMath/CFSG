module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinFrame
public import CFSG.RankThree.PartTwo.Census.Spin.CarrierBTheta

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open TauCeti TauCeti.TypeBSpinCarrier CFSG.RankThree.PartTwo.Census.Spin
open CFSG.RankThree.PartTwo.Census.Spin.CarrierB SpinFrame SpinFrame.BI

variable (n : ℕ)

abbrev Sp : Type :=
  ExteriorAlgebra ℚ (polarization n).W

@[expose] noncomputable def gen : BI (n + 1) → Cl n
  | .inl i => crB n i
  | .inr (.inl i) => anB n i
  | .inr (.inr _) => zeta n

@[simp] theorem gen_cr (i : Fin (n + 1)) : gen n (cr i) = crB n i := rfl
@[simp] theorem gen_an (i : Fin (n + 1)) : gen n (an i) = anB n i := rfl
@[simp] theorem gen_zeta : gen n BI.zeta = CarrierB.zeta n := rfl

theorem act_crB (i : Fin (n + 1)) (x : Sp n) :
    spinAction _ (polarization n) (crB n i) x = ExteriorAlgebra.ι ℚ (polarizationBasis n i) * x :=
  spinAction_ι_wedge (polarization n) (polarizationBasis n i) x

theorem act_anB (i : Fin (n + 1)) (x : Sp n) :
    spinAction _ (polarization n) (anB n i) x =
      CliffordAlgebra.contractLeft ((polarizationBasis n).coord i) x := by
  have h1 := spinAction_ι_contract (polarization n)
    ((polarization n).dualVector (polarizationBasis n) i) x
  have h3 := SpinPolarizationData.pairingEquiv_dualVector (polarization n)
    (polarizationBasis n) i
  rw [h3] at h1
  exact h1

theorem act_zeta (x : Sp n) :
    spinAction _ (polarization n) (zeta n) x = CliffordAlgebra.involute x :=
  spinAction_zeta n x

theorem act_gen_mem (a : BI (n + 1)) {x : Sp n} (hx : x ∈ lattice n) :
    spinAction _ (polarization n) (gen n a) x ∈ lattice n := by
  rcases a with i | i | u
  · rw [gen, act_crB]
    exact TauCeti.ExteriorAlgebra.ι_basis_mul_mem_integralLattice _ i hx
  · rw [gen, act_anB]
    exact TauCeti.ExteriorAlgebra.contractLeft_coord_mem_integralLattice _ i hx
  · rw [gen, act_zeta]
    exact TauCeti.ExteriorAlgebra.involute_mem_integralLattice _ hx

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

@[expose] noncomputable def gamB (a : BI (n + 1)) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  intMat (spinAction _ (polarization n) (gen n a)) fun s => act_gen_mem n a (latticeBasis n s).2

theorem isIntOp_gen (a : BI (n + 1)) : IsIntOp n (gen n a) (gamB n a) :=
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

theorem bi_cases (a : BI (n + 1)) : (∃ i, a = cr i) ∨ (∃ i, a = an i) ∨ a = BI.zeta := by
  rcases a with i | i | u
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · exact Or.inr (Or.inr rfl)

theorem gamB_anticomm_of {a b : BI (n + 1)} {c : Cl n}
    {X : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hc : gen n a * gen n b + gen n b * gen n a = c) (hX : IsIntOp n c X) :
    gamB n a * gamB n b + gamB n b * gamB n a = X :=
  ((isIntOp_add n ((isIntOp_gen n a).mul (isIntOp_gen n b))
    ((isIntOp_gen n b).mul (isIntOp_gen n a))).congr hc).eq hX

theorem gamB_anticomm (a b : BI (n + 1)) :
    gamB n a * gamB n b + gamB n b * gamB n a =
      bmB (n + 1) a b • (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) := by
  rcases bi_cases n a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
    rcases bi_cases n b with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · rw [gamB_anticomm_of n (by rw [gen_cr, gen_cr, Cliff.cr_cr, neg_add_cancel]) IsIntOp.zero,
      bmB_cr_cr, zero_smul]
  · by_cases hij : i = j
    · subst hij
      rw [gamB_anticomm_of n (by rw [gen_cr, gen_an, Cliff.cr_an_self]) (isIntOp_one n),
        bmB_cr_an, ite_eq_left rfl, one_smul]
    · rw [gamB_anticomm_of n (by rw [gen_cr, gen_an, Cliff.cr_an _ hij, neg_add_cancel])
        IsIntOp.zero, bmB_cr_an, ite_eq_right hij, zero_smul]
  · rw [gamB_anticomm_of n (by rw [gen_cr, gen_zeta, cr_zeta, neg_add_cancel]) IsIntOp.zero,
      bmB_cr_zeta, zero_smul]
  · by_cases hij : i = j
    · subst hij
      rw [gamB_anticomm_of n (by rw [gen_an, gen_cr, Cliff.an_cr_self]) (isIntOp_one n),
        bmB_an_cr, ite_eq_left rfl, one_smul]
    · rw [gamB_anticomm_of n (by rw [gen_an, gen_cr, Cliff.an_cr _ (Ne.symm hij),
        neg_add_cancel]) IsIntOp.zero, bmB_an_cr, ite_eq_right hij, zero_smul]
  · rw [gamB_anticomm_of n (by rw [gen_an, gen_an, Cliff.an_an, neg_add_cancel]) IsIntOp.zero,
      bmB_an_an, zero_smul]
  · rw [gamB_anticomm_of n (by rw [gen_an, gen_zeta, an_zeta, neg_add_cancel]) IsIntOp.zero,
      bmB_an_zeta, zero_smul]
  · rw [gamB_anticomm_of n (by rw [gen_zeta, gen_cr, zeta_cr, neg_add_cancel]) IsIntOp.zero,
      bmB_zeta_cr, zero_smul]
  · rw [gamB_anticomm_of n (by rw [gen_zeta, gen_an, zeta_an, neg_add_cancel]) IsIntOp.zero,
      bmB_zeta_an, zero_smul]
  · rw [gamB_anticomm_of n (by rw [gen_zeta, zeta_sq])
      (isIntOp_add n (isIntOp_one n) (isIntOp_one n)), bmB_zeta_zeta, two_smul]

theorem gamB_sq (a : BI (n + 1)) :
    gamB n a * gamB n a =
      qdB (n + 1) a • (1 : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ) := by
  rcases bi_cases n a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl
  · rw [((isIntOp_gen n (cr i)).mul (isIntOp_gen n (cr i))).eq
      (IsIntOp.zero.congr (by rw [gen_cr, Cliff.cr_sq])), qdB_cr, zero_smul]
  · rw [((isIntOp_gen n (an i)).mul (isIntOp_gen n (an i))).eq
      (IsIntOp.zero.congr (by rw [gen_an, Cliff.an_sq])), qdB_an, zero_smul]
  · rw [((isIntOp_gen n BI.zeta).mul (isIntOp_gen n BI.zeta)).eq
      ((isIntOp_one n).congr (by rw [gen_zeta, zeta_sq])), qdB_zeta, one_smul]

@[expose] noncomputable def posS (S : Finset (Fin (n + 1))) : Fin (dimension n) :=
  Fintype.equivFin (Finset (Fin (n + 1))) S

theorem signSet_posS (S : Finset (Fin (n + 1))) : signSet n (posS n S) = S :=
  (Fintype.equivFin (Finset (Fin (n + 1)))).symm_apply_apply S

theorem posS_signSet (s : Fin (dimension n)) : posS n (signSet n s) = s :=
  (Fintype.equivFin (Finset (Fin (n + 1)))).apply_symm_apply s

theorem posS_injective : Function.Injective (posS n) :=
  (Fintype.equivFin (Finset (Fin (n + 1)))).injective

theorem coe_latticeBasis_posS (S : Finset (Fin (n + 1))) :
    (latticeBasis n (posS n S) : Sp n) = (polarizationBasis n).ExteriorAlgebra S := by
  rw [coe_latticeBasis, signSet_posS]

theorem exteriorBasis_empty : (polarizationBasis n).ExteriorAlgebra ∅ = (1 : Sp n) := by
  rw [ExteriorAlgebra.basis_apply]
  simp

@[expose] noncomputable def posB : BI (n + 1) → Fin (dimension n) × Fin (dimension n)
  | .inl i => (posS n {i}, posS n ∅)
  | .inr (.inl i) => (posS n ∅, posS n {i})
  | .inr (.inr _) => (posS n ∅, posS n ∅)

@[simp] theorem posB_cr (i : Fin (n + 1)) : posB n (cr i) = (posS n {i}, posS n ∅) := rfl
@[simp] theorem posB_an (i : Fin (n + 1)) : posB n (an i) = (posS n ∅, posS n {i}) := rfl
@[simp] theorem posB_zeta : posB n BI.zeta = (posS n ∅, posS n ∅) := rfl

theorem act_cr_empty (j : Fin (n + 1)) :
    spinAction _ (polarization n) (gen n (cr j)) (latticeBasis n (posS n ∅) : Sp n) =
      (1 : ℤ) • (latticeBasis n (posS n {j}) : Sp n) := by
  show spinAction _ (polarization n) (crB n j) _ = _
  rw [act_crB, coe_latticeBasis_posS, coe_latticeBasis_posS, exteriorBasis_empty, mul_one,
    TauCeti.ExteriorAlgebra.basis_singleton, one_smul]

theorem act_an_empty (j : Fin (n + 1)) :
    spinAction _ (polarization n) (gen n (an j)) (latticeBasis n (posS n ∅) : Sp n) = 0 := by
  show spinAction _ (polarization n) (anB n j) _ = _
  rw [act_anB, coe_latticeBasis_posS, TauCeti.ExteriorAlgebra.contractLeft_coord_basis,
    ite_eq_right (Finset.notMem_empty j)]

theorem act_zeta_empty :
    spinAction _ (polarization n) (gen n BI.zeta) (latticeBasis n (posS n ∅) : Sp n) =
      (1 : ℤ) • (latticeBasis n (posS n ∅) : Sp n) := by
  show spinAction _ (polarization n) (zeta n) _ = _
  rw [act_zeta, coe_latticeBasis_posS, TauCeti.ExteriorAlgebra.involute_basis,
    Finset.card_empty, pow_zero, one_smul, one_smul]

theorem latticeBasis_single (i : Fin (n + 1)) :
    (latticeBasis n (posS n {i}) : Sp n) =
      spinAction _ (polarization n) (gen n (cr i)) (latticeBasis n (posS n ∅) : Sp n) := by
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
    spinAction (splitOddForm ℚ (n + 1)) (polarization n) (1 : Cl n) x = x := by
  rw [map_one, Module.End.one_apply]

theorem act_zero (x : Sp n) :
    spinAction (splitOddForm ℚ (n + 1)) (polarization n) (0 : Cl n) x = 0 := by
  rw [map_zero, LinearMap.zero_apply]

theorem act_cr_an_empty (i j : Fin (n + 1)) :
    spinAction _ (polarization n) (gen n (cr i) * gen n (an j))
      (latticeBasis n (posS n ∅) : Sp n) = 0 := by
  rw [← act_act, act_an_empty, LinearMap.map_zero]

theorem act_an_single (i j : Fin (n + 1)) :
    spinAction _ (polarization n) (gen n (an j)) (latticeBasis n (posS n {i}) : Sp n) =
      (if j = i then 1 else 0 : ℤ) • (latticeBasis n (posS n ∅) : Sp n) := by
  rw [latticeBasis_single, act_act]
  by_cases h : j = i
  · subst h
    have e := (act_add_eq n (Cliff.an_cr_self (polarizationBasis n) j)
      (latticeBasis n (posS n ∅) : Sp n)).trans (act_one n _)
    have h0 := act_cr_an_empty n j j
    simp only [gen_cr, gen_an] at h0
    simp only [h0, add_zero] at e
    simp only [ite_eq_left, one_smul]
    exact e
  · have hr : gen n (an j) * gen n (cr i) + gen n (cr i) * gen n (an j) = 0 := by
      show anB n j * crB n i + crB n i * anB n j = 0
      rw [Cliff.an_cr _ (Ne.symm h), neg_add_cancel]
    have e := (act_add_eq n hr (latticeBasis n (posS n ∅) : Sp n)).trans (act_zero n _)
    have h0 := act_cr_an_empty n i j
    simp only [h0, add_zero] at e
    simp only [h, ite_false, zero_smul]
    exact e

theorem act_zeta_single (i : Fin (n + 1)) :
    spinAction _ (polarization n) (gen n BI.zeta) (latticeBasis n (posS n {i}) : Sp n) =
      (-1 : ℤ) • (latticeBasis n (posS n {i}) : Sp n) := by
  have hr : gen n BI.zeta * gen n (cr i) + gen n (cr i) * gen n BI.zeta = 0 := by
    show CarrierB.zeta n * crB n i + crB n i * CarrierB.zeta n = 0
    rw [zeta_cr, neg_add_cancel]
  have e := (act_add_eq n hr (latticeBasis n (posS n ∅) : Sp n)).trans (act_zero n _)
  have h1 : spinAction _ (polarization n) (gen n (cr i) * gen n BI.zeta)
      (latticeBasis n (posS n ∅) : Sp n) = (latticeBasis n (posS n {i}) : Sp n) := by
    rw [← act_act, act_zeta_empty, one_smul, ← latticeBasis_single n i]
  simp only [h1] at e
  have e2 := eq_neg_of_add_eq_zero_left e
  rw [← act_act n (gen n BI.zeta) (gen n (cr i))] at e2
  simp only [← latticeBasis_single n i] at e2
  simp only [e2, neg_one_smul]

theorem act_cr_basis (j : Fin (n + 1)) (S : Finset (Fin (n + 1))) :
    spinAction _ (polarization n) (gen n (cr j)) (latticeBasis n (posS n S) : Sp n) =
      if j ∈ S then 0 else
        ((TauCeti.ExteriorAlgebra.basisEraseSign j (insert j S) : ℤˣ) : ℤ) •
          (latticeBasis n (posS n (insert j S)) : Sp n) := by
  show spinAction _ (polarization n) (crB n j) _ = _
  rw [act_crB, coe_latticeBasis_posS, coe_latticeBasis_posS,
    TauCeti.ExteriorAlgebra.ι_mul_basis, Units.smul_def]

theorem gamB_cr_single_empty (i j : Fin (n + 1)) : gamB n (cr j) (posS n ∅) (posS n {i}) = 0 := by
  have h := act_cr_basis n j {i}
  by_cases hji : j ∈ ({i} : Finset (Fin (n + 1)))
  · rw [ite_eq_left hji] at h
    exact intMat_apply_of_eq_zero h _
  · rw [ite_eq_right hji] at h
    rw [gamB, intMat_apply_of_eq h, ite_eq_right]
    intro he
    have := congrArg (signSet n) he
    rw [signSet_posS, signSet_posS] at this
    exact Finset.insert_ne_empty j {i} this.symm

theorem posS_ne_empty_single (i : Fin (n + 1)) : posS n {i} ≠ posS n ∅ := fun h => by
  have := congrArg (signSet n) h
  rw [signSet_posS, signSet_posS] at this
  exact Finset.singleton_ne_empty i this

theorem gamB_pos (a b : BI (n + 1)) :
    gamB n b (posB n a).1 (posB n a).2 = if a = b then 1 else 0 := by
  rcases bi_cases n a with ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl <;>
    rcases bi_cases n b with ⟨j, rfl⟩ | ⟨j, rfl⟩ | rfl
  · rw [posB_cr, gamB, intMat_apply_of_eq (act_cr_empty n j)]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right (fun h => hij (Finset.singleton_injective (posS_injective n h))),
        ite_eq_right (fun h => hij (Sum.inl_injective h))]
  · rw [posB_cr, gamB, intMat_apply_of_eq_zero (act_an_empty n j), ite_eq_right Sum.inl_ne_inr]
  · rw [posB_cr, gamB, intMat_apply_of_eq (act_zeta_empty n),
      ite_eq_right (posS_ne_empty_single n i),
      ite_eq_right Sum.inl_ne_inr]
  · rw [posB_an, gamB_cr_single_empty, ite_eq_right Sum.inr_ne_inl]
  · rw [posB_an, gamB, intMat_apply_of_eq (act_an_single n i j), ite_eq_left rfl]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [ite_eq_right (Ne.symm hij),
        ite_eq_right (fun h => hij (Sum.inl_injective (Sum.inr_injective h)))]
  · rw [posB_an, gamB, intMat_apply_of_eq (act_zeta_single n i),
      ite_eq_right (posS_ne_empty_single n i).symm,
      ite_eq_right (fun h => Sum.inl_ne_inr (Sum.inr_injective h))]
  · rw [posB_zeta, gamB, intMat_apply_of_eq (act_cr_empty n j),
      ite_eq_right (posS_ne_empty_single n j).symm, ite_eq_right Sum.inr_ne_inl]
  · rw [posB_zeta, gamB, intMat_apply_of_eq_zero (act_an_empty n j),
      ite_eq_right (fun h => Sum.inr_ne_inl (Sum.inr_injective h))]
  · rw [posB_zeta, gamB, intMat_apply_of_eq (act_zeta_empty n), ite_eq_left rfl, ite_eq_left rfl]

@[expose] noncomputable def frame : Frame (bmB (n + 1)) (qdB (n + 1)) (Fin (dimension n)) where
  gam := gamB n
  anticomm := gamB_anticomm n
  sq := gamB_sq n
  pos := posB n
  gam_pos := gamB_pos n

theorem frame_gam : (frame n).gam = gamB n :=
  rfl

theorem rootIntMatrix_inl_lt (i : Fin (n + 1)) (hi : i.val < n) :
    rootIntMatrix n (.inl i) = gamB n (cr i) * gamB n (an ⟨i.val + 1, by omega⟩) :=
  (isIntOp_E_lt n i hi).eq ((isIntOp_gen n (cr i)).mul (isIntOp_gen n (an ⟨i.val + 1, by omega⟩)))

theorem rootIntMatrix_inr_lt (i : Fin (n + 1)) (hi : i.val < n) :
    rootIntMatrix n (.inr i) = gamB n (cr ⟨i.val + 1, by omega⟩) * gamB n (an i) :=
  (isIntOp_F_lt n i hi).eq ((isIntOp_gen n (cr ⟨i.val + 1, by omega⟩)).mul (isIntOp_gen n (an i)))

theorem rootIntMatrix_inl_last :
    rootIntMatrix n (.inl (Fin.last n)) = gamB n (cr (Fin.last n)) * gamB n BI.zeta :=
  (isIntOp_E_last n).eq ((isIntOp_gen n (cr (Fin.last n))).mul (isIntOp_gen n BI.zeta))

theorem rootIntMatrix_inr_last :
    rootIntMatrix n (.inr (Fin.last n)) = gamB n BI.zeta * gamB n (an (Fin.last n)) :=
  (isIntOp_F_last n).eq ((isIntOp_gen n BI.zeta).mul (isIntOp_gen n (an (Fin.last n))))

theorem act_an_basis (j : Fin (n + 1)) (S : Finset (Fin (n + 1))) :
    spinAction _ (polarization n) (gen n (an j)) (latticeBasis n (posS n S) : Sp n) =
      if j ∈ S then
        ((TauCeti.ExteriorAlgebra.basisEraseSign j S : ℤˣ) : ℤ) •
          (latticeBasis n (posS n (S.erase j)) : Sp n)
      else 0 := by
  show spinAction _ (polarization n) (anB n j) _ = _
  rw [act_anB, coe_latticeBasis_posS, coe_latticeBasis_posS,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis, Units.smul_def]

theorem act_cr_an_basis (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) :
    spinAction _ (polarization n) (gen n (cr i) * gen n (an i))
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

theorem gamB_cr_mul_gamB_an (i : Fin (n + 1)) :
    gamB n (cr i) * gamB n (an i) =
      Matrix.diagonal fun s => if i ∈ signSet n s then (1 : ℤ) else 0 := by
  refine ((isIntOp_gen n (cr i)).mul (isIntOp_gen n (an i))).eq fun s => ?_
  have h := act_cr_an_basis n i (signSet n s)
  rw [posS_signSet n s] at h
  refine h.trans ?_
  rw [Finset.sum_eq_single s (fun r _ hr => by rw [Matrix.diagonal_apply_ne _ hr, zero_smul])
    (by simp), Matrix.diagonal_apply_eq]

theorem gamB_cr_apply (i : Fin (n + 1)) {s : Fin (dimension n)} (hi : i ∉ signSet n s)
    (r : Fin (dimension n)) :
    gamB n (cr i) r s = if r = posS n (insert i (signSet n s)) then
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
    have e : (frame n).gamA K (cr i) * (frame n).gamA K (an i) =
        Matrix.diagonal (fun s => if i ∈ signSet n s then (1 : K) else 0) := by
      rw [Frame.gamA, Frame.gamA, frame_gam, ← map_mul, gamB_cr_mul_gamB_an]
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
  have hstep : ∀ (S : Finset (Fin (n + 1))) (i : Fin (n + 1)), i ∉ S →
      g (posS n (insert i S)) (posS n (insert i S)) = g (posS n S) (posS n S) := by
    intro S i hi
    have hi' : i ∉ signSet n (posS n S) := by rwa [signSet_posS]
    have h := congrFun (congrFun (hg (cr i)) (posS n (insert i S))) (posS n S)
    rw [Matrix.mul_apply, Matrix.mul_apply,
      Finset.sum_eq_single (posS n (insert i S)) (fun t _ ht => by rw [hoff _ _ (Ne.symm ht),
        zero_mul]) (by simp),
      Finset.sum_eq_single (posS n S) (fun t _ ht => by rw [hoff _ _ ht, mul_zero]) (by simp)] at h
    rw [Frame.gamA, frame_gam, RingHom.mapMatrix_apply, Matrix.map_apply,
      gamB_cr_apply n i hi', signSet_posS, ite_eq_left rfl] at h
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
  have hdiag : ∀ S : Finset (Fin (n + 1)), g (posS n S) (posS n S) = g (posS n ∅) (posS n ∅) := by
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

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB

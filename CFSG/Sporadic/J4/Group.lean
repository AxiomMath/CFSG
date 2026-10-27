module

public import CFSG.Sporadic.J4.Setup

public section

namespace CFSG.Sporadic.J4

open Native Matrix

@[expose] noncomputable def gA : GL (Fin 112) (ZMod 2) :=
  @dite _ (matA.det ≠ 0) (Classical.propDecidable _)
    (fun h => Matrix.GeneralLinearGroup.mkOfDetNeZero matA h) (fun _ => 1)

@[expose] noncomputable def gB : GL (Fin 112) (ZMod 2) :=
  @dite _ (matB.det ≠ 0) (Classical.propDecidable _)
    (fun h => Matrix.GeneralLinearGroup.mkOfDetNeZero matB h) (fun _ => 1)

noncomputable abbrev J : Subgroup (GL (Fin 112) (ZMod 2)) := Subgroup.closure {gA, gB}

@[expose] noncomputable def a : J := ⟨gA, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J := ⟨gB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem a_coe : (a : GL (Fin 112) (ZMod 2)) = gA := Subtype.coe_mk _ _

theorem b_coe : (b : GL (Fin 112) (ZMod 2)) = gB := Subtype.coe_mk _ _

theorem closure_ab : Subgroup.closure ({a, b} : Set J) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA, gB} : Set (GL (Fin 112) (ZMod 2)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl a_coe
    · exact Or.inr b_coe
  · rintro (h | h)
    · exact Or.inl (Subtype.ext (h.trans a_coe.symm))
    · exact Or.inr (Subtype.ext (h.trans b_coe.symm))

section Facts

variable (hM : MatFacts)
include hM

theorem matA_sq : matA ^ 2 = 1 := by
  have := congrArg rowsMatrix (eqRows_iff.1 hM.a2)
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsA] at this

theorem matB_pow_four : matB ^ 4 = 1 := by
  have := congrArg rowsMatrix (eqRows_iff.1 hM.b4)
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsB] at this

theorem det_matA_ne_zero : matA.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (matA_sq hM)
  rw [Matrix.det_pow, h, zero_pow two_ne_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_matB_ne_zero : matB.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (matB_pow_four hM)
  rw [Matrix.det_pow, h, zero_pow four_ne_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem gA_eq : gA = Matrix.GeneralLinearGroup.mkOfDetNeZero matA (det_matA_ne_zero hM) := by
  unfold gA; rw [dite_eq_left (det_matA_ne_zero hM)]

theorem gB_eq : gB = Matrix.GeneralLinearGroup.mkOfDetNeZero matB (det_matB_ne_zero hM) := by
  unfold gB; rw [dite_eq_left (det_matB_ne_zero hM)]

theorem gA_val : ((gA : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = matA := by
  rw [gA_eq hM]; rfl

theorem gB_val : ((gB : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = matB := by
  rw [gB_eq hM]; rfl

noncomputable def seedEquiv : Blueprint.NativeSporadic.J4 ≃* J :=
  (Blueprint.NativeSporadic.matrixSeedEquiv 2 112 (by norm_num) matA matB (det_matA_ne_zero hM)
    (det_matB_ne_zero hM)).trans (MulEquiv.subgroupCongr (by
      show _ = Subgroup.closure {gA, gB}
      rw [gA_eq hM, gB_eq hM]))

end Facts

@[expose] noncomputable def baseGL (m : ℕ) : GL (Fin 112) (ZMod 2) :=
  if m = 0 then gA else if m = 1 then gB else 1

@[expose] noncomputable def locGL (k : ℕ) : GL (Fin 112) (ZMod 2) :=
  wordProd baseGL (localWords[k]?.getD [])

@[expose] noncomputable def stabGL (k : ℕ) : GL (Fin 112) (ZMod 2) :=
  wordProd locGL (stabWords[k]?.getD [])

@[expose] noncomputable def conjGL : GL (Fin 112) (ZMod 2) := wordProd baseGL conjWord

theorem baseGL_mem (m : ℕ) : baseGL m ∈ J := by
  unfold baseGL
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact J.one_mem

theorem locGL_mem (k : ℕ) : locGL k ∈ J := wordProd_mem J baseGL_mem _

theorem conjGL_mem : conjGL ∈ J := wordProd_mem J baseGL_mem _

noncomputable abbrev Hgl : Subgroup (GL (Fin 112) (ZMod 2)) :=
  Subgroup.closure {locGL 0, locGL 1, locGL 2}

theorem locGL_mem_Hgl {k : ℕ} (hk : k < 3) : locGL k ∈ Hgl := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem locGL_mem_Hgl' (k : ℕ) : locGL k ∈ Hgl := by
  by_cases hk : k < 3
  · exact locGL_mem_Hgl hk
  · have : localWords[k]? = none := by
      rw [List.getElem?_eq_none_iff]; simp only [localWords, List.length_cons, List.length_nil]
      omega
    rw [locGL, this, Option.getD_none, wordProd, List.map_nil, List.prod_nil]
    exact Hgl.one_mem

theorem stabGL_mem_Hgl (k : ℕ) : stabGL k ∈ Hgl := wordProd_mem Hgl locGL_mem_Hgl' _

theorem Hgl_le_J : Hgl ≤ J := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl) <;> exact locGL_mem _

section Mat

variable (hM : MatFacts)
include hM

omit hM in
theorem invs_of_invsOK {mats invs : Array (Array V2)} (h : invsOK mats invs = true) {k : ℕ}
    (hk : k < mats.size) :
    rowsMatrix (mats[k]?.getD idRows) * rowsMatrix (invs[k]?.getD idRows) = 1 := by
  unfold invsOK at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  have := h.2 k (List.mem_range.2 hk)
  have e := congrArg rowsMatrix (eqRows_iff.1 this)
  rw [rowsMatrix_mulRows, rowsMatrix_idRows] at e
  rwa [Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem (h.1 ▸ hk), Option.getD_some,
    Option.getD_some, ← getElem!_pos mats k hk, ← getElem!_pos invs k (h.1 ▸ hk)]

theorem baseMats_spec (m : ℕ) : rowsMatrix (baseMats[m]?.getD idRows) =
    ((baseGL m : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  unfold baseGL
  obtain rfl | rfl | hm : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
  · simp only [baseMats, ite_eq_left]
    rw [show (#[rowsA, rowsB] : Array (Array V2))[0]? = some rowsA from rfl, Option.getD_some,
      rowsMatrix_rowsA, gA_val hM]
  · simp only [baseMats]
    rw [show (#[rowsA, rowsB] : Array (Array V2))[1]? = some rowsB from rfl, Option.getD_some,
      rowsMatrix_rowsB, ite_eq_right one_ne_zero, ite_eq_left trivial, gB_val hM]
  · have : (baseMats)[m]? = none := by
      rw [Array.getElem?_eq_none_iff]; simp only [baseMats, List.size_toArray, List.length_cons,
        List.length_nil]; omega
    rw [this, Option.getD_none, rowsMatrix_idRows, ite_eq_right (by omega), ite_eq_right (by omega),
      Units.val_one]

omit hM in
theorem inv_spec_of {mats invs : Array (Array V2)} {gs : ℕ → GL (Fin 112) (ZMod 2)}
    (hm : ∀ m, rowsMatrix (mats[m]?.getD idRows) = ((gs m : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (hsz : invs.size = mats.size) (h : invsOK mats invs = true)
    (hout : ∀ m, mats.size ≤ m → gs m = 1) (m : ℕ) :
    rowsMatrix (invs[m]?.getD idRows) = (((gs m)⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  by_cases hk : m < mats.size
  · have e := invs_of_invsOK h hk
    rw [hm m] at e
    have e2 : ((gs m : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) *
        (((gs m)⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc rowsMatrix (invs[m]?.getD idRows)
        = (((gs m)⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) *
          ((gs m : GL (Fin 112) (ZMod 2)) * rowsMatrix (invs[m]?.getD idRows)) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]
      _ = (((gs m)⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
          rw [e, Matrix.mul_one]
  · have : invs[m]? = none := by rw [Array.getElem?_eq_none_iff]; omega
    rw [this, Option.getD_none, rowsMatrix_idRows, hout m (by omega), inv_one, Units.val_one]

theorem baseInvs_spec (m : ℕ) : rowsMatrix (baseInvs[m]?.getD idRows) =
    (((baseGL m)⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  inv_spec_of (baseMats_spec hM) (by simp [baseInvs]) hM.baseInv (fun m hm => by
    unfold baseGL; simp only [baseMats, List.size_toArray, List.length_cons, List.length_nil] at hm
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]) m

theorem locMats_spec (k : ℕ) : rowsMatrix ((locMats ())[k]?.getD idRows) =
    ((locGL k : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  unfold locMats locGL
  rw [Array.getElem?_map, List.getElem?_toArray]
  cases localWords[k]? with
  | none => simp [rowsMatrix_idRows, wordProd]
  | some w =>
    rw [Option.map_some, Option.getD_some, Option.getD_some]
    exact rowsMatrix_wordRows (baseMats_spec hM) (baseInvs_spec hM) w

theorem locInvs_spec (k : ℕ) : rowsMatrix ((locInvs ())[k]?.getD idRows) =
    (((locGL k)⁻¹ : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  inv_spec_of (locMats_spec hM) (by simp [locInvs]) hM.locInv (fun m hm => by
    have hsz := hM.locSize
    have : localWords[m]? = none := by
      rw [List.getElem?_eq_none_iff]; simp only [localWords, List.length_cons, List.length_nil]
      omega
    rw [locGL, this, Option.getD_none, wordProd, List.map_nil, List.prod_nil]) k

theorem stabMats_spec (k : ℕ) : rowsMatrix ((stabMats ())[k]?.getD idRows) =
    ((stabGL k : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  unfold stabMats stabGL
  rw [Array.getElem?_map, List.getElem?_toArray]
  cases stabWords[k]? with
  | none => simp [rowsMatrix_idRows, wordProd]
  | some w =>
    rw [Option.map_some, Option.getD_some, Option.getD_some]
    exact rowsMatrix_wordRows (locMats_spec hM) (locInvs_spec hM) w

theorem conjRows_spec : rowsMatrix conjRows =
    ((conjGL : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  rowsMatrix_wordRows (baseMats_spec hM) (baseInvs_spec hM) conjWord

end Mat

end CFSG.Sporadic.J4

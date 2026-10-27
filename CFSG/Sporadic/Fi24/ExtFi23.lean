module

public import CFSG.Sporadic.Fi24.ExtInvolution

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev M : Subgroup J := MulAction.stabilizer J root

theorem card_M :
    Nat.card M = 4089470473293004800 := card_stabilizer_root

theorem mem_M_iff
    (g : J) : g ∈ M ↔ (g : GL (Fin 781) (ZMod 3)) * tT = tT * g :=
  mem_stabilizer_iff_commute g

theorem M_eq_lvl_one : M = lvl 1 := stabilizer_root

noncomputable abbrev mL : Matrix (Fin 253) (Fin 781) (ZMod 3) := mS * (mR * mF)

theorem mL_mul_mRT :
    mL * mRᵀ = 1 := by
  rw [← mS_mul_mK]; simp only [mL, mK, Matrix.mul_assoc]

theorem mat_mul_mRT_of_mem
    {g : J} (hg : g ∈ M) : mat g * mRᵀ = mRᵀ * (mL * mat g * mRᵀ) := by
  have hfix : g • pt 0 = pt 0 := (smul_eq_iff g root root).1 hg
  obtain ⟨X, hX⟩ := exists_mul_eq mR (mat g) (fun j => by
    have := mulVec_mem_of_fix hfix j; rwa [form_zero] at this)
  have hX' : X = mL * mat g * mRᵀ := by
    rw [Matrix.mul_assoc mL (mat g) mRᵀ, hX, ← Matrix.mul_assoc mL mRᵀ X, mL_mul_mRT,
      Matrix.one_mul]
  rw [hX, hX']

@[expose] noncomputable def restrictHom :
    M →* Matrix (Fin 253) (Fin 253) (ZMod 3) where
  toFun g := mL * mat g * mRᵀ
  map_one' := by
    show mL * mat (1 : J) * mRᵀ = 1
    rw [mat_one, Matrix.mul_one, mL_mul_mRT]
  map_mul' g h := by
    show mL * (mat g * mat h) * mRᵀ = mL * mat g * mRᵀ * (mL * mat h * mRᵀ)
    calc mL * (mat g * mat h) * mRᵀ = mL * mat g * (mat h * mRᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = mL * mat g * (mRᵀ * (mL * mat h * mRᵀ)) := by rw [mat_mul_mRT_of_mem h.2]
      _ = mL * mat g * mRᵀ * (mL * mat h * mRᵀ) := by simp only [Matrix.mul_assoc]

theorem restrictHom_apply
    (g : M) : restrictHom g = mL * mat g * mRᵀ := by
  simp only [restrictHom, MonoidHom.coe_mk, OneHom.coe_mk]

structure LocalFacts : Prop where
  size : localWords.size = 2
  letters : localWords.all (·.all fun z => 3 ≤ z.natAbs && z.natAbs ≤ 13) = true
  Q_canon : canonRows 253 (basisRows ()) = true
  Qi_canon : canonRows 253 (invW 253 (basisRows ())) = true
  QQi : eqRows 253 (mulW (basisRows ()) (invW 253 (basisRows ()))) (idW 253) = true
  QiQ : eqRows 253 (mulW (invW 253 (basisRows ())) (basisRows ())) (idW 253) = true
  X0 : eqRows 253 (mulW (restrictW gramInvW (wordW (genLetterW sgW sgiW) localWords[0]!))
    (basisRows ())) (mulW (basisRows ()) (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedA)) = true
  X1 : eqRows 253 (mulW (restrictW gramInvW (wordW (genLetterW sgW sgiW) localWords[1]!))
    (basisRows ())) (mulW (basisRows ()) (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedB)) = true

theorem localFacts : LocalFacts := by
  have h := extFacts.loc
  unfold localChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem localWords_letters {i : ℕ} (hi : i < 2) :
    ∀ z ∈ localWords[i]!, 3 ≤ z.natAbs ∧ z.natAbs ≤ 13 := by
  intro z hz
  have h := localFacts.letters
  rw [Array.all_eq_true] at h
  have hi' : i < localWords.size := by rw [localFacts.size]; exact hi
  have := h i hi'
  rw [getElem!_pos localWords i hi'] at hz
  rw [List.all_eq_true] at this
  have := this z hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem matW_rowsOfSeed_253 (s : String) :
    matW 253 253 (rowsOfSeed 253 s) = Blueprint.NativeSporadic.decode 3 253 1 s := by
  ext i j
  rw [matW_apply, rowW_rowsOfSeed 253 s i.isLt, ofTrits_val (by norm_num), ite_eq_left j.isLt,
    CFSG.F3.Native.decode_apply_eq_decodeEntries, List.getElem?_toArray]

theorem rowsWF_rowsOfSeed_253 (s : String) : RowsWF (rowsOfSeed 253 s) := by
  intro x hx
  unfold rowsOfSeed at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  exact ofTrits_wf (by norm_num) _

theorem rowsOfSeed_253_size (s : String) : (rowsOfSeed 253 s).size = 253 := by
  unfold rowsOfSeed; simp

theorem matW_seedA23 :
    matW 253 253 (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedA) = Fi23.mA := by
  rw [matW_rowsOfSeed_253, CFSG.Sporadic.Fi23.seedA_eq]

theorem matW_seedB23 :
    matW 253 253 (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedB) = Fi23.mB := by
  rw [matW_rowsOfSeed_253, CFSG.Sporadic.Fi23.seedB_eq]

noncomputable abbrev mQ : Matrix (Fin 253) (Fin 253) (ZMod 3) := matW 253 253 (basisRows ())

noncomputable abbrev mQi : Matrix (Fin 253) (Fin 253) (ZMod 3) :=
  matW 253 253 (invW 253 (basisRows ()))

theorem mQ_mul_mQi : mQ * mQi = 1 := by
  have h := congrArg (matW 253 253) (eq_of_eqRows localFacts.QQi).2
  rwa [matW_mulW (m := 253) (by norm_num) (RowsWF.of_canonRows localFacts.Q_canon)
    (RowsWF.of_canonRows localFacts.Qi_canon)
    (by rw [(canonRows_spec localFacts.Qi_canon).1]), matW_idW (by norm_num)] at h

theorem mQi_mul_mQ : mQi * mQ = 1 := by
  have h := congrArg (matW 253 253) (eq_of_eqRows localFacts.QiQ).2
  rwa [matW_mulW (m := 253) (by norm_num) (RowsWF.of_canonRows localFacts.Qi_canon)
    (RowsWF.of_canonRows localFacts.Q_canon)
    (by rw [(canonRows_spec localFacts.Q_canon).1]), matW_idW (by norm_num)] at h

theorem genLetterG_mem
    {z : ℤ} (h3 : 3 ≤ z.natAbs) (h13 : z.natAbs ≤ 13) : genLetterG z ∈ M := by
  have hm : gs (z.natAbs - 1) ∈ M := gs_mem_stabilizer (by omega) (by omega)
  unfold genLetterG
  split_ifs
  · exact hm
  · exact M.inv_mem hm

theorem extWord_mem
    {w : List ℤ} (hw : ∀ z ∈ w, 3 ≤ z.natAbs ∧ z.natAbs ≤ 13) :
    extWord w ∈ M := by
  unfold extWord wordG
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact genLetterG_mem (hw z hz).1 (hw z hz).2

@[expose] noncomputable def mGen0 :
    M :=
  ⟨extWord localWords[0]!, extWord_mem (localWords_letters (by norm_num))⟩

@[expose] noncomputable def mGen1 :
    M :=
  ⟨extWord localWords[1]!, extWord_mem (localWords_letters (by norm_num))⟩

theorem letterOK_localWord
    {i : ℕ} (hi : i < 2) :
    LetterOK (wordW (genLetterW sgW sgiW) localWords[i]!) (mat (extWord localWords[i]!)) :=
  letterOK_extWord fun z hz => (localWords_letters hi z hz).2

theorem matW_restrictW
    {H : Array W} {g : J} (hH : LetterOK H (mat g)) :
    matW 253 253 (restrictW gramInvW H) = mL * mat g * mRᵀ := by
  obtain ⟨hRs, hRw⟩ := rootForm_facts
  have hFw := matrixFacts.F_wf
  have hFs := matrixFacts.F_size
  have hSw := RowsWF.of_canonRows baseFacts.S_canon
  have hRFw : RowsWF (mulW rootForm.rows matF) := RowsWF.mulW hRw hFw
  have hRTw : RowsWF (transposeW 253 781 rootForm.rows) := RowsWF.transposeW (by norm_num) _ _
  unfold restrictW
  rw [matW_mulW (m := 781) (by norm_num) (RowsWF.mulW hSw hRFw) (RowsWF.mulW hH.wf hRTw)
      (by rw [mulW_size, hH.size]),
    matW_mulW (m := 253) (by norm_num) hSw hRFw (by rw [mulW_size, hRs]),
    matW_mulW (m := 781) (by norm_num) hRw hFw (by omega),
    matW_mulW (m := 781) (by norm_num) hH.wf hRTw (by rw [transposeW_size]),
    matW_transposeW (by norm_num) hRw, hH.mat]
  simp only [mL, Matrix.mul_assoc]

theorem restrict_mul_mQ
    {i : ℕ} (hi : i < 2) {Y : Array W} (hYs : Y.size = 253) (hYw : RowsWF Y)
    (h : eqRows 253 (mulW (restrictW gramInvW (wordW (genLetterW sgW sgiW) localWords[i]!))
      (basisRows ())) (mulW (basisRows ()) Y) = true) :
    mL * mat (extWord localWords[i]!) * mRᵀ * mQ = mQ * matW 253 253 Y := by
  have hX := matW_restrictW (letterOK_localWord hi)
  have hXw : RowsWF (restrictW gramInvW (wordW (genLetterW sgW sgiW) localWords[i]!)) :=
    RowsWF.mulW (RowsWF.mulW (RowsWF.of_canonRows baseFacts.S_canon)
      (RowsWF.mulW rootForm_facts.2 matrixFacts.F_wf))
      (RowsWF.mulW (letterOK_localWord hi).wf (RowsWF.transposeW (by norm_num) _ _))
  have e := congrArg (matW 253 253) (eq_of_eqRows h).2
  rw [matW_mulW (m := 253) (by norm_num) hXw (RowsWF.of_canonRows localFacts.Q_canon)
      (by rw [(canonRows_spec localFacts.Q_canon).1]),
    matW_mulW (m := 253) (by norm_num) (RowsWF.of_canonRows localFacts.Q_canon) hYw
      (by rw [hYs]), hX] at e
  exact e

theorem restrictHom_mGen0 :
    restrictHom mGen0 * mQ = mQ * Fi23.mA := by
  rw [restrictHom_apply, ← matW_seedA23]
  exact restrict_mul_mQ (by norm_num) (rowsOfSeed_253_size _) (rowsWF_rowsOfSeed_253 _)
    localFacts.X0

theorem restrictHom_mGen1 :
    restrictHom mGen1 * mQ = mQ * Fi23.mB := by
  rw [restrictHom_apply, ← matW_seedB23]
  exact restrict_mul_mQ (by norm_num) (rowsOfSeed_253_size _) (rowsWF_rowsOfSeed_253 _)
    localFacts.X1

@[expose] noncomputable def fi23MatHom :
    M →* Matrix (Fin 253) (Fin 253) (ZMod 3) where
  toFun g := mQi * restrictHom g * mQ
  map_one' := by
    show mQi * restrictHom 1 * mQ = 1
    rw [map_one, Matrix.mul_one, mQi_mul_mQ]
  map_mul' g h := by
    show mQi * restrictHom (g * h) * mQ = mQi * restrictHom g * mQ * (mQi * restrictHom h * mQ)
    rw [map_mul]
    calc mQi * (restrictHom g * restrictHom h) * mQ =
        mQi * restrictHom g * (mQ * mQi) * restrictHom h * mQ := by
          rw [mQ_mul_mQi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = mQi * restrictHom g * mQ * (mQi * restrictHom h * mQ) := by
          simp only [Matrix.mul_assoc]

theorem fi23MatHom_apply
    (g : M) : fi23MatHom g = mQi * restrictHom g * mQ := by
  simp only [fi23MatHom, MonoidHom.coe_mk, OneHom.coe_mk]

noncomputable abbrev fi23Hom :
    M →* GL (Fin 253) (ZMod 3) := fi23MatHom.toHomUnits

theorem val_fi23Hom (g : M) :
    ((fi23Hom g : GL (Fin 253) (ZMod 3)) : Matrix (Fin 253) (Fin 253) (ZMod 3)) =
      mQi * restrictHom g * mQ := by
  rw [MonoidHom.coe_toHomUnits, fi23MatHom_apply]

theorem fi23Hom_mGen0 :
    fi23Hom mGen0 = Fi23.gA := by
  apply Units.ext
  rw [val_fi23Hom, Matrix.mul_assoc mQi, restrictHom_mGen0, ← Matrix.mul_assoc mQi mQ,
    mQi_mul_mQ, Matrix.one_mul]
  rfl

theorem fi23Hom_mGen1 :
    fi23Hom mGen1 = Fi23.gB := by
  apply Units.ext
  rw [val_fi23Hom, Matrix.mul_assoc mQi, restrictHom_mGen1, ← Matrix.mul_assoc mQi mQ,
    mQi_mul_mQ, Matrix.one_mul]
  rfl

theorem fi23J_le_range :
    Fi23.J ≤ fi23Hom.range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (rfl | rfl)
  · exact ⟨mGen0, fi23Hom_mGen0⟩
  · exact ⟨mGen1, fi23Hom_mGen1⟩

instance :
    Finite M := Nat.finite_of_card_ne_zero (by rw [card_M]; norm_num)

theorem range_fi23Hom :
    fi23Hom.range = Fi23.J := by
  symm
  apply Subgroup.eq_of_le_of_card_ge fi23J_le_range
  rw [Fi23.card_J, ← card_M]
  exact Nat.card_le_card_of_surjective _ fi23Hom.rangeRestrict_surjective

theorem fi23Hom_bijective :
    Function.Bijective fi23Hom.rangeRestrict :=
  fi23Hom.rangeRestrict_surjective.bijective_of_nat_card_le (by
    rw [card_M, range_fi23Hom, Fi23.card_J])

theorem fi23Hom_injective :
    Function.Injective fi23Hom := by
  intro x y h
  apply fi23Hom_bijective.1
  exact Subtype.ext h

@[expose] noncomputable def fi23EquivM :
    M ≃* Fi23.J :=
  (MulEquiv.ofBijective fi23Hom.rangeRestrict fi23Hom_bijective).trans
    (MulEquiv.subgroupCongr range_fi23Hom)

theorem fi23EquivM_mGen0 :
    fi23EquivM mGen0 = Fi23.a := Subtype.ext fi23Hom_mGen0

theorem fi23EquivM_mGen1 :
    fi23EquivM mGen1 = Fi23.b := Subtype.ext fi23Hom_mGen1

theorem closure_mGen :
    Subgroup.closure ({mGen0, mGen1} : Set M) = ⊤ := by
  have key : ∀ y ∈ Subgroup.closure ({Fi23.a, Fi23.b} : Set Fi23.J),
      fi23EquivM.symm y ∈ Subgroup.closure ({mGen0, mGen1} : Set M) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · rw [← fi23EquivM_mGen0, MulEquiv.symm_apply_apply]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [← fi23EquivM_mGen1, MulEquiv.symm_apply_apply]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul y z _ _ hy hz => rw [map_mul]; exact Subgroup.mul_mem _ hy hz
    | inv y _ hy => rw [map_inv]; exact Subgroup.inv_mem _ hy
  rw [eq_top_iff]
  intro x _
  have hx : fi23EquivM x ∈ Subgroup.closure ({Fi23.a, Fi23.b} : Set Fi23.J) := by
    rw [Fi23.closure_ab]; trivial
  have := key _ hx
  rwa [MulEquiv.symm_apply_apply] at this

@[expose] noncomputable def fi23Equiv :
    M ≃* Blueprint.NativeSporadic.Fi23 :=
  fi23EquivM.trans Fi23.fi23EquivJ.symm

theorem isSimpleGroup_M :
    IsSimpleGroup M :=
  @MulEquiv.isSimpleGroup _ _ _ _ Fi23.isSimpleGroup_J fi23EquivM

end CFSG.Sporadic.Fi24

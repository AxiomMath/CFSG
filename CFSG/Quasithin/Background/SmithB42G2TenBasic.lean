module

public import CFSG.Quasithin.Background.SmithB42G2TenSt

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8
open scoped Kronecker

inductive G2L
  | one
  | nat
  | lie
  | st
  deriving DecidableEq

instance : Fintype G2L :=
  ⟨{.one, .nat, .lie, .st}, fun l => by cases l <;> simp⟩

section GramSt

variable {F : Type} [Field F] [CharP F 2]

@[expose] def gramSt (F : Type) [Field F] [CharP F 2] : Matrix SIdx SIdx F :=
  (secSt F)ᵀ * (formQ F ⊗ₖ gramL F) * secSt F

theorem repQL_transpose_form (g : ↥(cayleyGroup F)) :
    (repQL g)ᵀ * (formQ F ⊗ₖ gramL F) * repQL g = formQ F ⊗ₖ gramL F := by
  rw [repQL, kron2Rep_apply, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, repQ_transpose_formQ, repLie_transpose_gramL]

theorem repSt_transpose_gramSt (g : ↥(cayleyGroup F)) :
    (repSt g)ᵀ * gramSt F * repSt g = gramSt F := by
  have h : secSt F * repSt g = repQL g * secSt F := sec_mul_pivotRep isPivot_st g
  calc (repSt g)ᵀ * gramSt F * repSt g
      = (secSt F * repSt g)ᵀ * (formQ F ⊗ₖ gramL F) * (secSt F * repSt g) := by
        rw [gramSt, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = (secSt F)ᵀ * ((repQL g)ᵀ * (formQ F ⊗ₖ gramL F) * repQL g) * secSt F := by
        rw [h, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = gramSt F := by rw [repQL_transpose_form, gramSt]

theorem gramSt_mul_repSt (g : ↥(cayleyGroup F)) :
    gramSt F * repSt g = (repSt g⁻¹)ᵀ * gramSt F :=
  gram_mul_rep repSt (gramSt F) repSt_transpose_gramSt g

abbrev castF (F : Type) [Field F] [CharP F 2] : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

theorem castF_ite (c : Prop) [Decidable c] :
    castF F (if c then 1 else 0) = if c then 1 else 0 := by
  split_ifs <;> simp

theorem secL_map : (secL (ZMod 2)).map (castF F) = secL F := by
  ext q p
  rw [Matrix.map_apply, secL_apply, secL_apply, castF_ite]

theorem formQ_map : (formQ (ZMod 2)).map (castF F) = formQ F := by
  ext i j
  rw [Matrix.map_apply, formQ_apply, formQ_apply, castF_ite]

theorem gramL_map : (gramL (ZMod 2)).map (castF F) = gramL F := by
  ext p p'
  simp only [Matrix.map_apply, gramL, Matrix.of_apply, castF_ite]

theorem ι3f_map (w : Ix3 × LIdx → ZMod 2) (x : Ix3 × (Ix3 × Ix3)) :
    ι3f (fun c => castF F (w c)) x = castF F (ι3f w x) := by
  obtain ⟨a, q⟩ := x
  rw [ι3f_apply, ι3f_apply, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, ← secL_map, Matrix.map_apply]

theorem map_mem_stSub {w : Ix3 × LIdx → ZMod 2} (hw : w ∈ stSub (ZMod 2)) :
    (fun c => castF F (w c)) ∈ stSub F := by
  refine mem_stSub.mpr fun i j k => ?_
  rw [ι3f_map, ι3f_map, ι3f_map, ← map_add, ← map_add, mem_stSub.mp hw, map_zero]

theorem secSt_map : (secSt (ZMod 2)).map (castF F) = secSt F := by
  ext c π
  have hcol : (fun c => castF F ((secSt (ZMod 2)).mulVec (Pi.single π 1) c)) ∈ stSub F :=
    map_mem_stSub (secSt_mulVec_mem _)
  have h := secSt_restrict hcol
  have e : (fun π' : SIdx => castF F ((secSt (ZMod 2)).mulVec (Pi.single π 1) π'.1)) =
      Pi.single π 1 := by
    funext π'
    rw [sec_mulVec_restrict isPivot_st, Pi.single_apply, Pi.single_apply, castF_ite]
  rw [e] at h
  have h2 := congrFun h c
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
  rw [Matrix.map_apply]
  exact h2.symm

theorem gramSt_map : (gramSt (ZMod 2)).map (castF F) = gramSt F := by
  rw [gramSt, gramSt, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, secSt_map,
    Matrix.kroneckerMap_map]
  congr 2
  ext ⟨i, p⟩ ⟨j, p'⟩
  simp only [Matrix.kroneckerMap_apply, map_mul]
  congr 1
  · rw [formQ_apply, formQ_apply, castF_ite]
  · simp only [gramL, Matrix.of_apply, castF_ite]

theorem isUnit_det_gramSt (h : (gramSt (ZMod 2)).det ≠ 0) : IsUnit (gramSt F).det := by
  have h1 : (gramSt (ZMod 2)).det = 1 := by
    generalize (gramSt (ZMod 2)).det = d at h
    fin_cases d
    · exact absurd rfl h
    · rfl
  rw [← gramSt_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h1, map_one]
  exact isUnit_one

end GramSt

namespace G2L

@[expose] def idx : G2L → Type
  | one => Unit
  | nat => Ix3
  | lie => LIdx
  | st => SIdx

instance (l : G2L) : Fintype l.idx := by cases l <;> dsimp only [idx] <;> infer_instance

instance (l : G2L) : DecidableEq l.idx := by cases l <;> dsimp only [idx] <;> infer_instance

variable {F : Type} [Field F] [CharP F 2]

@[expose] def rep : (l : G2L) → ↥(cayleyGroup F) →* Matrix l.idx l.idx F
  | one => 1
  | nat => repQ
  | lie => repLie
  | st => repSt

@[expose] def hw : (l : G2L) → l.idx → F
  | one => fun _ => 1
  | nat => Pi.single (.inl 0) 1
  | lie => Pi.single hwL 1
  | st => Pi.single hwS 1

@[expose] def low : (l : G2L) → l.idx → F
  | one => fun _ => 1
  | nat => Pi.single (.inr 0) 1
  | lie => Pi.single lowL 1
  | st => Pi.single lowS 1

theorem nat_mem : ∀ i : Ix3, (i, lowL) ∉ depList := by decide

theorem lie_mem : ∀ p : LIdx, ((.inr 0 : Ix3), p) ∉ depList := by decide

@[expose] def embNat (i : Ix3) : SIdx := ⟨(i, lowL), nat_mem i⟩

@[expose] def embLie (p : LIdx) : SIdx := ⟨(.inr 0, p), lie_mem p⟩

@[expose] def emb : (l : G2L) → l.idx → SIdx
  | one => fun _ => lowS
  | nat => embNat
  | lie => embLie
  | st => id

theorem emb_injective (l : G2L) : Function.Injective l.emb := by
  cases l
  · intro _ _ _
    rfl
  · intro i j h
    exact congrArg (fun π : SIdx => π.1.1) h
  · intro p q h
    exact congrArg (fun π : SIdx => π.1.2) h
  · exact Function.injective_id

omit [CharP F 2] in
theorem hw_ne_zero (l : G2L) : (l.hw : l.idx → F) ≠ 0 := by
  cases l <;> intro h
  · exact one_ne_zero (congrFun h ())
  · have h1 : (Pi.single (.inl 0) (1 : F) : Ix3 → F) (.inl 0) = 0 := congrFun h (.inl 0)
    simp at h1
  · have h1 : (Pi.single hwL (1 : F) : LIdx → F) hwL = 0 := congrFun h hwL
    simp at h1
  · have h1 : (Pi.single hwS (1 : F) : SIdx → F) hwS = 0 := congrFun h hwS
    simp at h1

theorem rep_U0_hw {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) (l : G2L) :
    (l.rep u).mulVec l.hw = l.hw := by
  cases l
  · change (1 : Matrix Unit Unit F).mulVec (fun _ => 1) = fun _ => 1
    rw [Matrix.one_mulVec]
  · change (repQ u).mulVec (Pi.single (.inl 0) 1) = Pi.single (.inl 0) (1 : F)
    rw [repQ_mulVec, g2Act_U0_single_u0 hu]
  · exact repLie_U0_hw hu
  · exact repSt_U0_hw hu

theorem rep_g2Sw_hw (l : G2L) : (l.rep (g2Sw : ↥(cayleyGroup F))).mulVec l.hw = l.low := by
  cases l
  · change (1 : Matrix Unit Unit F).mulVec (fun _ => 1) = fun _ => 1
    rw [Matrix.one_mulVec]
  · change (repQ g2Sw).mulVec (Pi.single (.inl 0) 1) = Pi.single (.inr 0) (1 : F)
    rw [repQ_mulVec, g2Act_g2Sw]
    funext i
    simp only [Pi.single_apply]
    exact if_congr ⟨fun h => by rw [← Sum.swap_swap i, h]; rfl, fun h => by rw [h]; rfl⟩ rfl rfl
  · exact repLie_g2Sw_hw
  · exact repSt_g2Sw_hw

theorem rep_U0_low {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) (l : G2L) (x : l.idx) :
    (l.rep u).mulVec l.low x = (repSt u).mulVec (Pi.single lowS 1) (l.emb x) := by
  cases l
  · change (1 : Matrix Unit Unit F).mulVec (fun _ => 1) x = (repSt u).mulVec (Pi.single lowS 1) lowS
    rw [repSt_lowS, Matrix.one_mulVec]
    change (1 : F) = repQ u (.inr 0) (.inr 0) * (repLie u).mulVec (Pi.single lowL 1) lowL
    rw [repQ_U0_apply hu (le_refl _), (repLie_U0_low hu).1, ite_eq_left rfl, one_mul]
  · change (repQ u).mulVec (Pi.single (.inr 0) 1) x =
      (repSt u).mulVec (Pi.single lowS 1) (embNat x)
    rw [repSt_lowS]
    change (repQ u).mulVec (Pi.single (.inr 0) 1) x = repQ u x (.inr 0) *
      (repLie u).mulVec (Pi.single lowL 1) lowL
    rw [(repLie_U0_low hu).1, mul_one, Matrix.mulVec_single_one]
    rfl
  · change (repLie u).mulVec (Pi.single lowL 1) x =
      (repSt u).mulVec (Pi.single lowS 1) (embLie x)
    rw [repSt_lowS]
    change (repLie u).mulVec (Pi.single lowL 1) x = repQ u (.inr 0) (.inr 0) *
      (repLie u).mulVec (Pi.single lowL 1) x
    rw [repQ_U0_apply hu (le_refl _), ite_eq_left rfl, one_mul]
  · rfl

@[expose] def gram : (l : G2L) → Matrix l.idx l.idx F
  | one => 1
  | nat => formQ F
  | lie => gramL F
  | st => gramSt F

@[expose] def gramInv : (l : G2L) → Matrix l.idx l.idx F
  | one => 1
  | nat => formQ F
  | lie => gramL F
  | st => (gramSt F)⁻¹

theorem gram_mul_rep (l : G2L) (g : ↥(cayleyGroup F)) :
    l.gram * l.rep g = (l.rep g⁻¹)ᵀ * l.gram := by
  cases l
  · change (1 : Matrix Unit Unit F) * (1 : Matrix Unit Unit F) =
      (1 : Matrix Unit Unit F)ᵀ * (1 : Matrix Unit Unit F)
    rw [Matrix.transpose_one]
  · exact formQ_mul_repQ g
  · exact gramL_mul_repLie g
  · exact gramSt_mul_repSt g

theorem gram_mul_gramInv (h2 : (gramSt (ZMod 2)).det ≠ 0) (l : G2L) :
    l.gram * l.gramInv = (1 : Matrix l.idx l.idx F) := by
  cases l
  · exact Matrix.one_mul _
  · exact formQ_mul_self
  · exact gramL_mul_self
  · exact Matrix.mul_nonsing_inv _ (isUnit_det_gramSt h2)

theorem gramInv_mul_gram (h2 : (gramSt (ZMod 2)).det ≠ 0) (l : G2L) :
    l.gramInv * l.gram = (1 : Matrix l.idx l.idx F) := by
  cases l
  · exact Matrix.one_mul _
  · exact formQ_mul_self
  · exact gramL_mul_self
  · exact Matrix.nonsing_inv_mul _ (isUnit_det_gramSt h2)

end G2L

end CFSG.Quasithin.B42G2Ten

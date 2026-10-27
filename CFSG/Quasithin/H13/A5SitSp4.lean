module

public import CFSG.Quasithin.H13.A5Orth

public section

namespace CFSG.Quasithin.H13.A5.Orth

@[expose] def Bf (v w : V4) : ZMod 2 := v 0 * w 1 + v 1 * w 0 + (v 2 * w 3 + v 3 * w 2)

theorem Bf_eq : ∀ v w : V4, Bf v w = q (v + w) + q v + q w := by
  decide +kernel

abbrev SC :=
  Σ _c0 : V4,
  Σ c1 : {c : V4 // Bf _c0 c = 1},
  Σ c2 : {c : V4 // Bf _c0 c = 0 ∧ Bf c1.1 c = 0},
  {c : V4 // Bf _c0 c = 0 ∧ Bf c1.1 c = 0 ∧ Bf c2.1 c = 1}

@[expose] def SC.cols (x : SC) : Fin 4 → V4 := ![x.1, x.2.1.1, x.2.2.1.1, x.2.2.2.1]

theorem Bf_add_left (x y z : V4) : Bf (x + y) z = Bf x z + Bf y z := by
  simp only [Bf, Pi.add_apply]
  ring

theorem Bf_add_right (x y z : V4) : Bf x (y + z) = Bf x y + Bf x z := by
  simp only [Bf, Pi.add_apply]
  ring

theorem Bf_smul_left (a : ZMod 2) (x z : V4) : Bf (a • x) z = a * Bf x z := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]
  ring

theorem Bf_smul_right (a : ZMod 2) (x z : V4) : Bf x (a • z) = a * Bf x z := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]
  ring

theorem Bf_comm (x y : V4) : Bf x y = Bf y x := by
  simp only [Bf]
  ring

theorem Bf_self : ∀ x : V4, Bf x x = 0 := by
  decide +kernel

theorem Bf_nondeg : ∀ v : V4, (∀ w : V4, Bf v w = 0) → v = 0 := by
  decide +kernel

theorem Bf_app_of6 (c0 c1 c2 c3 : V4) (h01 : Bf c0 c1 = 1) (h02 : Bf c0 c2 = 0)
    (h03 : Bf c0 c3 = 0) (h12 : Bf c1 c2 = 0) (h13 : Bf c1 c3 = 0) (h23 : Bf c2 c3 = 1)
    (v w : V4) : Bf (app ![c0, c1, c2, c3] v) (app ![c0, c1, c2, c3] w) = Bf v w := by
  have h10 : Bf c1 c0 = 1 := (Bf_comm _ _).trans h01
  have h20 : Bf c2 c0 = 0 := (Bf_comm _ _).trans h02
  have h30 : Bf c3 c0 = 0 := (Bf_comm _ _).trans h03
  have h21 : Bf c2 c1 = 0 := (Bf_comm _ _).trans h12
  have h31 : Bf c3 c1 = 0 := (Bf_comm _ _).trans h13
  have h32 : Bf c3 c2 = 1 := (Bf_comm _ _).trans h23
  have e0 : (![c0, c1, c2, c3] : Fin 4 → V4) 0 = c0 := rfl
  have e1 : (![c0, c1, c2, c3] : Fin 4 → V4) 1 = c1 := rfl
  have e2 : (![c0, c1, c2, c3] : Fin 4 → V4) 2 = c2 := rfl
  have e3 : (![c0, c1, c2, c3] : Fin 4 → V4) 3 = c3 := rfl
  simp only [app, e0, e1, e2, e3, Bf_add_left, Bf_add_right, Bf_smul_left, Bf_smul_right, Bf_self,
    h01, h02, h03, h12, h13, h23, h10, h20, h30, h21, h31, h32]
  simp only [Bf]
  ring

theorem SC_props (x : SC) : (∀ v w : V4, Bf (app x.cols v) (app x.cols w) = Bf v w) ∧
    ∀ v : V4, app x.cols v = 0 → v = 0 := by
  obtain ⟨c0, ⟨c1, h01⟩, ⟨c2, h02, h12⟩, ⟨c3, h03, h13, h23⟩⟩ := x
  have hB := Bf_app_of6 c0 c1 c2 c3 h01 h02 h03 h12 h13 h23
  refine ⟨hB, fun v hv => Bf_nondeg v fun w => ?_⟩
  have hv' : app ![c0, c1, c2, c3] v = 0 := hv
  rw [← hB v w, hv']
  simp [Bf]

@[expose] def Spq : Subgroup (MulAut (Multiplicative V4)) where
  carrier := {α | ∀ v w : V4, Bf (Multiplicative.toAdd (α (Multiplicative.ofAdd v)))
    (Multiplicative.toAdd (α (Multiplicative.ofAdd w))) = Bf v w}
  mul_mem' := by
    intro α β hα hβ v w
    simp only [Set.mem_ofPred_eq] at hα hβ ⊢
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have := hα (Multiplicative.toAdd (β (Multiplicative.ofAdd v)))
      (Multiplicative.toAdd (β (Multiplicative.ofAdd w)))
    rw [ofAdd_toAdd, ofAdd_toAdd] at this
    rw [this, hβ]
  one_mem' := by
    intro v w
    simp
  inv_mem' := by
    intro α hα v w
    simp only [Set.mem_ofPred_eq] at hα ⊢
    have := hα (Multiplicative.toAdd (α⁻¹ (Multiplicative.ofAdd v)))
      (Multiplicative.toAdd (α⁻¹ (Multiplicative.ofAdd w)))
    rw [ofAdd_toAdd, ofAdd_toAdd, ← MulAut.mul_apply, ← MulAut.mul_apply, mul_inv_cancel,
      MulAut.one_apply, MulAut.one_apply, toAdd_ofAdd, toAdd_ofAdd] at this
    exact this.symm

@[expose] noncomputable def toSC (α : ↥Spq) : SC :=
  have hB : ∀ v w, Bf (app (colsOf α) v) (app (colsOf α) w) = Bf v w := fun v w => by
    rw [← app_colsOf, ← app_colsOf]
    exact α.2 v w
  have h : ∀ i j, Bf (colsOf α i) (colsOf α j) = Bf (idc i) (idc j) := fun i j => by
    rw [← app_idc (colsOf α) i, ← app_idc (colsOf α) j, hB]
  ⟨colsOf α 0, ⟨colsOf α 1, (h 0 1).trans (by decide)⟩,
    ⟨⟨colsOf α 2, (h 0 2).trans (by decide), (h 1 2).trans (by decide)⟩,
      ⟨colsOf α 3, (h 0 3).trans (by decide), (h 1 3).trans (by decide),
        (h 2 3).trans (by decide)⟩⟩⟩

theorem toSC_cols (α : ↥Spq) : (toSC α).cols = colsOf α := by
  funext j
  fin_cases j <;> rfl

theorem toSC_injective : Function.Injective toSC := by
  intro α β h
  have := congrArg SC.cols h
  rw [toSC_cols, toSC_cols] at this
  exact Subtype.ext (colsOf_injective this)

@[expose] noncomputable def ofSC (x : SC) : MulAut (Multiplicative V4) :=
  let f : Multiplicative V4 →* Multiplicative V4 :=
    { toFun := fun v => Multiplicative.ofAdd (app x.cols (Multiplicative.toAdd v))
      map_one' := by
        show Multiplicative.ofAdd (app x.cols 0) = 1
        rw [app_zero]
        rfl
      map_mul' := fun v w => by
        show Multiplicative.ofAdd (app x.cols (Multiplicative.toAdd v + Multiplicative.toAdd w)) = _
        rw [app_add]
        rfl }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h0 : app x.cols (Multiplicative.toAdd v) = 0 := congrArg Multiplicative.toAdd hv
    have := (SC_props x).2 _ h0
    exact Multiplicative.toAdd.injective (by rw [this]; rfl)
  MulEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)

theorem ofSC_mem (x : SC) : ofSC x ∈ Spq := by
  intro v w
  show Bf (app x.cols (Multiplicative.toAdd (Multiplicative.ofAdd v)))
    (app x.cols (Multiplicative.toAdd (Multiplicative.ofAdd w))) = Bf v w
  exact (SC_props x).1 v w

theorem colsOf_ofSC (x : SC) : colsOf (ofSC x) = x.cols := by
  funext j
  show app x.cols (idc j) = x.cols j
  exact app_idc _ _

theorem toSC_surjective : Function.Surjective toSC := by
  intro x
  refine ⟨⟨ofSC x, ofSC_mem x⟩, ?_⟩
  have hcols : (toSC ⟨ofSC x, ofSC_mem x⟩).cols = x.cols := by
    rw [toSC_cols]
    exact colsOf_ofSC x
  obtain ⟨a0, ⟨a1, ha1⟩, ⟨a2, ha2⟩, ⟨a3, ha3⟩⟩ := x
  generalize hy : toSC ⟨ofSC _, ofSC_mem _⟩ = y at hcols
  obtain ⟨b0, ⟨b1, hb1⟩, ⟨b2, hb2⟩, ⟨b3, hb3⟩⟩ := y
  have e0 : b0 = a0 := congrFun hcols 0
  have e1 : b1 = a1 := congrFun hcols 1
  have e2 : b2 = a2 := congrFun hcols 2
  have e3 : b3 = a3 := congrFun hcols 3
  subst e0 e1 e2 e3
  rfl

@[expose] def Cube (c : Fin 4 → V4) : Prop := comp c (comp c c) = idc

instance : DecidablePred Cube := fun c => inferInstanceAs (Decidable (comp c (comp c c) = idc))

@[expose] def CubeAt (a : OC) : Prop :=
  Cube a.cols → ∀ b : OC, Cube b.cols →
    Cube (comp a.cols b.cols) ∧ comp a.cols b.cols = comp b.cols a.cols

instance (a : OC) : Decidable (CubeAt a) := by unfold CubeAt; infer_instance

theorem cubeAt_all : ∀ a : OC, CubeAt a := by
  decide +kernel

theorem cube_mul (a b : OC) (ha : Cube a.cols) (hb : Cube b.cols) :
    Cube (comp a.cols b.cols) :=
  (cubeAt_all a ha b hb).1

theorem cube_comm (a b : OC) (ha : Cube a.cols) (hb : Cube b.cols) :
    comp a.cols b.cols = comp b.cols a.cols :=
  (cubeAt_all a ha b hb).2

theorem card_cube : Fintype.card {x : OC // Cube x.cols} = 9 := by
  decide +kernel

theorem cube_colsOf_iff (α : MulAut (Multiplicative V4)) : Cube (colsOf α) ↔ α ^ 3 = 1 := by
  unfold Cube
  rw [← colsOf_mul, ← colsOf_mul, ← colsOf_one, colsOf_eq_iff, pow_three]

@[expose] def P3 : Subgroup (MulAut (Multiplicative V4)) where
  carrier := {α | α ∈ Oq ∧ α ^ 3 = 1}
  mul_mem' := by
    rintro α β ⟨hα, hα3⟩ ⟨hβ, hβ3⟩
    refine ⟨Oq.mul_mem hα hβ, ?_⟩
    have h := cube_mul (toOC ⟨α, hα⟩) (toOC ⟨β, hβ⟩)
      (by rw [toOC_mk_cols, cube_colsOf_iff]; exact hα3)
      (by rw [toOC_mk_cols, cube_colsOf_iff]; exact hβ3)
    rwa [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, cube_colsOf_iff] at h
  one_mem' := ⟨Oq.one_mem, one_pow 3⟩
  inv_mem' := by
    rintro α ⟨hα, hα3⟩
    exact ⟨Oq.inv_mem hα, by rw [inv_pow, hα3, inv_one]⟩

theorem P3_comm {α β : MulAut (Multiplicative V4)} (hα : α ∈ P3) (hβ : β ∈ P3) :
    α * β = β * α := by
  have h := cube_comm (toOC ⟨α, hα.1⟩) (toOC ⟨β, hβ.1⟩)
    (by rw [toOC_mk_cols, cube_colsOf_iff]; exact hα.2)
    (by rw [toOC_mk_cols, cube_colsOf_iff]; exact hβ.2)
  rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, ← colsOf_mul, colsOf_eq_iff] at h
  exact h

theorem card_P3 : Nat.card P3 = 9 := by
  have e : ↥P3 ≃ {x : OC // Cube x.cols} :=
    { toFun := fun α => ⟨toOC ⟨α, α.2.1⟩, by rw [toOC_mk_cols, cube_colsOf_iff]; exact α.2.2⟩
      invFun := fun x => ⟨ofOC x.1, ofOC_mem x.1, by
        rw [← cube_colsOf_iff, colsOf_ofOC]; exact x.2⟩
      left_inv := fun α => by
        apply Subtype.ext
        apply colsOf_injective
        show colsOf (ofOC (toOC ⟨α, α.2.1⟩)) = colsOf α
        rw [colsOf_ofOC, toOC_mk_cols]
      right_inv := fun x => by
        apply Subtype.ext
        obtain ⟨y, hy⟩ := toOC_surjective x.1
        show toOC ⟨ofOC x.1, ofOC_mem x.1⟩ = x.1
        rw [← hy]
        congr 1
        apply Subtype.ext
        apply colsOf_injective
        rw [colsOf_ofOC, toOC_cols] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_cube]

@[expose] def r1 : OC :=
  ⟨⟨![0, 1, 0, 0], by decide⟩, ⟨⟨![1, 1, 0, 0], by decide⟩,
    ⟨⟨![0, 0, 1, 0], by decide⟩, ⟨![0, 0, 0, 1], by decide⟩⟩⟩⟩

@[expose] def r2 : OC :=
  ⟨⟨![1, 0, 0, 0], by decide⟩, ⟨⟨![0, 1, 0, 0], by decide⟩,
    ⟨⟨![0, 0, 0, 1], by decide⟩, ⟨![0, 0, 1, 1], by decide⟩⟩⟩⟩

theorem r12_cube : Cube r1.cols ∧ Cube r2.cols := by
  decide +kernel

theorem ofOC_r1_mem : ofOC r1 ∈ P3 :=
  ⟨ofOC_mem r1, by rw [← cube_colsOf_iff, colsOf_ofOC]; exact r12_cube.1⟩

theorem ofOC_r2_mem : ofOC r2 ∈ P3 :=
  ⟨ofOC_mem r2, by rw [← cube_colsOf_iff, colsOf_ofOC]; exact r12_cube.2⟩

@[expose] def NormPC (g : Fin 4 → V4) : Prop :=
  (∀ w : V4, q (app g (app r1.cols w)) = q (app g w)) →
    (∀ w : V4, q (app g (app r2.cols w)) = q (app g w)) → ∀ v : V4, q (app g v) = q v

instance (g : Fin 4 → V4) : Decidable (NormPC g) := by unfold NormPC; infer_instance

@[expose] def NormPC3 (c0 c1 c2 : V4) : Prop :=
  ∀ c3 : V4, Bf c0 c3 = 0 → Bf c1 c3 = 0 → Bf c2 c3 = 1 → NormPC ![c0, c1, c2, c3]

instance (c0 c1 c2 : V4) : Decidable (NormPC3 c0 c1 c2) := by unfold NormPC3; infer_instance

@[expose] def NormPC2 (c0 c1 : V4) : Prop :=
  ∀ c2 : V4, Bf c0 c2 = 0 → Bf c1 c2 = 0 → NormPC3 c0 c1 c2

instance (c0 c1 : V4) : Decidable (NormPC2 c0 c1) := by unfold NormPC2; infer_instance

@[expose] def NormPC1 (c0 : V4) : Prop := ∀ c1 : V4, Bf c0 c1 = 1 → NormPC2 c0 c1

instance (c0 : V4) : Decidable (NormPC1 c0) := by unfold NormPC1; infer_instance

theorem mem_Oq_of_conj_of (hcert : ∀ c0 : V4, NormPC1 c0) {g : MulAut (Multiplicative V4)}
    (hg : g ∈ Spq) (h1 : g * ofOC r1 * g⁻¹ ∈ Oq) (h2 : g * ofOC r2 * g⁻¹ ∈ Oq) : g ∈ Oq := by
  have key : ∀ (r : OC), g * ofOC r * g⁻¹ ∈ Oq →
      ∀ w : V4, q (app (colsOf g) (app r.cols w)) = q (app (colsOf g) w) := by
    intro r hr w
    have h := hr (Multiplicative.toAdd (g (Multiplicative.ofAdd w)))
    rw [ofAdd_toAdd, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
      app_colsOf] at h
    have e : Multiplicative.toAdd (g (ofOC r (Multiplicative.ofAdd w))) =
        app (colsOf g) (app r.cols w) := by
      rw [← ofAdd_toAdd (ofOC r (Multiplicative.ofAdd w)), app_colsOf, app_colsOf, colsOf_ofOC]
    rw [e] at h
    exact h
  have hc : ∀ i j, Bf (colsOf g i) (colsOf g j) = Bf (idc i) (idc j) := fun i j => by
    rw [← app_idc (colsOf g) i, ← app_idc (colsOf g) j, ← app_colsOf, ← app_colsOf]
    exact hg _ _
  have hcols : colsOf g = ![colsOf g 0, colsOf g 1, colsOf g 2, colsOf g 3] := by
    funext j
    fin_cases j <;> rfl
  have hN : NormPC (colsOf g) := by
    rw [hcols]
    exact hcert _ _ ((hc 0 1).trans (by decide)) _ ((hc 0 2).trans (by decide))
      ((hc 1 2).trans (by decide)) _ ((hc 0 3).trans (by decide)) ((hc 1 3).trans (by decide))
      ((hc 2 3).trans (by decide))
  intro v
  rw [app_colsOf]
  exact hN (key r1 h1) (key r2 h2) v

end CFSG.Quasithin.H13.A5.Orth

module

public import CFSG.Quasithin.H13.U3SixCodes
public import CFSG.Quasithin.H13.U3U33Fixed

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

section Stab

variable {X Y : Type*} [Group X]

@[expose] def stabP (π : X →* Equiv.Perm Y) (y : Y) : Subgroup X where
  carrier := {g | π g y = y}
  one_mem' := by simp
  mul_mem' := fun {g h} hg hh => by
    simp only [Set.mem_ofPred_eq, map_mul, Equiv.Perm.mul_apply] at hg hh ⊢
    rw [hh, hg]
  inv_mem' := fun {g} hg => by
    simp only [Set.mem_ofPred_eq, map_inv] at hg ⊢
    rw [Equiv.Perm.inv_eq_iff_eq, hg]

theorem mem_stabP {π : X →* Equiv.Perm Y} {y : Y} {g : X} : g ∈ stabP π y ↔ π g y = y :=
  Iff.rfl

theorem closure_le_stabP {π : X →* Equiv.Perm Y} {y : Y} {S : Set X} (h : ∀ g ∈ S, π g y = y) :
    Subgroup.closure S ≤ stabP π y :=
  (Subgroup.closure_le _).2 h

end Stab

@[expose] def u6c (i : Fin 5) : List ℕ :=
  [[33, 5, 49, 26, 23, 61], [48, 46, 35, 50, 51, 26], [13, 14, 50, 62, 38, 44],
    [34, 14, 50, 17, 59, 3], [5, 34, 1, 19, 60, 2]].getD i []

@[expose] def u6ci (i : Fin 5) : List ℕ :=
  [[60, 23, 62, 26, 5, 61], [24, 9, 35, 61, 20, 21], [13, 14, 50, 62, 38, 44],
    [13, 45, 54, 25, 5, 44], [4, 32, 5, 27, 44, 34]].getD i []

theorem u6c_mul_inv : ∀ i : Fin 5, mul6 (u6c i) (u6ci i) = id6 ∧ mul6 (u6ci i) (u6c i) = id6 := by
  decide +kernel

theorem u6c_relators : ∀ w ∈ u33PresRels,
    (w.map fun l => cond l.2 (u6c l.1) (u6ci l.1)).foldr mul6 id6 = id6 := by
  decide +kernel

@[expose] def u6GL (i : Fin 5) : GL (Fin 6) (ZMod 2) :=
  ⟨colMat (u6c i), colMat (u6ci i), by rw [← colMat_mul6, (u6c_mul_inv i).1, colMat_id6],
    by rw [← colMat_mul6, (u6c_mul_inv i).2, colMat_id6]⟩

theorem coe_prod_u6GL (w : List (Fin 5 × Bool)) :
    (((w.map fun l => cond l.2 (u6GL l.1) (u6GL l.1)⁻¹).prod : GL (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      colMat ((w.map fun l => cond l.2 (u6c l.1) (u6ci l.1)).foldr mul6 id6) := by
  induction w with
  | nil => simp [colMat_id6]
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, List.map_cons, List.foldr_cons,
      colMat_mul6]
    congr 1
    cases l.2 <;> rfl

@[expose] noncomputable def rho6 : U33G →* GL (Fin 6) (ZMod 2) :=
  PresentedGroup.toGroup (f := u6GL) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    apply Units.ext
    rw [coe_prod_u6GL, Units.val_one, u6c_relators w hw, colMat_id6])

theorem rho6_of (i : Fin 5) : rho6 (PresentedGroup.of i) = u6GL i := by
  rw [rho6, PresentedGroup.toGroup.of]

theorem rho6_gen (i : Fin 5) : rho6 (u33GenPG i) = u6GL i := by
  simp only [u33GenPG, Fin.is_lt, ↓reduceDIte, Fin.eta, rho6_of]

theorem rho6_gen' (i : ℕ) (hi : i < 5) : rho6 (u33GenPG i) = u6GL ⟨i, hi⟩ :=
  rho6_gen ⟨i, hi⟩

theorem rho6_abs
    : rho6 u33Data.a = u6GL 0 ∧ rho6 u33Data.b = u6GL 1 ∧
    rho6 u33Data.s = u6GL 2 ∧ rho6 u33Data.x = u6GL 3 ∧ rho6 u33Data.y = u6GL 4 :=
  ⟨rho6_gen 0, rho6_gen 1, rho6_gen 2, rho6_gen 3, rho6_gen 4⟩

theorem rho6_injective
    : Function.Injective rho6 := by
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal rho6.ker with h | h
  · exact h
  · exfalso
    have h1 : rho6 (u33GenPG 0) = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top _)
    rw [rho6_gen' 0 (by norm_num)] at h1
    have h2 : colMat (u6c ⟨0, by norm_num⟩) = 1 := congrArg Units.val h1
    exact absurd h2 (by decide +kernel)

abbrev W6 : Type := Fin 6 → ZMod 2

@[expose] noncomputable def glLin : GL (Fin 6) (ZMod 2) ≃* (W6 ≃ₗ[ZMod 2] W6) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glLin_apply (g : GL (Fin 6) (ZMod 2)) (w : W6) :
    glLin g w = (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w :=
  rfl

@[expose] def linToMulAut : (W6 ≃ₗ[ZMod 2] W6) →* MulAut (Multiplicative W6) where
  toFun e := AddEquiv.toMultiplicative e.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def psiW : U33G →* MulAut (Multiplicative W6) :=
  linToMulAut.comp (glLin.toMonoidHom.comp rho6)

theorem psiW_apply (g : U33G) (w : W6) :
    psiW g (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd ((rho6 g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w) :=
  rfl

theorem psiW_gen_vecOf (i : Fin 5) (v : ℕ) :
    psiW (u33GenPG i) (Multiplicative.ofAdd (vecOf v)) =
      Multiplicative.ofAdd (vecOf (vapp (u6c i) v)) := by
  rw [psiW_apply, rho6_gen]
  exact congrArg Multiplicative.ofAdd (colMat_mulVec_vecOf _ _)

theorem psiW_gen_vecOf' (i : ℕ) (hi : i < 5) (v : ℕ) :
    psiW (u33GenPG i) (Multiplicative.ofAdd (vecOf v)) =
      Multiplicative.ofAdd (vecOf (vapp (u6c ⟨i, hi⟩) v)) :=
  psiW_gen_vecOf ⟨i, hi⟩ v

theorem card_W6 : Nat.card (Multiplicative W6) = 64 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem W6_mul_self (v : Multiplicative W6) : v * v = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize Multiplicative.toAdd v i = c
  revert c
  decide

theorem vapp_lt_of_foldr {m : List ℕ} (c : ℕ) :
    ∀ l : List ℕ, (∀ j ∈ l, m.getD j 0 < 2 ^ 6) →
      l.foldr (fun j acc => if c.testBit j then m.getD j 0 ^^^ acc else acc) 0 < 2 ^ 6 := by
  intro l
  induction l with
  | nil => intro _; norm_num
  | cons j l ih =>
    intro h
    rw [List.foldr_cons]
    have ih' := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    split_ifs
    · exact Nat.xor_lt_two_pow (h j (List.mem_cons_self ..)) ih'
    · exact ih'

theorem u6c_getD_lt : ∀ i : Fin 5, ∀ j < 6, (u6c i).getD j 0 < 2 ^ 6 := by
  decide +kernel

theorem vapp_u6c_lt (i : Fin 5) (c : ℕ) : vapp (u6c i) c < 64 :=
  vapp_lt_of_foldr c _ fun j hj => u6c_getD_lt i j (List.mem_range.1 hj)

theorem u6c_no_fixed : ∀ v < 64, v ≠ 0 → ∃ i : Fin 5, vapp (u6c i) v ≠ v := by
  decide +kernel

theorem psiW_fix : ∀ v : Multiplicative W6, (∀ g, psiW g v = v) → v = 1 := by
  intro v hv
  obtain ⟨c, hc, hcv⟩ := exists_vecOf (Multiplicative.toAdd v)
  have hv' : v = Multiplicative.ofAdd (vecOf c) := by rw [hcv]; rfl
  subst hv'
  by_contra hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [vecOf_zero]; rfl)
  obtain ⟨i, hi⟩ := u6c_no_fixed c hc hc0
  have h := hv (u33GenPG i)
  rw [psiW_gen_vecOf] at h
  have h2 : vecOf (vapp (u6c i) c) = vecOf c := congrArg Multiplicative.toAdd h
  exact hi (vecOf_injective (vapp_u6c_lt i c) hc h2)

@[expose] def w0 : Multiplicative W6 := Multiplicative.ofAdd (vecOf 15)

theorem w0_ne_one : w0 ≠ 1 := by
  intro h
  have h2 : vecOf 15 = vecOf 0 := by
    rw [vecOf_zero]
    exact congrArg Multiplicative.toAdd h
  exact absurd (vecOf_injective (by norm_num) (by norm_num) h2) (by norm_num)

theorem u6c_w0 : ∀ i : Fin 5, i ≠ 4 → vapp (u6c i) 15 = 15 := by
  decide +kernel

theorem u6c_y_w0 : vapp (u6c 4) 15 ≠ 15 := by
  decide +kernel

theorem psiW_gen_w0 (i : Fin 5) (hi : i ≠ 4) : psiW (u33GenPG i) w0 = w0 := by
  rw [w0, psiW_gen_vecOf, u6c_w0 i hi]

theorem psiW_y_w0 : psiW (u33GenPG 4) w0 ≠ w0 := by
  rw [w0, psiW_gen_vecOf' 4 (by norm_num)]
  intro h
  have h2 : vecOf (vapp (u6c 4) 15) = vecOf 15 := congrArg Multiplicative.toAdd h
  exact u6c_y_w0 (vecOf_injective (vapp_u6c_lt 4 15) (by norm_num) h2)

@[expose] noncomputable def permW : U33G →* Equiv.Perm (Multiplicative W6) :=
  (MulAut.toPerm _).comp psiW

theorem permW_apply (g : U33G) (v : Multiplicative W6) : permW g v = psiW g v :=
  rfl

theorem A_le_stab_w0
    : u33Data.A ≤ stabP permW w0 := by
  refine closure_le_stabP fun g hg => ?_
  rcases hg with rfl | rfl | rfl | rfl
  · exact psiW_gen_w0 0 (by decide)
  · exact psiW_gen_w0 1 (by decide)
  · exact psiW_gen_w0 2 (by decide)
  · exact psiW_gen_w0 3 (by decide)

theorem psiW_stab_w0
    : (∀ g, psiW g w0 = w0 ↔ g ∈ u33Data.A) ∧
    ∀ w : Multiplicative W6, w ≠ 1 → ∃ g, psiW g w0 = w := by
  have hT : ∀ t ∈ u33Data.T, psiW t w0 = w0 := fun t ht =>
    A_le_stab_w0 (u33Data.T_le_A ht)
  obtain ⟨hst, horb⟩ := u33_stab_orbit card_W6 psiW psiW_fix w0_ne_one hT
  refine ⟨?_, horb⟩
  rcases hst with h | h
  · exact h
  · exfalso
    exact psiW_y_w0 ((h _).2 u33Data.y_mem_B)

theorem psiW_transitive
    (w : Multiplicative W6) (hw : w ≠ 1) : ∃ g, psiW g w0 = w :=
  psiW_stab_w0.2 w hw

@[expose] def p63 (i : Fin 5) : List ℕ :=
  [[0, 1, 2, 4, 6, 3, 5, 8, 11, 9, 7, 10, 12, 14, 21, 15, 16, 20, 26, 27, 28, 29, 30, 31, 25,
      23, 22, 41, 34, 13, 18, 24, 44, 45, 17, 38, 35, 46, 42, 47, 48, 49, 36, 32, 52, 55, 59, 40,
      39, 19, 60, 61, 43, 33, 37, 53, 50, 62, 56, 54, 58, 57, 51],
    [0, 1, 2, 5, 3, 6, 4, 7, 8, 15, 10, 11, 16, 17, 20, 12, 9, 24, 14, 32, 25, 28, 29, 26, 30,
      18, 21, 44, 23, 34, 13, 22, 40, 50, 31, 49, 41, 51, 19, 36, 38, 52, 27, 47, 48, 60, 61, 35,
      42, 43, 46, 53, 39, 56, 62, 58, 37, 45, 54, 57, 59, 33, 55],
    [0, 2, 1, 6, 4, 5, 3, 9, 15, 7, 16, 12, 11, 18, 14, 8, 10, 26, 13, 33, 21, 20, 24, 34, 22,
      29, 17, 50, 28, 25, 30, 31, 45, 19, 23, 51, 37, 36, 53, 54, 55, 46, 56, 57, 60, 32, 41, 62,
      58, 61, 27, 35, 59, 38, 39, 40, 42, 43, 48, 52, 44, 49, 47],
    [1, 2, 0, 7, 10, 8, 11, 12, 15, 6, 16, 9, 3, 19, 35, 5, 4, 27, 36, 37, 38, 39, 32, 40, 41,
      42, 48, 58, 47, 44, 49, 43, 46, 18, 52, 51, 33, 13, 54, 53, 59, 45, 60, 57, 56, 24, 22, 62,
      50, 61, 26, 14, 55, 21, 20, 34, 29, 31, 17, 23, 25, 30, 28],
    [0, 3, 6, 5, 2, 1, 4, 13, 20, 21, 22, 23, 24, 25, 15, 34, 18, 10, 31, 43, 26, 30, 17, 29, 28,
      7, 8, 27, 12, 11, 9, 16, 58, 44, 14, 41, 61, 62, 38, 42, 33, 54, 60, 51, 40, 50, 46, 47, 37,
      45, 49, 19, 52, 36, 35, 55, 56, 57, 59, 32, 39, 53, 48]].getD i []

@[expose] def p63i (i : Fin 5) : List ℕ :=
  [[0, 1, 2, 5, 3, 6, 4, 10, 7, 9, 11, 8, 12, 29, 13, 15, 16, 34, 30, 49, 17, 14, 26, 25, 31,
      24, 18, 19, 20, 21, 22, 23, 43, 53, 28, 36, 42, 54, 35, 48, 47, 27, 38, 52, 32, 33, 37, 39,
      40, 41, 56, 62, 44, 55, 59, 45, 58, 61, 60, 46, 50, 51, 57],
    [0, 1, 2, 4, 6, 3, 5, 7, 8, 16, 10, 11, 15, 30, 18, 9, 12, 13, 25, 38, 14, 26, 31, 28, 17,
      20, 23, 42, 21, 22, 24, 34, 19, 61, 29, 47, 39, 56, 40, 52, 32, 36, 48, 49, 27, 57, 50, 43,
      44, 35, 33, 37, 41, 51, 58, 62, 53, 59, 55, 60, 45, 46, 54],
    [0, 2, 1, 6, 4, 5, 3, 9, 15, 7, 16, 12, 11, 18, 14, 8, 10, 26, 13, 33, 21, 20, 24, 34, 22,
      29, 17, 50, 28, 25, 30, 31, 45, 19, 23, 51, 37, 36, 53, 54, 55, 46, 56, 57, 60, 32, 41, 62,
      58, 61, 27, 35, 59, 38, 39, 40, 42, 43, 48, 52, 44, 49, 47],
    [2, 0, 1, 12, 16, 15, 9, 3, 5, 11, 4, 6, 7, 37, 51, 8, 10, 58, 33, 13, 54, 53, 46, 59, 45, 60,
      50, 17, 62, 56, 61, 57, 22, 36, 55, 14, 18, 19, 20, 21, 23, 24, 25, 31, 29, 41, 32, 28, 26,
      30, 48, 35, 34, 39, 38, 52, 44, 43, 27, 40, 42, 49, 47],
    [0, 5, 4, 1, 6, 3, 2, 25, 26, 30, 17, 29, 28, 7, 34, 14, 31, 22, 16, 51, 8, 9, 10, 11, 12, 13,
      20, 27, 24, 23, 21, 18, 59, 40, 15, 54, 53, 48, 38, 60, 44, 35, 39, 19, 33, 49, 46, 47, 62,
      50, 45, 43, 52, 61, 41, 55, 56, 57, 32, 58, 42, 36, 37]].getD i []

theorem p63_spec : ∀ i : Fin 5, (p63 i).length = 63 ∧ (p63i i).length = 63 ∧
    ∀ k : Fin 63, (p63 i).getD k 0 < 63 ∧ (p63i i).getD k 0 < 63 ∧
      (p63i i).getD ((p63 i).getD k 0) 0 = k ∧ (p63 i).getD ((p63i i).getD k 0) 0 = k := by
  decide +kernel

@[expose] def perm63 (i : Fin 5) : Equiv.Perm (Fin 63) where
  toFun k := ⟨(p63 i).getD k 0, ((p63_spec i).2.2 k).1⟩
  invFun k := ⟨(p63i i).getD k 0, ((p63_spec i).2.2 k).2.1⟩
  left_inv k := Fin.ext ((p63_spec i).2.2 k).2.2.1
  right_inv k := Fin.ext ((p63_spec i).2.2 k).2.2.2

theorem repL_perm63 (i : Fin 5) : RepL (p63 i) (perm63 i) :=
  ⟨(p63_spec i).1, fun _ => rfl⟩

theorem repL_perm63_inv (i : Fin 5) : RepL (p63i i) (perm63 i)⁻¹ :=
  ⟨(p63_spec i).2.1, fun _ => rfl⟩

theorem p63_relators : ∀ w ∈ u33PresRels,
    (w.map fun l => cond l.2 (p63 l.1) (p63i l.1)).foldr compL (List.range 63) =
      List.range 63 := by
  decide +kernel

theorem repL_prod_perm63 (w : List (Fin 5 × Bool)) :
    RepL ((w.map fun l => cond l.2 (p63 l.1) (p63i l.1)).foldr compL (List.range 63))
      (w.map fun l => cond l.2 (perm63 l.1) (perm63 l.1)⁻¹).prod := by
  induction w with
  | nil => exact repL_one 63
  | cons l w ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons]
    refine repL_mul ?_ ih
    cases l.2
    · exact repL_perm63_inv l.1
    · exact repL_perm63 l.1

@[expose] noncomputable def pi63 : U33G →* Equiv.Perm (Fin 63) :=
  PresentedGroup.toGroup (f := perm63) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    have h := repL_prod_perm63 w
    rw [p63_relators w hw] at h
    exact eq_of_repL h (repL_one 63))

theorem pi63_gen (i : Fin 5) : pi63 (u33GenPG i) = perm63 i := by
  simp only [u33GenPG, Fin.is_lt, ↓reduceDIte, Fin.eta, pi63, PresentedGroup.toGroup.of]

theorem pi63_gen' (i : ℕ) (hi : i < 5) : pi63 (u33GenPG i) = perm63 ⟨i, hi⟩ :=
  pi63_gen ⟨i, hi⟩

theorem p63_zero : ∀ i : Fin 5, i ≠ 3 → (p63 i).getD 0 0 = 0 := by
  decide +kernel

theorem p63_x_zero : (p63 3).getD 0 0 ≠ 0 := by
  decide +kernel

theorem pi63_gen_zero (i : Fin 5) (hi : i ≠ 3) : pi63 (u33GenPG i) 0 = 0 := by
  rw [pi63_gen]
  exact Fin.ext (p63_zero i hi)

theorem pi63_x_zero : pi63 (u33GenPG 3) 0 ≠ 0 := by
  rw [pi63_gen' 3 (by norm_num)]
  intro h
  exact p63_x_zero (congrArg Fin.val h)

theorem pi63_stab_zero
    : ∀ g, pi63 g 0 = 0 ↔ g ∈ u33Data.B := by
  have hB : u33Data.B ≤ stabP pi63 0 := by
    refine closure_le_stabP fun g hg => ?_
    rcases hg with rfl | rfl | rfl | rfl
    · exact pi63_gen_zero 0 (by decide)
    · exact pi63_gen_zero 1 (by decide)
    · exact pi63_gen_zero 2 (by decide)
    · exact pi63_gen_zero 4 (by decide)
  have hT : u33Data.T ≤ stabP pi63 0 := u33Data.T_le_B.trans hB
  have hx : u33Data.x ∉ stabP pi63 0 := pi63_x_zero
  have heq : stabP pi63 0 = u33Data.B := by
    rcases u33Data.lattice _ hT with h | h | h | h
    · exfalso
      have hle : u33Data.B ≤ u33Data.T := h ▸ hB
      have h1 := Subgroup.card_le_of_le hle
      rw [card_u33_B, u33_card_T] at h1
      norm_num at h1
    · exact absurd (h ▸ u33Data.x_mem_A) hx
    · exact h
    · exact absurd (h ▸ Subgroup.mem_top _) hx
  intro g
  rw [← heq]
  exact Iff.rfl

theorem pi63_transitive
    (k : Fin 63) : ∃ g, pi63 g 0 = k := by
  classical
  let _ : MulAction U33G (Fin 63) := MulAction.compHom (Fin 63) pi63
  have hidx := MulAction.index_stabilizer U33G (0 : Fin 63)
  have hst : MulAction.stabilizer U33G (0 : Fin 63) = u33Data.B := by
    ext g
    exact pi63_stab_zero g
  rw [hst, index_u33_B] at hidx
  have horb : MulAction.orbit U33G (0 : Fin 63) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, Nat.card_fin, ← hidx]
  have hk : k ∈ MulAction.orbit U33G (0 : Fin 63) := by rw [horb]; exact Set.mem_univ k
  obtain ⟨g, hg⟩ := hk
  exact ⟨g, hg⟩

theorem card_fix_pi63_y : Nat.card {k : Fin 63 // pi63 (u33GenPG 4) k = k} = 9 := by
  rw [pi63_gen' 4 (by norm_num), Nat.card_eq_fintype_card]
  decide +kernel

end CFSG.Quasithin.H13.U3

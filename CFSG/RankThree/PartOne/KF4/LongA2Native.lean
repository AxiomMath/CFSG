module

public import CFSG.RankThree.PartOne.KF4.LongA2Data
public import CFSG.RankThree.PartOne.KF4.Torus2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped Pointwise

section Mats

variable {K : Type} [Field K]

theorem f4Long_Mat_x1 (t : K) :
    f4Long_data.Mat (xUnit Tag.F4 K (f4Index 0) t) = 1 + single 0 1 t :=
  f4Long_data.Mat_xUnit_single ((mem_f4LongSupport _).2 (Or.inl rfl)) f4Long_steps.1 t

theorem f4Long_Mat_y1 (t : K) :
    f4Long_data.Mat (yUnit Tag.F4 K (f4Index 0) t) = 1 + single 1 0 t :=
  f4Long_data.Mat_yUnit_single ((mem_f4LongSupport _).2 (Or.inl rfl)) f4Long_steps.2.1 t

theorem f4Long_Mat_x2 (t : K) :
    f4Long_data.Mat (xUnit Tag.F4 K (f4Index 1) t) = 1 + single 1 2 t :=
  f4Long_data.Mat_xUnit_single ((mem_f4LongSupport _).2 (Or.inr rfl)) f4Long_steps.2.2.1 t

theorem f4Long_Mat_y2 (t : K) :
    f4Long_data.Mat (yUnit Tag.F4 K (f4Index 1) t) = 1 + single 2 1 t :=
  f4Long_data.Mat_yUnit_single ((mem_f4LongSupport _).2 (Or.inr rfl)) f4Long_steps.2.2.2 t

theorem torusElt_mem_f4Long {i : Fin Tag.F4.rank} (hi : i ∈ f4LongSupport) (a : Kˣ) :
    torusElt Tag.F4 K i a ∈ subsystemGroup Tag.F4 K f4LongSupport :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hi a)

theorem torus2Elt_mem_f4Long (a b : Kˣ) :
    torus2Elt (f4Index 0) (f4Index 1) a b ∈ subsystemGroup Tag.F4 K f4LongSupport :=
  mul_mem (torusElt_mem_f4Long ((mem_f4LongSupport _).2 (Or.inl rfl)) a)
    (torusElt_mem_f4Long ((mem_f4LongSupport _).2 (Or.inr rfl)) b)

theorem f4Long_Mat_torus (a b : Kˣ) :
    f4Long_data.Mat (torus2Elt (f4Index 0) (f4Index 1) a b) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  rw [torus2Elt,
    f4Long_data.Mat_mul (torusElt_mem_f4Long ((mem_f4LongSupport _).2 (Or.inl rfl)) a)
      (torusElt_mem_f4Long ((mem_f4LongSupport _).2 (Or.inr rfl)) b),
    f4Long_data.Mat_torusElt, f4Long_data.Mat_torusElt, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  obtain ⟨h0, h2⟩ := f4Long_pairing k
  rw [h0, h2]
  fin_cases k <;> simp [Units.val_mul, _root_.zpow_neg]

theorem det_f4Long_Mat {g : ModGL Tag.F4 K} (hg : g ∈ subsystemGroup Tag.F4 K f4LongSupport) :
    (f4Long_data.Mat g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_f4LongSupport i).1 hi with rfl | rfl
      · rw [f4Long_Mat_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [f4Long_Mat_x2]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_f4LongSupport i).1 hi with rfl | rfl
      · rw [f4Long_Mat_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [f4Long_Mat_y2]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [f4Long_data.Mat_one, det_one]
  | mul x y hx hy ihx ihy => rw [f4Long_data.Mat_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := f4Long_data.Mat_mul (inv_mem hx) hx
    rw [inv_mul_cancel, f4Long_data.Mat_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def f4LongRep :
    subsystemGroup Tag.F4 K f4LongSupport →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨f4Long_data.Mat (g : ModGL Tag.F4 K), det_f4Long_Mat g.2⟩
  map_one' := Subtype.ext f4Long_data.Mat_one
  map_mul' g h := Subtype.ext (f4Long_data.Mat_mul g.2 h.2)

theorem coe_f4LongRep (g : subsystemGroup Tag.F4 K f4LongSupport) :
    ((f4LongRep K g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      f4Long_data.Mat (g : ModGL Tag.F4 K) :=
  rfl

end Mats

section Families

variable
  {K : Type} [Field K]

theorem f4chainLong_mem_parabolicRoots {k l : Fin 3} (hkl : k ≠ l) :
    chainRoot f4chainLong k l ∈ parabolicRoots Tag.F4 f4LongSupport := by
  obtain ⟨m, hm, hs⟩ := f4chainLong_mem k l hkl
  rw [← hm]
  exact ⟨isRoot_f4RootVec m, fun i hi => hs i ((mem_f4LongSupport i).not.1 hi)⟩

theorem exists_f4chainLong_of_mem {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4LongSupport) :
    ∃ k l : Fin 3, k ≠ l ∧ chainRoot f4chainLong k l = α := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hα.1
  exact exists_f4chainLong_of_support m fun i hi => hα.2 i ((mem_f4LongSupport i).not.2 hi)

theorem pinnedX_mem_f4Long {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4LongSupport) (t : K) :
    pinnedX Tag.F4 K α t ∈ subsystemGroup Tag.F4 K f4LongSupport :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

variable (K) in
@[expose] def F4LongRootFamily (i j : Fin 3) : Prop :=
  ∃ ε : Kˣ, ∀ t : K, f4Long_data.Mat (pinnedX Tag.F4 K (chainRoot f4chainLong i j) t) =
    1 + single i j ((ε : K) * t)

@[expose] def f4LongN : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 0; 0, 0, 1]

@[expose] def f4LongNinv : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; 1, 0, 0; 0, 0, 1]

theorem f4LongN_mul_Ninv : (f4LongN : Matrix (Fin 3) (Fin 3) K) * f4LongNinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f4LongN, f4LongNinv, Matrix.mul_apply, Fin.sum_univ_three]

theorem f4LongN_conj_12 (c : K) :
    (f4LongN : Matrix (Fin 3) (Fin 3) K) * (1 + single 1 2 c) * f4LongNinv = 1 + single 0 2 c := by
  rw [Matrix.mul_assoc]
  ext a b
  simp only [f4LongN, f4LongNinv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem f4LongN_conj_21 (c : K) :
    (f4LongN : Matrix (Fin 3) (Fin 3) K) * (1 + single 2 1 c) * f4LongNinv = 1 + single 2 0 c := by
  rw [Matrix.mul_assoc]
  ext a b
  simp only [f4LongN, f4LongNinv, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem f4Long_Mat_n1 :
    f4Long_data.Mat (weylElt Tag.F4 K (f4Index 0) 1) = f4LongN := by
  have h1 : weylElt Tag.F4 K (f4Index 0) 1 =
      xUnit Tag.F4 K (f4Index 0) 1 * yUnit Tag.F4 K (f4Index 0) (-1) *
        xUnit Tag.F4 K (f4Index 0) 1 := by
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    simp
  have hx := xUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4LongSupport _).2
    (Or.inl rfl)) 1
  have hy := yUnit_mem_subsystemGroup (τ := Tag.F4) (K := K) ((mem_f4LongSupport _).2
    (Or.inl rfl)) (-1)
  rw [h1, f4Long_data.Mat_mul (mul_mem hx hy) hx, f4Long_data.Mat_mul hx hy, f4Long_Mat_x1,
    f4Long_Mat_y1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [f4LongN, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

theorem f4Long_Mat_n1_inv :
    f4Long_data.Mat (weylElt Tag.F4 K (f4Index 0) 1)⁻¹ = f4LongNinv := by
  have hn : weylElt Tag.F4 K (f4Index 0) 1 ∈ subsystemGroup Tag.F4 K f4LongSupport :=
    weylElt_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) 1
  rw [f4Long_data.Mat_inv hn, f4Long_Mat_n1]
  exact Matrix.inv_eq_right_inv f4LongN_mul_Ninv

theorem f4LongRootFamily_of_eq {i j : Fin 3} {g : K → ModGL Tag.F4 K}
    (hg : ∀ t, pinnedX Tag.F4 K (chainRoot f4chainLong i j) t = g t)
    (h : ∀ t, f4Long_data.Mat (g t) = 1 + single i j t) : F4LongRootFamily K i j :=
  ⟨1, fun t => by rw [hg, h, Units.val_one, one_mul]⟩

theorem f4LongRootFamily_02 : F4LongRootFamily K 0 2 := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 0)
    (isRoot_single Tag.F4 (f4Index 1))
  have hr : reflect Tag.F4 (f4Index 0) (Pi.single (f4Index 1) 1) = chainRoot f4chainLong 0 2 := by
    decide +kernel
  rw [hr] at h
  have hn : weylElt Tag.F4 K (f4Index 0) 1 ∈ subsystemGroup Tag.F4 K f4LongSupport :=
    weylElt_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) 1
  have hα : Pi.single (f4Index 1) 1 ∈ parabolicRoots Tag.F4 f4LongSupport := by
    have := f4chainLong_mem_parabolicRoots (k := 1) (l := 2) (by decide)
    rwa [f4chainLong_values.2.1] at this
  refine ⟨Units.mkOfMulEqOne ε ε hεε, fun t => ?_⟩
  have e : pinnedX Tag.F4 K (chainRoot f4chainLong 0 2) t =
      weylElt Tag.F4 K (f4Index 0) 1 * pinnedX Tag.F4 K (Pi.single (f4Index 1) 1) (ε * t) *
        (weylElt Tag.F4 K (f4Index 0) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := pinnedX_mem_f4Long hα (ε * t)
  rw [e, f4Long_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Long_data.Mat_mul hn hX,
    f4Long_Mat_n1, f4Long_Mat_n1_inv, pinnedX_single, f4Long_Mat_x2]
  exact f4LongN_conj_12 _

theorem f4LongRootFamily_20 : F4LongRootFamily K 2 0 := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 0)
    (isRoot_neg_single Tag.F4 (f4Index 1))
  have hr : reflect Tag.F4 (f4Index 0) (-Pi.single (f4Index 1) 1) = chainRoot f4chainLong 2 0 := by
    decide +kernel
  rw [hr] at h
  have hn : weylElt Tag.F4 K (f4Index 0) 1 ∈ subsystemGroup Tag.F4 K f4LongSupport :=
    weylElt_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) 1
  have hα : -Pi.single (f4Index 1) 1 ∈ parabolicRoots Tag.F4 f4LongSupport := by
    have := f4chainLong_mem_parabolicRoots (k := 2) (l := 1) (by decide)
    rwa [f4chainLong_values.2.2.2] at this
  refine ⟨Units.mkOfMulEqOne ε ε hεε, fun t => ?_⟩
  have e : pinnedX Tag.F4 K (chainRoot f4chainLong 2 0) t =
      weylElt Tag.F4 K (f4Index 0) 1 * pinnedX Tag.F4 K (-Pi.single (f4Index 1) 1) (ε * t) *
        (weylElt Tag.F4 K (f4Index 0) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := pinnedX_mem_f4Long hα (ε * t)
  rw [e, f4Long_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Long_data.Mat_mul hn hX,
    f4Long_Mat_n1, f4Long_Mat_n1_inv, pinnedX_neg_single, f4Long_Mat_y2]
  exact f4LongN_conj_21 _

theorem f4LongRootFamily_all : ∀ i j : Fin 3, i ≠ j → F4LongRootFamily K i j := by
  obtain ⟨c01, c12, c10, c21⟩ := f4chainLong_values
  have f01 : F4LongRootFamily K 0 1 := f4LongRootFamily_of_eq
    (fun t => by rw [c01, pinnedX_single]) f4Long_Mat_x1
  have f12 : F4LongRootFamily K 1 2 := f4LongRootFamily_of_eq
    (fun t => by rw [c12, pinnedX_single]) f4Long_Mat_x2
  have f10 : F4LongRootFamily K 1 0 := f4LongRootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) f4Long_Mat_y1
  have f21 : F4LongRootFamily K 2 1 := f4LongRootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) f4Long_Mat_y2
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f4LongRootFamily_02
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 2, 0, _ => exact f4LongRootFamily_20
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h

theorem f4LongRep_surjective : Function.Surjective (f4LongRep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, h⟩ := f4LongRootFamily_all (K := K) i j hij
  have hmem := pinnedX_mem_f4Long (f4chainLong_mem_parabolicRoots hij) ((ε⁻¹ : Kˣ) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_f4LongRep, h, CFSG.LinearGroups.coe_transvection]
  rw [← mul_assoc, Units.mul_inv, one_mul]

theorem mem_subsystemTorus_f4Long {g : ModGL Tag.F4 K} :
    g ∈ subsystemTorus Tag.F4 K f4LongSupport ↔
      ∃ a b : Kˣ, g = torus2Elt (f4Index 0) (f4Index 1) a b :=
  mem_subsystemTorus_pair (f4Index 0) (f4Index 1)

theorem range_f4LongPosRoot : Set.range f4LongPosRoot = parabolicPosRoots Tag.F4 f4LongSupport := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨k, l, hkl, hm⟩ := exists_chain_of_f4LongPosRoot m
    rw [hm]
    have hmem := f4chainLong_mem_parabolicRoots hkl.ne
    exact ⟨hmem, hmem.1, (f4chainLong_height_pos k l hkl.ne).2 hkl⟩
  · rintro ⟨hβ, -, hpos⟩
    obtain ⟨k, l, hkl, rfl⟩ := exists_f4chainLong_of_mem hβ
    exact exists_f4LongPosRoot k l ((f4chainLong_height_pos k l hkl).1 hpos)

theorem f4LongPosRoot_eq (m : Fin 3) :
    f4LongPosRoot m = chainRoot f4chainLong (KE.a2PosRow m) (KE.a2PosCol m) := by
  fin_cases m <;> rfl

theorem f4LongPosRoot_mem (m : Fin 3) : f4LongPosRoot m ∈ parabolicRoots Tag.F4 f4LongSupport :=
  (show f4LongPosRoot m ∈ parabolicPosRoots Tag.F4 f4LongSupport from
    range_f4LongPosRoot ▸ ⟨m, rfl⟩).1

theorem f4Long_eq_one_of_Mat_mul_eq_one {t u : ModGL Tag.F4 K}
    (ht : t ∈ subsystemTorus Tag.F4 K f4LongSupport)
    (hu : u ∈ parabolicLeviUnipotent Tag.F4 K f4LongSupport) (h : f4Long_data.Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_f4Long.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) f4LongPosRoot
    f4LongPosRoot_injective range_f4LongPosRoot).surjOn hu
  choose ε hε using f4LongRootFamily_all (K := K)
  have hrc : ∀ m, KE.a2PosRow m ≠ KE.a2PosCol m := fun m => (KE.a2PosRow_lt_col m).ne
  set y : Fin 3 → K := fun m => ((ε (KE.a2PosRow m) (KE.a2PosCol m) (hrc m) : Kˣ) : K) * x m
    with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.F4 K (f4LongPosRoot m) (x m),
      g ∈ subsystemGroup Tag.F4 K f4LongSupport := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_f4Long (f4LongPosRoot_mem m) _
  have hu' : f4Long_data.Mat (List.ofFn fun m => pinnedX Tag.F4 K (f4LongPosRoot m) (x m)).prod =
      1 + (single 1 2 (y 0) + (single 0 1 (y 1) + single 0 2 (y 2))) := by
    rw [f4Long_data.Mat_list_prod _ hlist, List.map_ofFn, ← KE.prod_a2Pos y]
    refine congrArg List.prod (congrArg List.ofFn (funext fun m => ?_))
    rw [Function.comp_apply, f4LongPosRoot_eq, hε]
  rw [f4Long_data.Mat_mul (torus2Elt_mem_f4Long a b) (Subgroup.list_prod_mem _ hlist),
    f4Long_Mat_torus, hu'] at h
  have e : ∀ p q, (Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] *
      (1 + (single 1 2 (y 0) + (single 0 1 (y 1) + single 0 2 (y 2)))) :
        Matrix (Fin 3) (Fin 3) K) p q = (1 : Matrix (Fin 3) (Fin 3) K) p q := fun p q => by
    rw [h]
  have d0 := e 0 0
  have d1 := e 1 1
  simp [Matrix.diagonal_mul, Matrix.add_apply] at d0 d1
  have ha : a = 1 := Units.ext (by simpa using d0)
  subst ha
  have hb : b = 1 := Units.ext (by simpa using d1)
  subst hb
  have o0 := e 1 2
  have o1 := e 0 1
  have o2 := e 0 2
  simp [Matrix.diagonal_mul, Matrix.add_apply] at o0 o1 o2
  have hy0 : ∀ m, y m = 0 := by
    intro m
    fin_cases m
    exacts [o0, o1, o2]
  have hx0 : x = 0 := by
    funext m
    have h0 := hy0 m
    rw [hy] at h0
    exact (mul_eq_zero.1 h0).resolve_left (Units.ne_zero _)
  subst hx0
  refine ⟨torus2Elt_one _ _, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem f4LongRep_injective : Function.Injective (f4LongRep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : f4Long_data.Mat (g : ModGL Tag.F4 K) = 1 := congrArg Subtype.val hg
  exact Subtype.ext (f4Long_bruhat.Mat_eq_one
    (fun t ht u hu => f4Long_eq_one_of_Mat_mul_eq_one ht hu) g.2 hmat)

end Families

end CFSG.RankThree.PartOne.KF4

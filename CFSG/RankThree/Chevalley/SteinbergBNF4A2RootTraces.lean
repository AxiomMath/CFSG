module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4RootSL2Traces

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial Matrix
  Polynomial SteinbergBN

variable {L : Type} [Field L]

@[expose] def sl2BlockMat {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem sl2BlockMat_mul {K : Type} [Field K] (A B : Matrix (Fin 2) (Fin 2) K) :
    sl2BlockMat (A * B) = sl2BlockMat A * sl2BlockMat B := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sl2BlockMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_sl2BlockMat {K : Type} [Field K] (A : SL2 K) :
    (sl2BlockMat (A : Matrix (Fin 2) (Fin 2) K)).det = 1 := by
  rw [Matrix.det_fin_three]
  have h := det_SL2 A
  simp only [sl2BlockMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  linear_combination h

@[expose] def sl2BlockDiag (K : Type) [Field K] : SL2 K →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨sl2BlockMat (A : Matrix (Fin 2) (Fin 2) K), det_sl2BlockMat A⟩
  map_one' := by
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  map_mul' A B := Subtype.ext (sl2BlockMat_mul (A : Matrix (Fin 2) (Fin 2) K) B)

theorem coe_sl2BlockDiag (K : Type) [Field K] (A : SL2 K) :
    ((sl2BlockDiag K A : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      sl2BlockMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem sl2BlockDiag_injective (K : Type) [Field K] : Function.Injective (sl2BlockDiag K) := by
  intro A B h
  have e := fun a b => congrFun (congrFun (congrArg Subtype.val h) a) b
  refine SL2_ext ?_ ?_ ?_ ?_
  · simpa [coe_sl2BlockDiag, sl2BlockMat] using e 0 0
  · simpa [coe_sl2BlockDiag, sl2BlockMat] using e 0 1
  · simpa [coe_sl2BlockDiag, sl2BlockMat] using e 1 0
  · simpa [coe_sl2BlockDiag, sl2BlockMat] using e 1 1

theorem sl2BlockDiag_uSL (c : L) : sl2BlockDiag L (uSL c) = t01 c := by
  apply Subtype.ext
  rw [CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_sl2BlockDiag, sl2BlockMat, coe_uSL]

theorem sl2BlockDiag_vSL (c : L) : sl2BlockDiag L (vSL c) = t10 c := by
  apply Subtype.ext
  rw [CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_sl2BlockDiag, sl2BlockMat, coe_vSL]

@[expose] def f4A2Iota
    (K : Type) [Field K] (κ : F4A2Kind) :
    SL2 K →* subsystemGroup Tag.F4 K {κ.i, κ.j} :=
  (f4A2Equiv K κ).symm.toMonoidHom.comp (sl2BlockDiag K)

theorem f4A2Equiv_f4A2Iota
    (κ : F4A2Kind) (A : SL2 L) :
    f4A2Equiv L κ (f4A2Iota L κ A) = sl2BlockDiag L A := by
  rw [f4A2Iota, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem f4A2Iota_injective
    (κ : F4A2Kind) : Function.Injective (f4A2Iota L κ) :=
  (f4A2Equiv L κ).symm.injective.comp (sl2BlockDiag_injective L)

theorem coe_f4A2Iota
    (κ : F4A2Kind) (A : SL2 L) :
    ((f4A2Iota L κ A : subsystemGroup Tag.F4 L {κ.i, κ.j}) : ModGL Tag.F4 L) =
      simpleRootSL2 Tag.F4 L κ.i A := by
  have hr := isElemRep_f4A2Rep L κ
  have hu : ∀ c : L, f4A2Iota L κ (uSL c) = qx (left_mem_pair κ.i κ.j) c := fun c => by
    apply (f4A2Equiv L κ).injective
    rw [f4A2Equiv_f4A2Iota, sl2BlockDiag_uSL, f4A2Equiv_apply, (hr c).1]
  have hv : ∀ c : L, f4A2Iota L κ (vSL c) = qy (left_mem_pair κ.i κ.j) c := fun c => by
    apply (f4A2Equiv L κ).injective
    rw [f4A2Equiv_f4A2Iota, sl2BlockDiag_vSL, f4A2Equiv_apply, (hr c).2.1]
  have h : (subsystemGroup Tag.F4 L {κ.i, κ.j}).subtype.comp (f4A2Iota L κ) =
      simpleRootSL2 Tag.F4 L κ.i :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change ((f4A2Iota L κ (uSL c) : subsystemGroup Tag.F4 L {κ.i, κ.j}) : ModGL Tag.F4 L) =
          simpleRootSL2 Tag.F4 L κ.i (uSL c)
        rw [hu, simpleRootSL2_uSL, coe_qx]
      · change ((f4A2Iota L κ (vSL c) : subsystemGroup Tag.F4 L {κ.i, κ.j}) : ModGL Tag.F4 L) =
          simpleRootSL2 Tag.F4 L κ.i (vSL c)
        rw [hv, simpleRootSL2_vSL, coe_qy]
  exact DFunLike.congr_fun h A

@[expose] def F4A2Kind.tracePoly : F4A2Kind → ℤ[X]
  | .long => X ^ 2 + 14 * X + 20
  | .short => 7 * X ^ 2 + 8 * X + 8

theorem trace_simpleRootSL2_of_HSL_mul_uSL
    {τ : Tag} (i : Fin τ.rank) (P : ℤ[X])
    (hP : ∀ (L : Type) [Field L] (c : Lˣ) (s : L),
      LinearMap.trace L (RootModule τ L)
          (simpleRootSL2 τ L i (HSL c * uSL s) : Module.End L (RootModule τ L)) =
        aeval ((c : L) + (c⁻¹ : Lˣ)) P)
    {k : Type} [Field k] (A : SL2 k) :
    LinearMap.trace k (RootModule τ k) (simpleRootSL2 τ k i A : Module.End k (RootModule τ k)) =
      aeval (A : Matrix (Fin 2) (Fin 2) k).trace P := by
  set L := AlgebraicClosure k
  set f : k →+* L := algebraMap k L
  apply f.injective
  rw [← trace_baseChangeGL, baseChangeGL_simpleRootSL2]
  set A' := Matrix.SpecialLinearGroup.map f A
  obtain ⟨Q, hQ⟩ := exists_conj_lower_eq_zero_of_isAlgClosed A'
  set B := Q⁻¹ * A' * Q with hB
  have hA' : A' = Q * B * Q⁻¹ := by rw [hB]; group
  have hBe := eq_HSL_mul_uSL hQ
  set u := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hQ)
  set s := (B : Matrix (Fin 2) (Fin 2) L) 0 1 / (B : Matrix (Fin 2) (Fin 2) L) 0 0
  have htr : f (A : Matrix (Fin 2) (Fin 2) k).trace = (u : L) + (u⁻¹ : Lˣ) := by
    have h1 : f (A : Matrix (Fin 2) (Fin 2) k).trace = (A' : Matrix (Fin 2) (Fin 2) L).trace := by
      simp [A', Matrix.trace_fin_two]
    have h2 : (A' : Matrix (Fin 2) (Fin 2) L).trace = (B : Matrix (Fin 2) (Fin 2) L).trace := by
      rw [hA', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, one_mul]
    rw [h1, h2, hBe, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two]
    simp [coe_HSL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hA', map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, LinearMap.trace_conj, hBe,
    hP L u s, ← htr]
  exact aeval_algebraMap_apply L _ _

theorem rootExponents_F4_zero :
    (rootExponents Tag.F4 0).toFinset ⊆ {-2, -1, 0, 1, 2} ∧
      (rootExponents Tag.F4 0).count (-2) = 1 ∧ (rootExponents Tag.F4 0).count (-1) = 14 ∧
      (rootExponents Tag.F4 0).count 0 = 18 ∧ (rootExponents Tag.F4 0).count 1 = 14 ∧
      (rootExponents Tag.F4 0).count 2 = 1 :=
  rootExponents_F4_long 0 (by decide)

theorem rootExponents_F4_two :
    (rootExponents Tag.F4 2).toFinset ⊆ {-2, -1, 0, 1, 2} ∧
      (rootExponents Tag.F4 2).count (-2) = 7 ∧ (rootExponents Tag.F4 2).count (-1) = 8 ∧
      (rootExponents Tag.F4 2).count 0 = 18 ∧ (rootExponents Tag.F4 2).count 1 = 8 ∧
      (rootExponents Tag.F4 2).count 2 = 7 :=
  rootExponents_F4_short 2 (by decide)

theorem trace_simpleRootSL2_HSL_mul_uSL_F4A2
    (κ : F4A2Kind) (c : Lˣ) (s : L) :
    LinearMap.trace L (RootModule Tag.F4 L)
        (simpleRootSL2 Tag.F4 L κ.i (HSL c * uSL s) : Module.End L (RootModule Tag.F4 L)) =
      aeval ((c : L) + (c⁻¹ : Lˣ)) κ.tracePoly := by
  set d : L := ((c⁻¹ : Lˣ) : L)
  have hcd : (c : L) * d = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ∀ n : ℤ, ((c ^ n : Lˣ) : L) = (c : L) ^ n := fun n => Units.val_zpow_eq_zpow_val c n
  have hd : d = (c : L)⁻¹ := Units.val_inv_eq_inv_val c
  have hneg2 : (c : L) ^ (-2 : ℤ) = d ^ 2 := by
    rw [_root_.zpow_neg, zpow_two, ← pow_two, hd, inv_pow]
  have hneg1 : (c : L) ^ (-1 : ℤ) = d := by rw [_root_.zpow_neg_one, hd]
  have hpos2 : (c : L) ^ (2 : ℤ) = (c : L) ^ 2 := zpow_ofNat _ 2
  rw [map_mul, simpleRootSL2_HSL, simpleRootSL2_uSL, Units.val_mul,
    trace_torusElt_mul_of_isUpperUnitriangular κ.i c (isUpperUnitriangular_xUnit κ.i s),
    sum_torusEigen, sum_isRoot_eq_rootExponents κ.i (fun n => ((c ^ n : Lˣ) : L))]
  cases κ
  · obtain ⟨hset, e1, e2, e3, e4, e5⟩ := rootExponents_F4_zero
    change ((Tag.F4.rank : ℕ) : L) + ((rootExponents Tag.F4 0).map
      fun n => ((c ^ n : Lˣ) : L)).sum = _
    rw [list_sum_map_eq_of_toFinset_subset _ _ hset, e1, e2, e3, e4, e5]
    simp only [hz, hneg2, hneg1, hpos2, nsmul_eq_mul, zpow_zero, zpow_one, Nat.cast_ofNat,
      Nat.cast_one, one_mul, F4A2Kind.tracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat,
      Units.val_one]
    change (4 : L) + _ = _
    linear_combination (-2 : L) * hcd
  · obtain ⟨hset, e1, e2, e3, e4, e5⟩ := rootExponents_F4_two
    change ((Tag.F4.rank : ℕ) : L) + ((rootExponents Tag.F4 2).map
      fun n => ((c ^ n : Lˣ) : L)).sum = _
    rw [list_sum_map_eq_of_toFinset_subset _ _ hset, e1, e2, e3, e4, e5]
    simp only [hz, hneg2, hneg1, hpos2, nsmul_eq_mul, zpow_zero, zpow_one, Nat.cast_ofNat,
      F4A2Kind.tracePoly, map_add, map_pow, map_mul, aeval_X, map_ofNat, Units.val_one]
    change (4 : L) + _ = _
    linear_combination (-14 : L) * hcd

theorem trace_f4A2Iota
    (κ : F4A2Kind) {k : Type} [Field k] (A : SL2 k) :
    LinearMap.trace k (RootModule Tag.F4 k)
        (((f4A2Iota k κ A : subsystemGroup Tag.F4 k {κ.i, κ.j}) : ModGL Tag.F4 k) :
          Module.End k (RootModule Tag.F4 k)) =
      aeval (A : Matrix (Fin 2) (Fin 2) k).trace κ.tracePoly := by
  rw [coe_f4A2Iota]
  exact trace_simpleRootSL2_of_HSL_mul_uSL κ.i κ.tracePoly
    (fun L _ c s => trace_simpleRootSL2_HSL_mul_uSL_F4A2 κ c s) A

theorem closure_range_tracePoly (κ : F4A2Kind) (k : Type) [Field k] [Finite k] :
    Subfield.closure (Set.range fun t : k => aeval t κ.tracePoly) = ⊤ := by
  cases κ
  · have h2 : ringChar k = 2 → (14 : k) = 0 := fun h => by
      have : CharP k 2 := ringChar.of_eq h
      rw [show (14 : k) = 2 * 7 by norm_num, CharTwo.two_eq_zero, zero_mul]
    convert closure_range_quadratic_eq_top (14 : k) 20 h2 using 3
    funext t
    simp only [F4A2Kind.tracePoly, map_add, map_mul, map_pow, aeval_X, map_ofNat]
  · by_cases h7 : (7 : k) = 0
    · have h8 : (8 : k) = 1 := by linear_combination h7
      rw [eq_top_iff]
      intro x _
      refine Subfield.subset_closure ⟨x - 1, ?_⟩
      simp only [F4A2Kind.tracePoly, map_add, map_mul, map_pow, aeval_X, map_ofNat, h7, h8]
      ring
    · set F := Subfield.closure (Set.range fun t : k => aeval t F4A2Kind.short.tracePoly)
      have hb : ringChar k = 2 → (8 / 7 : k) = 0 := fun h => by
        have : CharP k 2 := ringChar.of_eq h
        rw [show (8 : k) = 2 * 4 by norm_num, CharTwo.two_eq_zero, zero_mul, zero_div]
      rw [eq_top_iff, ← closure_range_quadratic_eq_top (8 / 7 : k) (8 / 7) hb, Subfield.closure_le]
      rintro _ ⟨t, rfl⟩
      have h7F : (7 : k) ∈ F := by simp
      have hv : aeval t F4A2Kind.short.tracePoly ∈ F := Subfield.subset_closure ⟨t, rfl⟩
      have e : t ^ 2 + 8 / 7 * t + 8 / 7 = 7⁻¹ * aeval t F4A2Kind.short.tracePoly := by
        simp only [F4A2Kind.tracePoly, map_add, map_mul, map_pow, aeval_X, map_ofNat]
        field_simp
      show t ^ 2 + 8 / 7 * t + 8 / 7 ∈ F
      rw [e]
      exact mul_mem (inv_mem h7F) hv

theorem F4_A2_root_SL2_full_module_traces_all_characteristics
    (κ : F4A2Kind) :
    (∀ (k : Type) [Field k] (A : SL2 k), f4A2Equiv k κ (f4A2Iota k κ A) = sl2BlockDiag k A) ∧
    (∀ (k : Type) [Field k], Function.Injective (f4A2Iota k κ)) ∧
    (∀ (k : Type) [Field k] (A : SL2 k),
      LinearMap.trace k (RootModule Tag.F4 k)
          (((f4A2Iota k κ A : subsystemGroup Tag.F4 k {κ.i, κ.j}) : ModGL Tag.F4 k) :
            Module.End k (RootModule Tag.F4 k)) =
        aeval (A : Matrix (Fin 2) (Fin 2) k).trace κ.tracePoly) ∧
    ∀ (k : Type) [Field k] [Finite k] (M : Type) [Field M] [Algebra k M] (P : GL (Fin 2) M)
      (g : ModGL Tag.F4 M),
      Subfield.closure {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule Tag.F4 M)
        ((g * ((f4A2Iota M κ (conjGL P (Matrix.SpecialLinearGroup.map (algebraMap k M) A)) :
            subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) * g⁻¹ : ModGL Tag.F4 M) :
          Module.End M (RootModule Tag.F4 M))} = (algebraMap k M).fieldRange := by
  refine ⟨fun k _ A => f4A2Equiv_f4A2Iota κ A, fun k _ => f4A2Iota_injective κ,
    fun k _ A => trace_f4A2Iota κ A, fun k _ _ M _ _ P g => ?_⟩
  set f : k →+* M := algebraMap k M
  have hval : ∀ A : SL2 k, LinearMap.trace M (RootModule Tag.F4 M)
      ((g * ((f4A2Iota M κ (conjGL P (Matrix.SpecialLinearGroup.map f A)) :
          subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) * g⁻¹ : ModGL Tag.F4 M) :
        Module.End M (RootModule Tag.F4 M)) =
      f (aeval (A : Matrix (Fin 2) (Fin 2) k).trace κ.tracePoly) := by
    intro A
    rw [Units.val_mul, Units.val_mul, LinearMap.trace_conj, trace_f4A2Iota, trace_conjGL]
    have htr : ((Matrix.SpecialLinearGroup.map f A : SL2 M) : Matrix (Fin 2) (Fin 2) M).trace =
        f (A : Matrix (Fin 2) (Fin 2) k).trace := by
      simp [Matrix.trace_fin_two]
    rw [htr]
    exact aeval_algebraMap_apply M _ _
  have hS : {x : M | ∃ A : SL2 k, x = LinearMap.trace M (RootModule Tag.F4 M)
      ((g * ((f4A2Iota M κ (conjGL P (Matrix.SpecialLinearGroup.map f A)) :
          subsystemGroup Tag.F4 M {κ.i, κ.j}) : ModGL Tag.F4 M) * g⁻¹ : ModGL Tag.F4 M) :
        Module.End M (RootModule Tag.F4 M))} =
      f '' Set.range fun t : k => aeval t κ.tracePoly := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, (hval A).symm⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      refine ⟨companionSL t, ?_⟩
      rw [hval, trace_companionSL]
  rw [hS, ← RingHom.map_field_closure, closure_range_tracePoly κ k, RingHom.fieldRange_eq_map]

end CFSG.RankThree.Chevalley

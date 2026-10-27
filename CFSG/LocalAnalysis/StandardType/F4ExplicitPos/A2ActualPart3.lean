module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2ActualPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.A2Actual
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
open CFSG.StandardType.F4ExplicitPos.PositiveNo117
open scoped Pointwise
variable {K : Type} [Field K]
open scoped MatrixGroups
open Matrix

theorem f4_mat_eq_one_min
    {n : ℕ} {J : Set (Fin Tag.F4.rank)}
    {w : Fin n → Fin Tag.F4.rank → ℤ} {D : MinNativeData Tag.F4 n J w} {k₀ : Fin n}
    (B : MinNativeBruhat D k₀)
    (hbruhat : ∀ {g : ModGL Tag.F4 K}, g ∈ subsystemGroup Tag.F4 K J →
      ∃ w ∈ parabolicWeylGroup Tag.F4 J, ∃ b ∈ subsystemBorel Tag.F4 K J,
        ∃ v ∈ rootSpan Tag.F4 K (inversionSet w) ⊓ subsystemGroup Tag.F4 K J,
          b * canonicalRep (coxeterSystem Tag.F4) K w * v = g)
    (hrec : ∀ t ∈ subsystemTorus Tag.F4 K J, ∀ u ∈ parabolicLeviUnipotent Tag.F4 K J,
      D.Mat (t * u) = 1 → t = 1 ∧ u = 1)
    {g : ModGL Tag.F4 K} (hg : g ∈ subsystemGroup Tag.F4 K J) (hmat : D.Mat g = 1) : g = 1 := by
  have hfixv : ∀ k, (g : Module.End K (RootModule Tag.F4 K)) (D.vec K k) = D.vec K k := by
    intro k
    rw [D.apply_vec hg, hmat]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ m ∈ D.module K, (g : Module.End K (RootModule Tag.F4 K)) m = m := by
    intro m hm
    have e := D.eq_sum_of_mem_module hm
    calc (g : Module.End K (RootModule Tag.F4 K)) m =
        (g : Module.End K (RootModule Tag.F4 K)) (∑ k, m (D.label k) • D.vec K k) := by rw [← e]
      _ = ∑ k, m (D.label k) • D.vec K k := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hfixv]
      _ = m := e.symm
  obtain ⟨w', hw, b, hb, v, hv, hgbv⟩ := hbruhat hg
  have hbB : b ∈ borelGroup Tag.F4 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.F4 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv.1
  have hvB : v ∈ borelGroup Tag.F4 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup Tag.F4 K J := hv.2
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.F4) K w' : Module.End K (RootModule Tag.F4 K))
      (D.vec K j) = ((b⁻¹ * v⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))
        (D.vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.F4) K w' = b⁻¹ * (g : ModGL Tag.F4 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (D.mem_module_of_mem (inv_mem hvS) (D.vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j' : Fin n, w j' = w' • w j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec_of_isRoot (K := K) w' (D.isRoot j)
    have h0 := B.borel_apply_vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hlt
    rw [← hn j, ← D.rootVec_w K j, hne, ← hj', D.rootVec_w K j', Finsupp.smul_apply, D.vec_apply,
      ite_eq_left rfl, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w' = 1 := B.eq_one_of_smul_weight hw (B.smul_weight_eq_of_not_lt hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.F4 K (∅ : Set (Fin Tag.F4.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact Subgroup.mem_bot.1 (Subgroup.mem_inf.1 hv).1
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus Tag.F4 K J : Set (ModGL Tag.F4 K)) *
      (parabolicLeviUnipotent Tag.F4 K J : Set (ModGL Tag.F4 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.F4) (K := K) (A := J)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  beta_reduce at hgbv
  have h1 := hrec t ht u hu (by rw [hgbv]; exact hmat)
  rw [← hgbv, h1.1, h1.2, mul_one]

theorem f4LongRep_injective_actual :
    Function.Injective (f4LongRep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : f4Long_data.Mat (g : ModGL Tag.F4 K) = 1 := congrArg Subtype.val hg
  exact Subtype.ext (f4_mat_eq_one_min f4Long_bruhat
    (f4_subsystem_bruhat_no117_actual f4LongSupport)
    (fun t ht u hu => f4Long_eq_one_of_Mat_mul_eq_one_actual ht hu) g.2 hmat)

theorem f4LongRep_surjective_actual :
    Function.Surjective (f4LongRep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, h⟩ := f4LongRootFamily_all_actual (K := K) i j hij
  have hmem := f4_pinnedX_mem_f4Long (f4chainLong_mem_parabolicRoots hij) ((ε⁻¹ : Kˣ) * c)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [coe_f4LongRep, h, CFSG.LinearGroups.coe_transvection]
  rw [← mul_assoc, Units.mul_inv, one_mul]

theorem f4LongRep_bijective_actual :
    Function.Bijective (f4LongRep K) :=
  ⟨f4LongRep_injective_actual, f4LongRep_surjective_actual⟩

def f4LongEquiv_actual :
    SL(3, K) ≃* subsystemGroup Tag.F4 K f4LongSupport :=
  (MulEquiv.ofBijective (f4LongRep K) (f4LongRep_bijective_actual)).symm

def f4rhoLong_actual :
    SL(3, K) →* ModGL Tag.F4 K :=
  (subsystemGroup Tag.F4 K f4LongSupport).subtype.comp (f4LongEquiv_actual).toMonoidHom

theorem f4LongRep_f4LongEquiv_actual
    (X : SL(3, K)) : f4LongRep K (f4LongEquiv_actual X) = X :=
  (MulEquiv.ofBijective (f4LongRep K) (f4LongRep_bijective_actual)).apply_symm_apply X

theorem f4rhoLong_f4LongRep_actual
    {g : ModGL Tag.F4 K}
    (hg : g ∈ subsystemGroup Tag.F4 K f4LongSupport) :
    f4rhoLong_actual (f4LongRep K ⟨g, hg⟩) = g := by
  have h := (MulEquiv.ofBijective (f4LongRep K) (f4LongRep_bijective_actual)).symm_apply_apply
    (⟨g, hg⟩ : subsystemGroup Tag.F4 K f4LongSupport)
  exact congrArg Subtype.val h

theorem f4rhoLong_mem_actual
    (X : SL(3, K)) :
    f4rhoLong_actual X ∈ subsystemGroup Tag.F4 K f4LongSupport :=
  (f4LongEquiv_actual X).2

theorem Mat_f4rhoLong_actual
    (X : SL(3, K)) :
    f4Long_data.Mat (f4rhoLong_actual X) = (X : Matrix (Fin 3) (Fin 3) K) :=
  congrArg (fun Y : SL(3, K) => (Y : Matrix (Fin 3) (Fin 3) K))
    (f4LongRep_f4LongEquiv_actual X)

theorem f4rhoLong_injective_actual :
    Function.Injective (f4rhoLong_actual (K := K)) := by
  intro X Y h
  apply Subtype.ext
  rw [← Mat_f4rhoLong_actual X, ← Mat_f4rhoLong_actual Y, h]

theorem f4rhoLong_range_actual :
    (f4rhoLong_actual).range = subsystemGroup Tag.F4 K f4LongSupport := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ f4rhoLong_mem_actual X) fun g hg => ?_
  exact ⟨f4LongRep K ⟨g, hg⟩, f4rhoLong_f4LongRep_actual hg⟩

theorem f4rhoLong_transvection_actual
    (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Kˣ, ∀ t : K, f4rhoLong_actual (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.F4 K (chainRoot f4chainLong i j) ((ε : K) * t) := by
  obtain ⟨ε, hε⟩ := f4LongRootFamily_all_actual (K := K) i j hij
  refine ⟨ε⁻¹, fun s => ?_⟩
  have hmem := f4_pinnedX_mem_f4Long (K := K) (f4chainLong_mem_parabolicRoots hij)
    (((ε⁻¹ : Kˣ) : K) * s)
  have hrep : f4LongRep K ⟨pinnedX Tag.F4 K (chainRoot f4chainLong i j) (((ε⁻¹ : Kˣ) : K) * s),
      hmem⟩ = Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_f4LongRep, hε, CFSG.LinearGroups.coe_transvection]
    congr 2
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [← hrep]
  exact f4rhoLong_f4LongRep_actual hmem

theorem f4rhoLong_diag_actual
    (A : SL(3, K))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    f4rhoLong_actual A ∈ torusGroup Tag.F4 K := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) K) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) K).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Kˣ := Units.mk0 _ h0 with hua
  set ub : Kˣ := Units.mk0 _ h01 with hub
  have hrep : f4LongRep K ⟨torus2Elt (f4Index 0) (f4Index 1) ua ub,
      torus2Elt_mem_f4Long ua ub⟩ = A := by
    apply Subtype.ext
    rw [coe_f4LongRep, f4Long_Mat_torus, hdiag]
    have h22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 =
        ((A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hJ : f4rhoLong_actual A = torus2Elt (f4Index 0) (f4Index 1) ua ub := by
    rw [← hrep]
    exact f4rhoLong_f4LongRep_actual (torus2Elt_mem_f4Long ua ub)
  rw [hJ]
  exact subsystemTorus_le_torusGroup (mem_subsystemTorus_f4Long.2 ⟨ua, ub, rfl⟩)

theorem f4Long_frame_actual :
    IsA2Frame (f4rhoLong_actual (K := K)) (fun i j => chainRoot f4chainLong i j) where
  injective := f4rhoLong_injective_actual
  isRoot i j hij := (f4chainLong_mem_parabolicRoots hij).1
  neg i j := f4chainLong_neg i j
  add i j k := f4chainLong_add i j k
  transv i j hij := f4rhoLong_transvection_actual i j hij
  range := by
    rw [f4rhoLong_range_actual, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    constructor
    · intro hr
      obtain ⟨k, l, hkl, rfl⟩ := exists_f4chainLong_of_mem hr
      exact ⟨k, l, hkl, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact f4chainLong_mem_parabolicRoots hij
  diag A hA := f4rhoLong_diag_actual A hA

theorem f4_pinnedX_mem_f4Short
    {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4ShortSupport) (t : K) :
    pinnedX Tag.F4 K α t ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

theorem f4ShortRootFamily_20_actual :
    F4ShortRootFamily K 2 0 (by decide) := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 2)
    (isRoot_single Tag.F4 (f4Index 3))
  have hs : f4ShortSigma 2 1 = Pi.single (f4Index 3) 1 := f4ShortSigma_values.2.1
  have hr := f4ShortSigma_reflect.1
  rw [← hs, hr] at h
  have hn : weylElt Tag.F4 K (f4Index 2) 1 ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
    weylElt_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) 1
  have hα : f4ShortSigma 2 1 ∈ parabolicRoots Tag.F4 f4ShortSupport :=
    f4ShortSigma_mem_parabolicRoots (by decide)
  refine ⟨Units.mkOfMulEqOne (-ε) (-ε) (by rw [neg_mul_neg]; exact hεε), fun t => ?_⟩
  have e : pinnedX Tag.F4 K (f4ShortSigma 2 0) t =
      weylElt Tag.F4 K (f4Index 2) 1 * pinnedX Tag.F4 K (f4ShortSigma 2 1) (ε * t) *
        (weylElt Tag.F4 K (f4Index 2) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := f4_pinnedX_mem_f4Short hα (ε * t)
  rw [e, f4Short_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Short_data.Mat_mul hn hX,
    Mat_f4Short_n3, Mat_f4Short_n3_inv, Mat_pinnedX_simple_short.2.2.1, ← map_mul, ← map_mul,
    f4ShortN_conj_21]
  congr 2
  simp

theorem f4ShortRootFamily_02_actual :
    F4ShortRootFamily K 0 2 (by decide) := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 2)
    (isRoot_neg_single Tag.F4 (f4Index 3))
  have hs : f4ShortSigma 1 2 = -Pi.single (f4Index 3) 1 := f4ShortSigma_values.2.2.2
  have hr := f4ShortSigma_reflect.2
  rw [← hs, hr] at h
  have hn : weylElt Tag.F4 K (f4Index 2) 1 ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
    weylElt_mem_subsystemGroup ((mem_f4ShortSupport _).2 (Or.inl rfl)) 1
  have hα : f4ShortSigma 1 2 ∈ parabolicRoots Tag.F4 f4ShortSupport :=
    f4ShortSigma_mem_parabolicRoots (by decide)
  refine ⟨Units.mkOfMulEqOne (-ε) (-ε) (by rw [neg_mul_neg]; exact hεε), fun t => ?_⟩
  have e : pinnedX Tag.F4 K (f4ShortSigma 0 2) t =
      weylElt Tag.F4 K (f4Index 2) 1 * pinnedX Tag.F4 K (f4ShortSigma 1 2) (ε * t) *
        (weylElt Tag.F4 K (f4Index 2) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := f4_pinnedX_mem_f4Short hα (ε * t)
  rw [e, f4Short_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Short_data.Mat_mul hn hX,
    Mat_f4Short_n3, Mat_f4Short_n3_inv, Mat_pinnedX_simple_short.2.2.2, ← map_mul, ← map_mul,
    f4ShortN_conj_12]
  congr 2
  simp

theorem f4ShortRootFamily_all_actual :
    ∀ (i j : Fin 3) (hij : i ≠ j), F4ShortRootFamily K i j hij := by
  obtain ⟨f10, f01, f21, f12⟩ := Mat_pinnedX_simple_short (K := K)
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f01
  | 0, 2, _ => exact f4ShortRootFamily_02_actual
  | 1, 0, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f12
  | 2, 0, _ => exact f4ShortRootFamily_20_actual
  | 2, 1, _ => exact f4ShortRootFamily_of_eq (by decide) (fun t => rfl) f21
  | 2, 2, h => exact absurd rfl h

end CFSG.StandardType.F4ExplicitPos.A2Actual
end

end

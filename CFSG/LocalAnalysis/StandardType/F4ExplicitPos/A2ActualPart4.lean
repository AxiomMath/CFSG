module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2ActualPart3

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

theorem f4Short_eq_one_of_Mat_mul_eq_one_actual
    {t u : ModGL Tag.F4 K}
    (ht : t ∈ subsystemTorus Tag.F4 K f4ShortSupport)
    (hu : u ∈ parabolicLeviUnipotent Tag.F4 K f4ShortSupport)
    (h : f4Short_data.Mat (t * u) = 1) : t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_f4Short.1 ht
  obtain ⟨x, -, rfl⟩ := (f4_bijOn_prod_pinnedX_parabolicPosRoots f4ShortPosRoot
    f4ShortPosRoot_injective range_f4ShortPosRoot).surjOn hu
  have f10 := f4ShortRootFamily_all_actual (K := K) 1 0 (by decide)
  have f21 := f4ShortRootFamily_all_actual (K := K) 2 1 (by decide)
  have f20 := f4ShortRootFamily_all_actual (K := K) 2 0 (by decide)
  obtain ⟨ε0, h0⟩ := f10
  obtain ⟨ε1, h1⟩ := f21
  obtain ⟨ε2, h2⟩ := f20
  set y : Fin 3 → K := fun m => (![(ε0 : K), (ε1 : K), (ε2 : K)] m) * x m with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.F4 K (f4ShortPosRoot m) (x m),
      g ∈ subsystemGroup Tag.F4 K f4ShortSupport := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact f4_pinnedX_mem_f4Short (f4ShortPosRoot_mem m) _
  have hMu : f4Short_data.Mat (List.ofFn fun m => pinnedX Tag.F4 K (f4ShortPosRoot m) (x m)).prod =
      symRep K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (y 0) *
        (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (y 1) *
          Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (y 2))) := by
    rw [f4Short_data.Mat_list_prod _ hlist]
    simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    have e0 : f4ShortPosRoot 0 = f4ShortSigma 1 0 := rfl
    have e1 : f4ShortPosRoot 1 = f4ShortSigma 2 1 := rfl
    have e2 : f4ShortPosRoot 2 = f4ShortSigma 2 0 := rfl
    simp only [Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, e0, e1, e2, h0, h1, h2,
      map_mul, hy]
    rfl
  rw [f4Short_data.Mat_mul (torus2Elt_mem_f4Short a b) (Subgroup.list_prod_mem _ hlist),
    Mat_torus2_short, hMu, ← map_mul] at h
  have hDL : f4ShortDiag K a b *
      (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (y 0) *
        (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (y 1) *
          Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (y 2))) = 1 :=
    symRep_injective (by rw [h, map_one])
  have hmat : Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a * b⁻¹ : Kˣ) : K), (b : K)] *
      (1 + (Matrix.single 1 0 (y 0) + (Matrix.single 2 1 (y 1) + Matrix.single 2 0 (y 2)))) =
        (1 : Matrix (Fin 3) (Fin 3) K) := by
    have h' := congrArg (fun A : SL(3, K) => (A : Matrix (Fin 3) (Fin 3) K)) hDL
    rw [Matrix.SpecialLinearGroup.coe_mul, prod_short_pos, Matrix.SpecialLinearGroup.coe_one]
      at h'
    exact h'
  have e : ∀ p q, (Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((a * b⁻¹ : Kˣ) : K), (b : K)] *
      (1 + (Matrix.single 1 0 (y 0) + (Matrix.single 2 1 (y 1) + Matrix.single 2 0 (y 2)))) :
        Matrix (Fin 3) (Fin 3) K) p q = (1 : Matrix (Fin 3) (Fin 3) K) p q := fun p q => by
    rw [hmat]
  have d0 := e 0 0
  have d1 := e 1 1
  simp [Matrix.diagonal_mul, Matrix.add_apply] at d0 d1
  have ha : a = 1 := by
    have : (a⁻¹ : Kˣ) = 1 := Units.ext (by simpa using d0)
    simpa using this
  subst ha
  have hb : b = 1 := by
    have : (b⁻¹ : Kˣ) = 1 := Units.ext (by simpa using d1)
    simpa using this
  subst hb
  have o0 := e 1 0
  have o1 := e 2 1
  have o2 := e 2 0
  simp [Matrix.diagonal_mul, Matrix.add_apply] at o0 o1 o2
  have hy0 : ∀ m, y m = 0 := by
    intro m
    fin_cases m
    exacts [o0, o1, o2]
  have hx0 : x = 0 := by
    funext m
    have h0' := hy0 m
    rw [hy] at h0'
    have hne : ((![(ε0 : K), (ε1 : K), (ε2 : K)] : Fin 3 → K) m) ≠ 0 := by
      fin_cases m <;> simp
    exact (mul_eq_zero.1 h0').resolve_left hne
  subst hx0
  refine ⟨torus2Elt_one _ _, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem f4_mat_eq_one_str
    {n : ℕ} {J : Set (Fin Tag.F4.rank)}
    {w : Fin n → Fin Tag.F4.rank → ℤ} {D : StrNativeData Tag.F4 n J w} {k₀ : Fin n}
    (B : StrNativeBruhat D k₀)
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

theorem f4ShortRep_injective_actual :
    Function.Injective (f4ShortRep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : f4Short_data.Mat (g : ModGL Tag.F4 K) = 1 := by
    rw [Mat_f4ShortRep, hg, map_one]
  exact Subtype.ext (f4_mat_eq_one_str f4Short_bruhat
    (f4_subsystem_bruhat_no117_actual f4ShortSupport)
    (fun t ht u hu => f4Short_eq_one_of_Mat_mul_eq_one_actual ht hu) g.2 hmat)

theorem f4ShortRep_surjective_actual :
    Function.Surjective (f4ShortRep K) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  obtain ⟨ε, h⟩ := f4ShortRootFamily_all_actual (K := K) i j hij
  have hmem := f4_pinnedX_mem_f4Short (f4ShortSigma_mem_parabolicRoots hij) (((ε⁻¹ : Kˣ) : K) * c)
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply symRep_injective
  rw [← Mat_f4ShortRep]
  change f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma i j) (((ε⁻¹ : Kˣ) : K) * c)) =
    symRep K (Matrix.SpecialLinearGroup.transvection hij c)
  rw [h]
  congr 2
  rw [← mul_assoc, Units.mul_inv, one_mul]

theorem f4ShortRep_bijective_actual :
    Function.Bijective (f4ShortRep K) :=
  ⟨f4ShortRep_injective_actual, f4ShortRep_surjective_actual⟩

def f4ShortEquiv_actual :
    SL(3, K) ≃* subsystemGroup Tag.F4 K f4ShortSupport :=
  (MulEquiv.ofBijective (f4ShortRep K) (f4ShortRep_bijective_actual)).symm

def f4rhoShort_actual :
    SL(3, K) →* ModGL Tag.F4 K :=
  (subsystemGroup Tag.F4 K f4ShortSupport).subtype.comp (f4ShortEquiv_actual).toMonoidHom

theorem f4ShortRep_f4ShortEquiv_actual
    (X : SL(3, K)) :
    f4ShortRep K (f4ShortEquiv_actual X) = X :=
  (MulEquiv.ofBijective (f4ShortRep K) (f4ShortRep_bijective_actual)).apply_symm_apply X

theorem f4rhoShort_f4ShortRep_actual
    {g : ModGL Tag.F4 K}
    (hg : g ∈ subsystemGroup Tag.F4 K f4ShortSupport) :
    f4rhoShort_actual (f4ShortRep K ⟨g, hg⟩) = g := by
  have h := (MulEquiv.ofBijective (f4ShortRep K) (f4ShortRep_bijective_actual)).symm_apply_apply
    (⟨g, hg⟩ : subsystemGroup Tag.F4 K f4ShortSupport)
  exact congrArg Subtype.val h

theorem f4rhoShort_mem_actual
    (X : SL(3, K)) :
    f4rhoShort_actual X ∈ subsystemGroup Tag.F4 K f4ShortSupport :=
  (f4ShortEquiv_actual X).2

theorem Mat_f4rhoShort_actual
    (X : SL(3, K)) :
    f4Short_data.Mat (f4rhoShort_actual X) = symRep K X := by
  have h := Mat_f4ShortRep (f4ShortEquiv_actual X)
  rw [f4ShortRep_f4ShortEquiv_actual] at h
  exact h

theorem f4rhoShort_injective_actual :
    Function.Injective (f4rhoShort_actual (K := K)) := by
  intro X Y h
  apply symRep_injective
  rw [← Mat_f4rhoShort_actual X, ← Mat_f4rhoShort_actual Y, h]

theorem f4rhoShort_range_actual :
    (f4rhoShort_actual (K := K)).range = subsystemGroup Tag.F4 K f4ShortSupport := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ f4rhoShort_mem_actual X) fun g hg => ?_
  exact ⟨f4ShortRep K ⟨g, hg⟩, f4rhoShort_f4ShortRep_actual hg⟩

theorem f4rhoShort_transvection_actual
    (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Kˣ, ∀ t : K, f4rhoShort_actual (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.F4 K (f4ShortSigma i j) ((ε : K) * t) := by
  obtain ⟨ε, h⟩ := f4ShortRootFamily_all_actual (K := K) i j hij
  refine ⟨ε⁻¹, fun s => ?_⟩
  have hmem := f4_pinnedX_mem_f4Short (K := K) (f4ShortSigma_mem_parabolicRoots hij)
    (((ε⁻¹ : Kˣ) : K) * s)
  have hrep : f4ShortRep K ⟨pinnedX Tag.F4 K (f4ShortSigma i j) (((ε⁻¹ : Kˣ) : K) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply symRep_injective
    rw [← Mat_f4ShortRep]
    change f4Short_data.Mat (pinnedX Tag.F4 K (f4ShortSigma i j) (((ε⁻¹ : Kˣ) : K) * s)) = _
    rw [h]
    congr 2
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [← hrep]
  exact f4rhoShort_f4ShortRep_actual hmem

theorem f4rhoShort_diag_actual
    (A : SL(3, K))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    f4rhoShort_actual A ∈ torusGroup Tag.F4 K := by
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
  have h2 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := fun h => by
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  set ua : Kˣ := (Units.mk0 _ h0)⁻¹ with hua
  set ub : Kˣ := Units.mk0 _ h2 with hub
  have hAeq : A = f4ShortDiag K ua ub := by
    apply Subtype.ext
    rw [hdiag]
    change Matrix.diagonal _ = Matrix.diagonal ![((ua⁻¹ : Kˣ) : K), ((ua * ub⁻¹ : Kˣ) : K),
      (ub : K)]
    congr 1
    funext i
    have h11 : (A : Matrix (Fin 3) (Fin 3) K) 1 1 =
        ((A : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹ * ((A : Matrix (Fin 3) (Fin 3) K) 2 2)⁻¹ := by
      field_simp
      linear_combination hdet
    fin_cases i <;> simp [hua, hub, h11]
  have hrep : f4ShortRep K ⟨torus2Elt (f4Index 2) (f4Index 3) ua ub,
      torus2Elt_mem_f4Short ua ub⟩ = A := by
    apply symRep_injective
    rw [← Mat_f4ShortRep]
    exact (Mat_torus2_short ua ub).trans (by rw [hAeq])
  have hJ : f4rhoShort_actual A = torus2Elt (f4Index 2) (f4Index 3) ua ub := by
    rw [← hrep]
    exact f4rhoShort_f4ShortRep_actual (torus2Elt_mem_f4Short ua ub)
  rw [hJ]
  exact subsystemTorus_le_torusGroup (mem_subsystemTorus_f4Short.2 ⟨ua, ub, rfl⟩)

theorem f4Short_frame_actual :
    IsA2Frame (f4rhoShort_actual (K := K)) f4ShortSigma where
  injective := f4rhoShort_injective_actual
  isRoot i j hij := (f4ShortSigma_mem_parabolicRoots hij).1
  neg i j := f4ShortSigma_neg i j
  add i j k := f4ShortSigma_add i j k
  transv i j hij := f4rhoShort_transvection_actual i j hij
  range := by
    rw [f4rhoShort_range_actual, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    constructor
    · intro hr
      obtain ⟨k, l, hkl, rfl⟩ := exists_f4ShortSigma_of_mem hr
      exact ⟨k, l, hkl, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact f4ShortSigma_mem_parabolicRoots hij
  diag A hA := f4rhoShort_diag_actual A hA

end CFSG.StandardType.F4ExplicitPos.A2Actual

end

end

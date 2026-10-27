module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinOuter
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOne
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinLift
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TorLinR
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
import CFSG.HardMathSupport.Foote.ModuleExclusions.ProjectiveLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

private lemma l02qfnm_linConjAut_eq_one_scalar {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K]
    {A : GL (Fin d) K} (hA : TableB.linConjAut (Fin d) K A = 1) :
    A ∈ (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
  classical
  have hsingle : ∀ i j : Fin d, i ≠ j →
      (A : Matrix (Fin d) (Fin d) K) * Matrix.single i j (1 : K) =
        Matrix.single i j (1 : K) * (A : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    let T : LargeEvenSLGroup (Fin d) K :=
      ⟨Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (1 : K)), by
        rw [LargeEvenSLGroup, MonoidHom.mem_ker]
        apply Units.ext
        change (Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij (1 : K)) : Matrix (Fin d) (Fin d) K).det = (1 : K)
        rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
          Matrix.SpecialLinearGroup.transvection_coe]
        simpa [Matrix.transvection] using Matrix.det_transvection_of_ne i j hij (1 : K)⟩
    let N : Subgroup (LargeEvenSLGroup (Fin d) K) :=
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K)
    have h1 : TableB.linConjAut (Fin d) K A
        (T : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) =
        (T : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
      simpa using DFunLike.congr_fun hA (T : LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    rw [TableB.linConjAut_mk] at h1
    let z : LargeEvenSLGroup (Fin d) K := (MulAut.conjNormal A T)⁻¹ * T
    have hzN : z ∈ N := by
      have hq := (QuotientGroup.eq (s := N)).mp h1
      simpa [z] using hq
    have hz : MulAut.conjNormal A T * z = T := by
      change MulAut.conjNormal A T * ((MulAut.conjNormal A T)⁻¹ * T) = T
      group
    have hzS : (z : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
      Subgroup.mem_subgroupOf.mp hzN
    have hzcenter : (z : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact hzS
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzcenter
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hzcenter
    have hzGL : ((MulAut.conjNormal A T : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) *
        (z : GL (Fin d) K) = (T : GL (Fin d) K) := by
      simpa using congrArg Subtype.val hz
    rw [MulAut.conjNormal_apply] at hzGL
    rw [← hu] at hzGL
    have hAT : A * (T : GL (Fin d) K) * A⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) u⁻¹ * (T : GL (Fin d) K) := by
      calc A * (T : GL (Fin d) K) * A⁻¹
          = (A * (T : GL (Fin d) K) * A⁻¹ *
              Matrix.GeneralLinearGroup.scalar (Fin d) u) *
              (Matrix.GeneralLinearGroup.scalar (Fin d) u)⁻¹ := by group
        _ = (T : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) u)⁻¹ := by
              rw [hzGL]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) u⁻¹ * (T : GL (Fin d) K) := by
              rw [map_inv]
              exact (Matrix.GeneralLinearGroup.scalar_commute u⁻¹ (T : GL (Fin d) K)).symm
    have hTmat : ((T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 + Matrix.single i j 1 := by
      change (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij (1 : K)) : Matrix (Fin d) (Fin d) K) = _
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.transvection_coe]
    have hAinv : (A : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hAinvA : ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (A : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    let e : Matrix (Fin d) (Fin d) K := Matrix.single i j (1 : K)
    let R : Matrix (Fin d) (Fin d) K :=
      (A : Matrix (Fin d) (Fin d) K) * e *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
    have hATm : (A : Matrix (Fin d) (Fin d) K) * (1 + e) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) * (1 + e) := by
      have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hAT
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv, hTmat,
        Matrix.GeneralLinearGroup.coe_scalar] at h
      simpa [e] using h
    have hsplit : (A : Matrix (Fin d) (Fin d) K) * (1 + e) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + R := by
      rw [mul_add, mul_one, add_mul, hAinv]
    have hRexp : R = Matrix.scalar (Fin d) (((u⁻¹ : Kˣ) : K) - 1) +
        Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) * e := by
      have h := hATm
      rw [hsplit] at h
      have hR : R = Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) * (1 + e) - 1 := by
        rw [← h]
        abel
      rw [hR, mul_add, mul_one]
      rw [show Matrix.scalar (Fin d) (((u⁻¹ : Kˣ) : K) - 1) =
          Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) - 1 by
        rw [map_sub, map_one]]
      abel
    have he2 : e * e = 0 := by
      dsimp [e]
      rw [Matrix.single_mul_single_of_ne (h := hij.symm)]
    have hR2 : R * R = 0 := by
      simp only [R]
      calc (A : Matrix (Fin d) (Fin d) K) * e *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            ((A : Matrix (Fin d) (Fin d) K) * e *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
          = (A : Matrix (Fin d) (Fin d) K) * e *
              (((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
                (A : Matrix (Fin d) (Fin d) K)) * e *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              noncomm_ring
        _ = (A : Matrix (Fin d) (Fin d) K) * e * 1 * e *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              rw [hAinvA]
        _ = (A : Matrix (Fin d) (Fin d) K) * (e * e) *
              ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
              noncomm_ring
        _ = 0 := by
              rw [he2, Matrix.mul_zero, Matrix.zero_mul]
    have hRentry : ∀ k : Fin d, R j k =
        (((u⁻¹ : Kˣ) : K) - 1) * (if j = k then 1 else 0) := by
      intro k
      rw [hRexp, Matrix.add_apply, Matrix.mul_apply]
      have hsum : (∑ l : Fin d, Matrix.scalar (Fin d) ((u⁻¹ : Kˣ) : K) j l *
          Matrix.single i j (1 : K) l k) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        by_cases hli : l = i
        · rw [hli]
          have hji : ¬ j = i := fun h => hij h.symm
          simp [Matrix.scalar_apply, hji]
        · have hil : ¬ i = l := fun h => hli h.symm
          simp [Matrix.single_apply, hil]
      rw [hsum, add_zero]
      by_cases hjk : j = k
      · rw [hjk]
        simp [Matrix.scalar_apply]
      · simp [Matrix.scalar_apply, hjk]
    have hsq : (((u⁻¹ : Kˣ) : K) - 1) ^ 2 = 0 := by
      have h := congrFun (congrFun hR2 j) j
      rw [Matrix.mul_apply] at h
      have hsum : (∑ k : Fin d, R j k * R k j) = R j j * R j j := by
        refine Finset.sum_eq_single j ?_ ?_
        · intro k _ hk
          rw [hRentry k]
          have hkj : ¬ j = k := fun h => hk h.symm
          simp [hkj]
        · intro hj
          exact absurd (Finset.mem_univ j) hj
      rw [hsum, hRentry j] at h
      simpa [pow_two] using h
    have hu1 : ((u⁻¹ : Kˣ) : K) = 1 := by
      have hsub : ((u⁻¹ : Kˣ) : K) - 1 = 0 := by
        have h := hsq
        rw [pow_two] at h
        exact mul_self_eq_zero.mp h
      exact sub_eq_zero.mp hsub
    have hu1' : u⁻¹ = 1 := Units.ext hu1
    have hATm1 : (A : Matrix (Fin d) (Fin d) K) * (1 + e) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + e := by
      rw [hATm, hu1]
      simp
    have hAe : (A : Matrix (Fin d) (Fin d) K) * e *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = e := by
      rw [hsplit, add_left_cancel_iff] at hATm1
      simpa [R] using hATm1
    have hcomm : (A : Matrix (Fin d) (Fin d) K) * e = e * (A : Matrix (Fin d) (Fin d) K) := by
      have h := congrArg (fun M => M * (A : Matrix (Fin d) (Fin d) K)) hAe
      simpa [Matrix.mul_assoc, hAinvA] using h
    simpa [e] using hcomm
  have hpair : Pairwise fun i j : Fin d =>
      Commute (Matrix.single i j 1) (A : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    exact (hsingle i j hij).symm
  have hrange : (A : Matrix (Fin d) (Fin d) K) ∈
      Set.range (Matrix.scalar (Fin d)) :=
    Matrix.mem_range_scalar_of_commute_single hpair
  obtain ⟨a, ha⟩ := hrange
  have ha0 : a ≠ 0 := by
    intro h0
    have hzero : (A : Matrix (Fin d) (Fin d) K) = 0 := by
      rw [← ha, h0, map_zero]
    have hAinv2 : (A : Matrix (Fin d) (Fin d) K) *
        ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hentry := congrFun (congrFun hAinv2 (⟨0, by omega⟩ : Fin d)) (⟨0, by omega⟩ : Fin d)
    simp [Matrix.mul_apply, hzero] at hentry
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact ha

private lemma l02qfnm_orderOf_odd {N p n : ℕ} {K : Type} [Field K] [Finite K]
    (hN : 2 ≤ N) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {g : GL (Fin N) K}
    (hg : TableB.linConjAut (Fin N) K g ^ p = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) : Odd (orderOf g) := by
  classical
  have hker : TableB.linConjAut (Fin N) K (g ^ p) = 1 := by
    rw [map_pow, hg]
  obtain ⟨c, hc⟩ := l02qfnm_linConjAut_eq_one_scalar hN hker
  have hgp : (g ^ p) ^ (2 ^ n - 1) = 1 := by
    rw [← hc, ← map_pow]
    have hcunit : c ^ (2 ^ n - 1) = 1 := by
      haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
      have hcard : Fintype.card Kˣ = 2 ^ n - 1 := by
        rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
      have := pow_card_eq_one (x := c)
      rwa [hcard] at this
    rw [hcunit, map_one]
  have hgpow : g ^ (p * (2 ^ n - 1)) = 1 := by
    rw [pow_mul]; exact hgp
  have hdvd : orderOf g ∣ p * (2 ^ n - 1) := orderOf_dvd_iff_pow_eq_one.mpr hgpow
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hnodd : Odd (2 ^ n - 1) := by
    have h2n : 2 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by norm_num) hn
      simpa using this
    obtain ⟨k, hk⟩ := Nat.even_pow.mpr ⟨even_two, Nat.one_le_iff_ne_zero.mp hn⟩
    exact ⟨k - 1, by omega⟩
  exact (hpodd.mul hnodd).of_dvd_nat hdvd

private theorem l02qfnm_congr_linConjAut {d : ℕ} {K : Type} [Field K] (A : GL (Fin d) K) :
    MulAut.congr (TypeA.recipeEquiv d K) (TableB.linConjAut (Fin d) K A) =
      LinearFlag.conjAut d K A := by
  ext x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective d K x
  set h : LargeEvenSLGroup (Fin d) K := (TypeA.slKerEquiv d K).symm g with hh
  have hg : LinearFlag.proj d K g = TypeA.recipeEquiv d K
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h) := by
    rw [TypeA.recipeEquiv_mk, hh, MulEquiv.apply_symm_apply]
  have hdet : A * (h : GL (Fin d) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin d) K := by
    rw [TypeA.mem_largeEvenSLGroup_iff, Units.val_mul, Units.val_mul, Matrix.det_mul,
      Matrix.det_mul, TypeA.mem_largeEvenSLGroup_iff.mp h.2, mul_one, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  set h' : LargeEvenSLGroup (Fin d) K := ⟨A * (h : GL (Fin d) K) * A⁻¹, hdet⟩ with hh'
  have h1 : TableB.linConjAut (Fin d) K A
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h' := by
    change TableB.linConjAut (Fin d) K A (h : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) =
      (h' : LargeEvenProj (LargeEvenSLGroup (Fin d) K))
    rw [TableB.linConjAut_mk]
    congr 1
  rw [MulAut.congr_apply, hg, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.trans_apply, h1]
  simp only [TypeA.recipeEquiv_mk, LinearFlag.conjAut_proj]
  apply congrArg (LinearFlag.proj d K)
  ext i j
  rw [TypeA.coe_slConjugation', TypeA.coe_slKerEquiv]
  rfl

private theorem l02qfnm_congr_fieldAut {d : ℕ} {K : Type} [Field K] {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))
      (fun x x' => ((x' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ) f) :
    MulAut.congr (TypeA.recipeEquiv d K) f = LinearFlag.fieldAut d K σ := by
  ext x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective d K x
  set h : LargeEvenSLGroup (Fin d) K := (TypeA.slKerEquiv d K).symm g with hh
  have hsymm : (TypeA.recipeEquiv d K).symm (LinearFlag.proj d K g) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h := by
    rw [MulEquiv.symm_apply_eq, TypeA.recipeEquiv_mk, hh, MulEquiv.apply_symm_apply]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hsymm]
  have hrel : ((Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin d) K) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ :=
    CFSG.LocalAnalysis.GLTheoremA.YS09Field.coe_glMap σ.toRingHom (h : GL (Fin d) K)
  rw [hgraph h ⟨Matrix.GeneralLinearGroup.map σ.toRingHom (h : GL (Fin d) K),
      CFSG.LocalAnalysis.GLTheoremA.YS09Field.sl_map_mem σ (h : GL (Fin d) K) h.2⟩ hrel]
  rw [TypeA.recipeEquiv_mk, LinearFlag.fieldAut_proj]
  apply congrArg (LinearFlag.proj d K)
  ext i j
  have hcoe : ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin d) (Fin d) K) := by
    rw [hh]; rfl
  rw [Matrix.SpecialLinearGroup.map_apply_coe, TypeA.coe_slKerEquiv]
  rw [CFSG.LocalAnalysis.GLTheoremA.YS09Field.coe_glMap, hcoe]
  rfl

private lemma l02qfnm_sigma_ne_one {N : ℕ} {K : Type} [Field K]
    {σ : K ≃+* K} {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (fun x x' => ((x' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ) f)
    (hf1 : f ≠ 1) : σ ≠ 1 := by
  rintro rfl
  apply hf1
  ext x
  obtain ⟨g, rfl⟩ := (QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K))) x
  exact hgraph g g (by simp)

private lemma l02qfnm_sigma_smul {N : ℕ} (hN : 2 ≤ N) {K : Type} [Field K]
    {M : GL (Fin N) K} {σ : K ≃+* K}
    {h f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hM : h = TableB.linConjAut (Fin N) K M)
    (hgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (fun x x' => ((x' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ) f)
    (hcomm : h * f = f * h) :
    ∃ μ : K, (M : Matrix (Fin N) (Fin N) K).map σ = μ • (M : Matrix (Fin N) (Fin N) K) := by
  classical
  let c : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) ≃*
      MulAut (LinearFlag.projectiveSL N K) := MulAut.congr (TypeA.recipeEquiv N K)
  have hch : c h = LinearFlag.conjAut N K M := by
    rw [hM]
    exact l02qfnm_congr_linConjAut M
  have hcf : c f = LinearFlag.fieldAut N K σ :=
    l02qfnm_congr_fieldAut hgraph
  have h1 : LinearFlag.conjAut N K M * LinearFlag.fieldAut N K σ =
      LinearFlag.fieldAut N K σ * LinearFlag.conjAut N K M := by
    have := congrArg c hcomm
    simpa [map_mul, hch, hcf] using this
  have h2 : LinearFlag.conjAut N K M =
      LinearFlag.conjAut N K (Matrix.GeneralLinearGroup.map σ.toRingHom M) := by
    have h := h1
    rw [CFSG.HardMathSupport.Foote.ModuleExclusions.fieldAut_mul_conjAut] at h
    exact mul_right_cancel h
  have h3 : LinearFlag.conjAut N K
      (M⁻¹ * Matrix.GeneralLinearGroup.map σ.toRingHom M) = 1 := by
    rw [map_mul, map_inv, ← h2, inv_mul_cancel]
  have hX1 : TableB.linConjAut (Fin N) K
      (M⁻¹ * Matrix.GeneralLinearGroup.map σ.toRingHom M) = 1 := by
    apply c.injective
    rw [map_one, l02qfnm_congr_linConjAut, h3]
  obtain ⟨u, hu⟩ := l02qfnm_linConjAut_eq_one_scalar hN hX1
  have hXeq : Matrix.GeneralLinearGroup.map σ.toRingHom M =
      M * Matrix.GeneralLinearGroup.scalar (Fin N) u := by
    rw [hu]
    group
  refine ⟨(u : K), ?_⟩
  have hmat := congrArg (fun z : GL (Fin N) K => (z : Matrix (Fin N) (Fin N) K)) hXeq
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at hmat
  rw [CFSG.LocalAnalysis.GLTheoremA.YS09Field.coe_glMap] at hmat
  have hdiag : (M : Matrix (Fin N) (Fin N) K) *
      Matrix.diagonal (fun _ => (u : K)) = (u : K) • (M : Matrix (Fin N) (Fin N) K) := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [Matrix.diagonal_apply_eq, mul_comm]
      rfl
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  erw [hmat, hdiag]

private theorem l02qfnm_map_subtype_commutator {G : Type*} [Group G] (H : Subgroup G) :
    (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem l02qfnm_commutatorElement_mul_center_left {X : Type*} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (a b : X) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hz_all : ∀ g : X, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hzinv_all : ∀ g : X, z⁻¹ * g = g * z⁻¹ :=
    fun g => (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) g).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  simp only [mul_assoc]
  rw [hz_all, hzinv_all]
  group

private theorem l02qfnm_commutatorElement_mul_center_right {X : Type*} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (a b : X) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hz_all : ∀ g : X, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have hzinv_all : ∀ g : X, z⁻¹ * g = g * z⁻¹ :=
    fun g => (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) g).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  simp only [mul_assoc]
  rw [hz_all, hzinv_all]
  group

private theorem l02qfnm_commutator_sup_center {X : Type*} [Group X] {J Z : Subgroup X}
    (hZ : Z ≤ Subgroup.center X) (hJJ : ⁅J, J⁆ = J) :
    ⁅J ⊔ Z, J ⊔ Z⁆ = J := by
  haveI hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    obtain ⟨j, hj, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨j', hj', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    rw [l02qfnm_commutatorElement_mul_center_left (hZ hz) j (j' * z'),
      l02qfnm_commutatorElement_mul_center_right (hZ hz') j j']
    exact hJJ ▸ Subgroup.commutator_mem_commutator hj hj'
  · calc J = ⁅J, J⁆ := hJJ.symm
      _ ≤ ⁅J ⊔ Z, J ⊔ Z⁆ :=
        Subgroup.commutator_mono (show J ≤ J ⊔ Z from le_sup_left)
          (show J ≤ J ⊔ Z from le_sup_left)

private theorem l02qfnm_sigma_invariant {N : ℕ} {K : Type} [Field K] [Finite K]
    (M : GL (Fin N) K) (σ : K ≃+* K)
    (hMσ : ∃ μ : K, (M : Matrix (Fin N) (Fin N) K).map σ = μ • (M : Matrix (Fin N) (Fin N) K))
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hgraph : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (fun x x' => ((x' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        ((x : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ) f)
    (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({M} : Set (GL (Fin N) K))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) K)
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)))
    (f' : MulAut ↥J₀)
    (hf' : ∀ j : ↥J₀, (f' j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = f j) :
    ∀ c ∈ C, Matrix.GeneralLinearGroup.map (σ : K →+* K) c ∈ C := by
  classical
  set σh : GL (Fin N) K →* GL (Fin N) K := Matrix.GeneralLinearGroup.map (σ : K →+* K) with hσh
  have hCC : ⁅C, C⁆ = C := by
    rw [← l02qfnm_map_subtype_commutator C, hC.2.2.1]
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hZ : LargeEvenScalars (Fin N) K ≤ Subgroup.center (GL (Fin N) K) :=
    le_of_eq (CFSG.Open.StatedAPI.statedScalars_eq_center (Fin N) K)
  have hsup : ⁅C ⊔ LargeEvenScalars (Fin N) K, C ⊔ LargeEvenScalars (Fin N) K⁆ = C :=
    l02qfnm_commutator_sup_center hZ hCC
  have hCσ_perf : ⁅C.map σh, C.map σh⁆ = C.map σh := by
    rw [← Subgroup.map_commutator, hCC]
  have hCσ_le : C.map σh ≤ C ⊔ LargeEvenScalars (Fin N) K := by
    rintro x ⟨c, hc, rfl⟩
    have hcSL : c ∈ LargeEvenSLGroup (Fin N) K := hCSL hc
    have hσSL : σh c ∈ LargeEvenSLGroup (Fin N) K := by
      simpa [hσh] using CFSG.LocalAnalysis.GLTheoremA.YS09Field.sl_map_mem σ c hcSL
    have hπcJ : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) ⟨c, hcSL⟩ ∈ J₀ := by
      rw [hJ₀]
      exact Subgroup.mem_map.mpr ⟨⟨c, hcSL⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
    have hfx : f (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) ⟨c, hcSL⟩) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) ⟨σh c, hσSL⟩ := by
      apply hgraph
      simpa [hσh] using CFSG.LocalAnalysis.GLTheoremA.YS09Field.coe_glMap σ.toRingHom c
    have hσJ : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) ⟨σh c, hσSL⟩ ∈ J₀ := by
      rw [← hfx, ← hf' ⟨_, hπcJ⟩]
      exact (f' ⟨_, hπcJ⟩).2
    obtain ⟨d, hd, hdπ⟩ := Subgroup.mem_map.mp (hJ₀ ▸ hσJ)
    have hdC : (d : GL (Fin N) K) ∈ C := Subgroup.mem_subgroupOf.mp hd
    have hker : d⁻¹ * ⟨σh c, hσSL⟩ ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdπ, inv_mul_cancel]
    have hz : ((d : GL (Fin N) K)⁻¹ * σh c) ∈ LargeEvenScalars (Fin N) K := by
      have hmem : d⁻¹ * ⟨σh c, hσSL⟩ ∈
          (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K) := by
        rw [← QuotientGroup.ker_mk'
          ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K))]
        exact MonoidHom.mem_ker.mp hker
      exact Subgroup.mem_subgroupOf.mp hmem
    have hdecomp : σh c = (d : GL (Fin N) K) * ((d : GL (Fin N) K)⁻¹ * σh c) := by group
    rw [hdecomp]
    exact (C ⊔ LargeEvenScalars (Fin N) K).mul_mem
      (Subgroup.mem_sup_left hdC) (Subgroup.mem_sup_right hz)
  have hCσC : C.map σh ≤ C := by
    calc C.map σh = ⁅C.map σh, C.map σh⁆ := hCσ_perf.symm
      _ ≤ ⁅C ⊔ LargeEvenScalars (Fin N) K, C ⊔ LargeEvenScalars (Fin N) K⁆ :=
        Subgroup.commutator_mono hCσ_le hCσ_le
      _ = C := hsup
  intro c hc
  exact hCσC ⟨c, hc, rfl⟩

private lemma l02qfnm_two_le_exponent {D : Type} [Field D] [Finite D] [CharP D 2]
    {k : ℕ} (hk : Nat.card D = 2 ^ k) (hk1 : 1 ≤ k) {τ : D ≃+* D} (hτ : τ ≠ 1) : 2 ≤ k := by
  classical
  by_contra h
  have hk_eq : k = 1 := by omega
  have hcard2 : Nat.card D = 2 := by rw [hk, hk_eq, pow_one]
  apply hτ
  haveI : Fintype D := Fintype.ofFinite D
  have h2 : Fintype.card D = 2 := by rwa [Nat.card_eq_fintype_card] at hcard2
  ext x
  have hx : x = 0 ∨ x = 1 := by
    have hcard : ({0, 1} : Finset D).card = Fintype.card D := by
      rw [h2]; simp [zero_ne_one]
    have huniv : ({0, 1} : Finset D) = Finset.univ := Finset.eq_univ_of_card _ hcard
    have : x ∈ ({0, 1} : Finset D) := by rw [huniv]; exact Finset.mem_univ x
    simpa using this
  rcases hx with rfl | rfl
  · exact map_zero τ
  · exact map_one τ

private lemma l02qfnm_exists_card_eq_two_pow (D : Type) [Field D] [Finite D] [CharP D 2] :
    ∃ k : ℕ, 1 ≤ k ∧ Nat.card D = 2 ^ k := by
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨k, -, hk⟩ := FiniteField.card D 2
  exact ⟨k, k.pos, by rw [Nat.card_eq_fintype_card, hk]⟩

private theorem l02qfnm_rawDatum_linear {m k : ℕ} {D : Type} [Field D] [Finite D]
    (hm : 1 ≤ m) (hcard : Nat.card D = 2 ^ k) (Q : LargeEvenRawCont)
    (hQ : Q (LargeEvenProj (LargeEvenSLGroup (Fin m) D))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) D)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) D)))) :
    LargeEvenRawDatum (⟨.A, m - 1, k⟩ : LargeEvenLabel) Q := by
  change LargeEvenRecipeLinear (m - 1 + 1) (2 ^ k) Q
  rw [show m - 1 + 1 = m from Nat.sub_add_cancel (by omega)]
  exact ⟨D, inferInstance, inferInstance, hcard, hQ⟩

theorem fniLin_oneMarking {N n p : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    {f h : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)))
    (hfo : orderOf f = p)
    (hh : h ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ)
    (hhp : h ^ p = 1) (hcomm : h * f = f * h)
    {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    (hJ₀ : CFSG.Open.IsComponentOf J₀
      (MonoidHom.eqLocus (h : LargeEvenProj (LargeEvenSLGroup (Fin N) K) →* _) (MonoidHom.id _)))
    (f' : MulAut ↥J₀) (hf' : ∀ j : ↥J₀, (f' j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = f j) :
    LargeEvenMarking ↥J₀ fun _ _ _ I _ θ =>
      ¬ ∃ φ ∈ Subgroup.closure I, LargeEvenInduces θ (fun j k : ↥J₀ => k = f' j) φ := by
  classical
  haveI hcharK : CharP K 2 := charP_two_of_card hK
  obtain ⟨M, hM⟩ := TableB.exists_eq_linConjAut hh
  obtain ⟨σ, hσgraph⟩ := hf
  have hf1 : f ≠ 1 := by
    intro hf1
    have h1 : orderOf f = 1 := by rw [hf1, orderOf_one]
    rw [hfo] at h1
    exact hp.ne_one h1
  have hσne : σ ≠ 1 := l02qfnm_sigma_ne_one hσgraph hf1
  have hMσ : ∃ μ : K, (M : Matrix (Fin N) (Fin N) K).map σ =
      μ • (M : Matrix (Fin N) (Fin N) K) := l02qfnm_sigma_smul hN hM hσgraph hcomm
  have hModd : Odd (orderOf M) :=
    l02qfnm_orderOf_odd hN hn hK (by rw [← hM]; exact hhp) hp hp2
  have hJ₀fix : CFSG.Open.IsComponentOf J₀
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) K M)) := by
    have heq : ggAutFixedSubgroup (TableB.linConjAut (Fin N) K M) =
        MonoidHom.eqLocus (h : LargeEvenProj (LargeEvenSLGroup (Fin N) K) →* _)
          (MonoidHom.id _) := by
      rw [← hM]; ext r; rfl
    rw [heq]; exact hJ₀
  obtain ⟨C, hC, hCSL, hJeq⟩ := q1TorLin_component_lift hN M J₀ hJ₀fix
  have hσC : ∀ c ∈ C, Matrix.GeneralLinearGroup.map (σ : K →+* K) c ∈ C :=
    l02qfnm_sigma_invariant M σ hMσ hσgraph C hC hCSL J₀ hJeq f' hf'
  obtain ⟨m, D, hDfield, hDfin, hDchar, ψ, B, τ, hm, hτ, hact⟩ :=
    fniLin_block hN M hModd σ hσne hMσ C hC hCSL hσC J₀ hJeq
  letI : Field D := hDfield
  letI : Finite D := hDfin
  letI : CharP D 2 := hDchar
  obtain ⟨k, hk1, hk⟩ := l02qfnm_exists_card_eq_two_pow D
  have hk2 : 2 ≤ k := l02qfnm_two_le_exponent hk hk1 hτ
  let θ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin m) D) :=
    ψ.trans (TypeA.recipeEquiv m D).symm
  refine ⟨hJ₀.2.2.1, ⟨⟨.A, m - 1, k⟩, ?hlab, ?hraw⟩⟩
  · refine ⟨hk1, ?_, ?_⟩
    · show 1 ≤ m - 1
      omega
    · intro _
      exact hk2
  · refine l02qfnm_rawDatum_linear (m := m) (k := k) (D := D) (by omega) hk _ ?_
    refine ⟨?hsimple, ?hnonab, ?hθP⟩
    · exact ((TypeA.recipeEquiv m D).trans ψ.symm).isSimpleGroup_congr.mpr hJ₀.2.2.2
    · haveI : Nontrivial (↥J₀ ⧸ Subgroup.center ↥J₀) := hJ₀.2.2.2.toNontrivial
      have hnab : ∃ a b : ↥J₀ ⧸ Subgroup.center ↥J₀, a * b ≠ b * a :=
        exists_mul_ne_mul_centerQuot_of_perfect hJ₀.2.2.1 inferInstance
      exact nonabelian_of_mulEquiv ((TypeA.recipeEquiv m D).trans ψ.symm).symm hnab
    · refine ⟨θ, ?hP⟩
      rintro ⟨φ, hφcl, hφind⟩
      have hrange : Subgroup.closure
          (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) D)) Set.univ) ≤
          (TableB.linConjAut (Fin m) D).range :=
        (Subgroup.closure_le (TableB.linConjAut (Fin m) D).range).mpr (fun ψ' hψ' => by
          obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut hψ'
          exact ⟨A, hA.symm⟩)
      obtain ⟨A, hA⟩ := hrange hφcl
      have hmemI : TableB.linConjAut (Fin m) D A ∈
          LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) D)) Set.univ := by
        refine ⟨A, Set.mem_univ _, ?_⟩
        intro x x' hxx'
        change TableB.linConjAut (Fin m) D A
          (x : LargeEvenProj (LargeEvenSLGroup (Fin m) D)) =
            (x' : LargeEvenProj (LargeEvenSLGroup (Fin m) D))
        rw [TableB.linConjAut_mk]
        congr 1
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        exact hxx'.symm
      obtain ⟨A', hA'⟩ := TypeA.congr_recipeEquiv_mem hmemI
      have hkey : ∀ x : LinearFlag.projectiveSL m D,
          LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ x) =
            LinearFlag.conjAut m D A' x := by
        intro x
        obtain ⟨j0, hj0⟩ := QuotientGroup.mk_surjective (ψ.symm x)
        have hxψ : ψ (QuotientGroup.mk j0) = x := by rw [hj0, MulEquiv.apply_symm_apply]
        obtain ⟨xgl, hxgl⟩ :=
          (QuotientGroup.mk'_surjective
            ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K)))
            (j0 : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
        let x'gl : LargeEvenSLGroup (Fin N) K :=
          ⟨Matrix.GeneralLinearGroup.map (σ : K →+* K) (xgl : GL (Fin N) K),
            CFSG.LocalAnalysis.GLTheoremA.YS09Field.sl_map_mem σ (xgl : GL (Fin N) K) xgl.2⟩
        have hrel : ((x'gl : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
            ((xgl : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map σ :=
          CFSG.LocalAnalysis.GLTheoremA.YS09Field.coe_glMap σ.toRingHom (xgl : GL (Fin N) K)
        have hfx : f (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xgl) =
            LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x'gl := hσgraph xgl x'gl hrel
        have hπxJ : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xgl ∈ J₀ := by
          rw [show LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xgl = (j0 : _) from hxgl]
          exact j0.2
        have hx'J : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x'gl ∈ J₀ := by
          rw [← hfx, ← hf' ⟨_, hπxJ⟩]
          exact (f' ⟨_, hπxJ⟩).2
        have hact' := hact xgl x'gl hπxJ hx'J hrel
        have e0 : (⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xgl, hπxJ⟩ : ↥J₀) = j0 :=
          Subtype.ext hxgl
        have e1 : (⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) x'gl, hx'J⟩ : ↥J₀) = f' j0 := by
          apply Subtype.ext
          show (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) x'gl =
            ((f' j0 : ↥J₀) : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
          rw [← hfx, hxgl]
          exact (hf' j0).symm
        have hψf : ψ (QuotientGroup.mk (f' j0)) =
            LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ (ψ (QuotientGroup.mk j0))) := by
          have h := hact'
          rw [e0, e1] at h
          exact h
        have hθj0 : θ (QuotientGroup.mk j0) = (TypeA.recipeEquiv m D).symm x := by
          rw [show θ = ψ.trans (TypeA.recipeEquiv m D).symm from rfl, MulEquiv.trans_apply, hxψ]
        have hθfj0 : θ (QuotientGroup.mk (f' j0)) = (TypeA.recipeEquiv m D).symm
            (LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ x)) := by
          rw [show θ = ψ.trans (TypeA.recipeEquiv m D).symm from rfl, MulEquiv.trans_apply,
            hψf, hxψ]
        have h1 : φ ((TypeA.recipeEquiv m D).symm x) =
            (TypeA.recipeEquiv m D).symm
              (LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ x)) := by
          have h := hφind j0 (f' j0) rfl
          rw [hθj0, hθfj0] at h
          exact h
        have h2x : LinearFlag.conjAut m D A' x =
            LinearFlag.conjAut m D B (LinearFlag.fieldAut m D τ x) := by
          have h := congrArg (TypeA.recipeEquiv m D) h1
          rw [MulEquiv.apply_symm_apply] at h
          have hφA : φ = TableB.linConjAut (Fin m) D A := hA.symm
          rw [hφA] at h
          have hcφ : (MulAut.congr (TypeA.recipeEquiv m D) (TableB.linConjAut (Fin m) D A)) x =
              LinearFlag.conjAut m D A' x := by rw [hA']
          rw [MulAut.congr_apply] at hcφ
          exact hcφ.symm.trans h
        exact h2x.symm
      exact fniLin_not_inner hm hτ B A' hkey

end CFSG.StandardType

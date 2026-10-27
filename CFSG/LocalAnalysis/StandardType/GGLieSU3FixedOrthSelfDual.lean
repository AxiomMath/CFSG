module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFactor
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentBlocks
import CFSG.RankThree.CentralLift.DefiningUnitary
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Reduction
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.StandardType

open CFSG Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.RankThree.CentralLift CFSG.AGLEmbedding.ToralCensus
open CFSG.ClassicalGroups.UnitaryFlag (gramSU mem_gramSU_iff_isometry gramForm_mulVec)

private lemma ggLieSU3Fixed_selfDualData {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {j : K[X]} [Fact (Irreducible j)]
    (hj : j ∈ primaryFactors y.toLinearMap) (hj1 : j ≠ X - 1)
    (hjs : j = reciprocalPolynomial j) :
    ∃ (ℓ f d : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot j))
      (B : primaryComponent y.toLinearMap j →ₛₗ[hU.bar] primaryComponent y.toLinearMap j
        →ₗ[AdjoinRoot j] AdjoinRoot j),
      j.natDegree = 2 * d ∧ Nat.card K = ℓ ^ f ∧ B.IsSymm ∧ B.SeparatingLeft ∧
        hU.bar (AdjoinRoot.root j) = (AdjoinRoot.root j)⁻¹ ∧
        (blockGL Q y j).range = sesqUnitaryGroup B := by
  have hirr := irreducible_of_mem_primaryFactors hj
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hy.exists_selfDual_hermitian (by decide) hj hj1 hjs
  have hd : finrank K (AdjoinRoot j) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot j) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot j) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent y.toLinearMap j →ₛₗ[hU.bar]
      primaryComponent y.toLinearMap j →ₗ[AdjoinRoot j] AdjoinRoot j :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hy.eq_zero_of_polar_selfdual hj hjs u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (blockGL Q y j).range = sesqUnitaryGroup B := by
    ext γ
    rw [hy.mem_range_blockGL_selfDual_iff hj hj1 hjs H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  exact ⟨ℓ, f, d, hU, B, hdeg, hq, hBsymm, hBl, by rw [hbar, hroot], hrange⟩

private lemma ggLieSU3Fixed_restrictionInRange {K : Type} [Field K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {j : K[X]}
    (hj : j ∈ primaryFactors y.toLinearMap) {x : V ≃ₗ[K] V}
    (hx : x ∈ isometryCentralizer Q y) :
    ∃ t : ↥(supportedBlock Q y j),
      blockGL Q y j t = centralizerGL y j ⟨x, (Subgroup.mem_inf.mp hx).2⟩ := by
  classical
  let xc : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
    ⟨x, (Subgroup.mem_inf.mp hx).2⟩
  refine ⟨⟨(RankThree.PartOne.KCOrthogonal.blockComponent hy xc j).1, hy.blockComponent_mem hx hj⟩, ?_⟩
  refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
  rw [coe_blockGL, coe_centralizerGL, blockComponent_apply_of_mem hy xc j hj v.2,
    if_pos (Or.inl rfl)]

private lemma ggLieSU3Fixed_toLin_diagGL_apply {L : Type} [Field L] {W : Type}
    [AddCommGroup W] [Module L W] {n : ℕ} (b : Module.Basis (Fin n) L W)
    (c : Fin n → Lˣ) (k : Fin n) :
    ((Matrix.GeneralLinearGroup.toLin' b (diagGL n L c) :
        LinearMap.GeneralLinearGroup L W) : Module.End L W) (b k) = (c k : L) • b k := by
  rw [toLin'_basis_apply]
  have hrepr : b.equivFun (b k) = Pi.single k (1 : L) := by
    rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]
  rw [hrepr, coe_diagGL]
  have hmv : (Matrix.diagonal (fun i => (c i : L))).mulVec (Pi.single k (1 : L)) =
      Pi.single k (c k : L) := by
    funext i
    rw [Matrix.mulVec_diagonal]
    by_cases h : i = k
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, mul_zero, Pi.single_eq_of_ne h]
  rw [hmv, Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply]

private lemma ggLieSU3Fixed_permMatrix_apply {L : Type} [Field L] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (σ.permMatrix L) a b = if σ a = b then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private lemma ggLieSU3Fixed_toLin_perm_apply {L : Type} [Field L] {W : Type}
    [AddCommGroup W] [Module L W] {n : ℕ} (b : Module.Basis (Fin n) L W)
    (σ : Equiv.Perm (Fin n)) (M : GL (Fin n) L)
    (hM : (M : Matrix (Fin n) (Fin n) L) = σ.permMatrix L) (k : Fin n) :
    ((Matrix.GeneralLinearGroup.toLin' b M :
        LinearMap.GeneralLinearGroup L W) : Module.End L W) (b k) = b (σ.symm k) := by
  rw [toLin'_basis_apply]
  have hrepr : b.equivFun (b k) = Pi.single k (1 : L) := by
    rw [Module.Basis.equivFun_apply, Module.Basis.repr_self, Finsupp.single_eq_pi_single]
  rw [hrepr, hM, Matrix.permMatrix_mulVec]
  have hmv : (Pi.single k (1 : L)) ∘ σ = Pi.single (σ.symm k) (1 : L) := by
    funext a
    rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
    by_cases h : σ a = k
    · have ha : a = σ.symm k := by rw [← h, Equiv.symm_apply_apply]
      rw [if_pos h, if_pos ha]
    · have ha : a ≠ σ.symm k := fun ha => h (by rw [ha, Equiv.apply_symm_apply])
      rw [if_neg h, if_neg ha]
  rw [hmv, Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply]

private lemma ggLieSU3Fixed_permGL_mem_gramSU {L : Type} [Field L]
    {ℓ f n : ℕ} (hU : UnitaryFieldData ℓ f L) (σ : Equiv.Perm (Fin n)) (M : GL (Fin n) L)
    (hM : (M : Matrix (Fin n) (Fin n) L) = σ.permMatrix L)
    (hdet : (M : Matrix (Fin n) (Fin n) L).det = 1) :
    M ∈ gramSU hU (1 : Matrix (Fin n) (Fin n) L) := by
  rw [mem_gramSU_iff_isometry]
  refine ⟨fun x y => ?_, hdet⟩
  rw [hM, gramForm_mulVec]
  have hmap : (σ.permMatrix L).map hU.bar = σ.permMatrix L := by
    ext a b
    rw [Matrix.map_apply, ggLieSU3Fixed_permMatrix_apply]
    split_ifs <;> simp
  rw [hmap, Matrix.transpose_permMatrix, Matrix.mul_one, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

private lemma ggLieSU3Fixed_twoDiag_apply_left {m : ℕ} {E : Type} [Field E] (i j : Fin m)
    (hij : i ≠ j) (μ : Eˣ) : twoDiag i j μ i = μ := by
  simp [twoDiag, hij]

theorem ggLieSU3Fixed_torus_selfDual {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {j : K[X]}
    (hj : j ∈ primaryFactors y.toLinearMap) (hj1 : j ≠ X - 1)
    (hjs : j = reciprocalPolynomial j) (hm : 2 ≤ primaryMultiplicity y.toLinearMap j)
    (E : Set (V ≃ₗ[K] V)) (hEy : E ⊆ isometryCentralizer Q y)
    (hEc : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ t ∈ specialBlock Q y j, (∀ x ∈ E, t * x = x * t) ∧
      ∃ u ∈ specialBlock Q y j, t * u ≠ u * t := by
  classical
  haveI hirr : Fact (Irreducible j) := ⟨irreducible_of_mem_primaryFactors hj⟩
  haveI hchar : CharP (AdjoinRoot j) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot j)).injective 2
  obtain ⟨ℓ, f, d, hU, B, hdeg, hq, hBs, hBl, hbar, hrange⟩ :=
    ggLieSU3Fixed_selfDualData hy hj hj1 hjs
  have hVfin : Finite V := Module.finite_of_finite K
  haveI hEquivFin : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      (fun a b h => LinearEquiv.ext (fun v => congrFun h v))
  have hωord : orderOf (AdjoinRoot.root j) = 3 := orderOf_root_eq_three hy hj hj1
  have hζ : IsPrimitiveRoot (AdjoinRoot.root j) 3 := hωord ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨ν, hνval, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three hωord
  have hνbar : hU.bar (ν : AdjoinRoot j) = ((ν : AdjoinRoot j))⁻¹ := by
    rw [hνval]; exact hbar
  have hpq : 3 ∣ ℓ ^ (f * d) + 1 := by
    have hω0 : AdjoinRoot.root j ≠ 0 := by
      intro h0
      have h1 := pow_orderOf_eq_one (AdjoinRoot.root j)
      rw [hωord, h0] at h1
      rw [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at h1
      exact zero_ne_one h1
    have h1 : (AdjoinRoot.root j) ^ (ℓ ^ (f * d) + 1) = 1 := by
      have hb : hU.bar (AdjoinRoot.root j) = (AdjoinRoot.root j) ^ (ℓ ^ (f * d)) :=
        hU.bar_apply _
      rw [hb] at hbar
      rw [pow_succ, hbar, inv_mul_cancel₀ hω0]
    simpa [hωord] using orderOf_dvd_of_pow_eq_one h1
  let gfun : ↥E → BlockGL y j :=
    fun i => centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩
  let g : ↥E → Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j) :=
    fun i => (gfun i : Module.End _ _)
  have hmemrange : ∀ i : ↥E, gfun i ∈ (blockGL Q y j).range := by
    intro i
    obtain ⟨t, ht⟩ := ggLieSU3Fixed_restrictionInRange hy hj (hEy i.2)
    exact ⟨t, ht⟩
  have hunit : ∀ i : ↥E, gfun i ∈ sesqUnitaryGroup B := fun i => by
    rw [← hrange]; exact hmemrange i
  have hiso : ∀ i : ↥E, ∀ v w, B (g i v) (g i w) = B v w := fun i =>
    mem_sesqUnitaryGroup.mp (hunit i)
  have hcomm : ∀ i i' : ↥E, Commute (g i) (g i') := by
    intro i i'
    have hsub : (⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ :
          ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V)))) *
        ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩ =
        ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩ *
          ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ := by
      apply Subtype.ext
      exact hEc i.1 i.2 i'.1 i'.2
    have hgroup : gfun i * gfun i' = gfun i' * gfun i := by
      show centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ *
          centralizerGL y j ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩ =
          centralizerGL y j ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩ *
            centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩
      calc centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ *
            centralizerGL y j ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩
          = centralizerGL y j (⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ *
              ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩) := (map_mul _ _ _).symm
        _ = centralizerGL y j (⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩ *
              ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩) := by rw [hsub]
        _ = centralizerGL y j ⟨i'.1, (Subgroup.mem_inf.mp (hEy i'.2)).2⟩ *
              centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ := map_mul _ _ _
    have h := congrArg (fun u : BlockGL y j =>
      (u : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))) hgroup
    show g i * g i' = g i' * g i
    simpa only [Units.val_mul] using h
  have hpow : ∀ i : ↥E, g i ^ 3 = 1 := by
    intro i
    have hsub : (⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ :
        ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V)))) ^ 3 = 1 :=
      Subtype.ext (hE3 i.1 i.2)
    have hgroup : gfun i ^ 3 = 1 := by
      show centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ ^ 3 = 1
      calc centralizerGL y j ⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ ^ 3
          = centralizerGL y j (⟨i.1, (Subgroup.mem_inf.mp (hEy i.2)).2⟩ ^ 3) :=
            (map_pow _ _ _).symm
        _ = 1 := by rw [hsub, map_one]
    have h := congrArg (fun u : BlockGL y j =>
      (u : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))) hgroup
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  obtain ⟨b, μ, hdiag, horth⟩ :=
    exists_orthonormal_common_eigenbasis hU hζ hpq hBs hBl g hcomm hpow hiso
  have hmfin : 2 ≤ Module.finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j) := hm
  let i₀ : Fin (Module.finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)) :=
    ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)) :=
    ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let Mγ : GL (Fin (Module.finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
      (AdjoinRoot j) := diagGL _ _ (twoDiag i₀ i₁ ν)
  let γ : LinearMap.GeneralLinearGroup (AdjoinRoot j) (primaryComponent y.toLinearMap j) :=
    Matrix.GeneralLinearGroup.toLin' b Mγ
  have hγSU : γ ∈ sesqSpecialUnitaryGroup B := by
    show Matrix.GeneralLinearGroup.toLin' b Mγ ∈ sesqSpecialUnitaryGroup B
    exact toLin'_diagGL_mem b horth i₀ i₁ hνbar
  have hγrange : γ ∈ (blockGL Q y j).range := hrange.symm ▸ sesqSpecialUnitaryGroup_le B hγSU
  obtain ⟨t, ht⟩ := hγrange
  have htF : t.1 ∈ specialBlock Q y j := by
    refine mem_specialBlock.mpr ⟨t.2, ?_⟩
    rw [blockDet_apply, ht]
    exact (mem_sesqSpecialUnitaryGroup.mp hγSU).2
  let Mσ : GL (Fin (Module.finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
      (AdjoinRoot j) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((Equiv.swap i₀ i₁).permMatrix (AdjoinRoot j)) (by
        rw [Matrix.det_permutation]
        exact (Units.map (Int.castRingHom (AdjoinRoot j)).toMonoidHom
          (Equiv.Perm.sign (Equiv.swap i₀ i₁))).ne_zero)
  have hMσ : (Mσ : Matrix (Fin (Module.finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))) (Fin (Module.finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))) (AdjoinRoot j)) =
      (Equiv.swap i₀ i₁).permMatrix (AdjoinRoot j) :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hdetσ : (Mσ : Matrix (Fin (Module.finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))) (Fin (Module.finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))) (AdjoinRoot j)).det = 1 := by
    rw [hMσ, Matrix.det_permutation, Equiv.Perm.sign_swap hi01]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    rw [CharTwo.neg_eq]
  let δ : LinearMap.GeneralLinearGroup (AdjoinRoot j) (primaryComponent y.toLinearMap j) :=
    Matrix.GeneralLinearGroup.toLin' b Mσ
  have hσgram : Mσ ∈ gramSU hU (1 : Matrix (Fin (Module.finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))) (Fin (Module.finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))) (AdjoinRoot j)) :=
    ggLieSU3Fixed_permGL_mem_gramSU hU (Equiv.swap i₀ i₁) Mσ hMσ hdetσ
  have hσSU : δ ∈ sesqSpecialUnitaryGroup B :=
    (toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU hU b (fun i j => by
      rw [horth, Matrix.one_apply]) Mσ).mpr hσgram
  have hσrange : δ ∈ (blockGL Q y j).range := hrange.symm ▸ sesqSpecialUnitaryGroup_le B hσSU
  obtain ⟨u, hu⟩ := hσrange
  have huF : u.1 ∈ specialBlock Q y j := by
    refine mem_specialBlock.mpr ⟨u.2, ?_⟩
    rw [blockDet_apply, hu]
    exact (mem_sesqSpecialUnitaryGroup.mp hσSU).2
  let Γ : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j) := γ
  let Δ : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j) := δ
  have hγapp : ∀ k, Γ (b k) = (twoDiag i₀ i₁ ν k : AdjoinRoot j) • b k := by
    intro k
    show ((Matrix.GeneralLinearGroup.toLin' b Mγ :
        LinearMap.GeneralLinearGroup (AdjoinRoot j) (primaryComponent y.toLinearMap j)) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b k) = _
    exact ggLieSU3Fixed_toLin_diagGL_apply b (twoDiag i₀ i₁ ν) k
  have hδapp : ∀ k, Δ (b k) = b (Equiv.swap i₀ i₁ k) := by
    intro k
    have h := ggLieSU3Fixed_toLin_perm_apply b (Equiv.swap i₀ i₁) Mσ hMσ k
    simpa [Equiv.swap_inv] using h
  refine ⟨t.1, htF, ?_, u.1, huF, ?_⟩
  ·
    intro x hx
    let xc : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
      ⟨x, (Subgroup.mem_inf.mp (hEy hx)).2⟩
    have hconj : x * t.1 * x⁻¹ ∈ supportedBlock Q y j :=
      conj_mem_supportedBlock (hEy hx) t.2
    let tc : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
      ⟨t.1, (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp t.2).1).2⟩
    let hc : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
      ⟨x * t.1 * x⁻¹, (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hconj).1).2⟩
    have hconjGL : blockGL Q y j ⟨x * t.1 * x⁻¹, hconj⟩ = centralizerGL y j xc * γ *
        (centralizerGL y j xc)⁻¹ := by
      show centralizerGL y j hc = centralizerGL y j xc * γ * (centralizerGL y j xc)⁻¹
      have hsub : hc = xc * tc * xc⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hsub, map_mul, map_mul, map_inv]
      have hct : centralizerGL y j tc = γ := by
        show blockGL Q y j t = γ
        exact ht
      rw [hct]
    have hcxcomm : centralizerGL y j xc * γ = γ * centralizerGL y j xc := by
      apply Units.ext
      show ((centralizerGL y j xc : BlockGL y j) : Module.End (AdjoinRoot j)
          (primaryComponent y.toLinearMap j)) * Γ =
        Γ * ((centralizerGL y j xc : BlockGL y j) : Module.End (AdjoinRoot j)
          (primaryComponent y.toLinearMap j))
      refine b.ext fun k => ?_
      calc (((centralizerGL y j xc : BlockGL y j) : Module.End (AdjoinRoot j)
              (primaryComponent y.toLinearMap j)) * Γ) (b k)
          = (centralizerGL y j xc : Module.End (AdjoinRoot j)
              (primaryComponent y.toLinearMap j)) ((twoDiag i₀ i₁ ν k : AdjoinRoot j) • b k) := by
            rw [Module.End.mul_apply, hγapp k]
        _ = (twoDiag i₀ i₁ ν k : AdjoinRoot j) •
              ((centralizerGL y j xc : BlockGL y j) : Module.End (AdjoinRoot j)
                (primaryComponent y.toLinearMap j)) (b k) := by rw [map_smul]
        _ = (twoDiag i₀ i₁ ν k : AdjoinRoot j) • (μ ⟨x, hx⟩ k • b k) := by
            rw [hdiag ⟨x, hx⟩ k]
        _ = (μ ⟨x, hx⟩ k * (twoDiag i₀ i₁ ν k : AdjoinRoot j)) • b k := by
            rw [smul_smul, mul_comm]
        _ = (μ ⟨x, hx⟩ k) • ((twoDiag i₀ i₁ ν k : AdjoinRoot j) • b k) := by
            rw [← smul_smul]
        _ = Γ ((μ ⟨x, hx⟩ k) • b k) := by rw [map_smul, hγapp k]
        _ = Γ (((centralizerGL y j xc : BlockGL y j) : Module.End (AdjoinRoot j)
                (primaryComponent y.toLinearMap j)) (b k)) := by rw [hdiag ⟨x, hx⟩ k]
        _ = (Γ * ((centralizerGL y j xc : BlockGL y j) : Module.End (AdjoinRoot j)
                (primaryComponent y.toLinearMap j))) (b k) := by rw [Module.End.mul_apply]
    have hconj_eq : blockGL Q y j ⟨x * t.1 * x⁻¹, hconj⟩ = γ := by
      rw [hconjGL, hcxcomm, mul_assoc, mul_inv_cancel, mul_one]
    have ht_eq : t = ⟨x * t.1 * x⁻¹, hconj⟩ :=
      hy.blockGL_injective hj (by rw [ht, hconj_eq])
    have hval : t.1 = x * t.1 * x⁻¹ := congrArg Subtype.val ht_eq
    have h := congrArg (fun w : V ≃ₗ[K] V => w * x) hval
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h
  ·
    intro htu
    have hTU : (t * u : ↥(supportedBlock Q y j)) = (u * t : ↥(supportedBlock Q y j)) :=
      Subtype.ext htu
    have hγδ : γ * δ = δ * γ := by
      have h := congrArg (fun z : ↥(supportedBlock Q y j) => blockGL Q y j z) hTU
      rwa [map_mul, map_mul, ht, hu] at h
    have hΓΔ : Γ * Δ = Δ * Γ := by
      have h := congrArg (fun z : LinearMap.GeneralLinearGroup (AdjoinRoot j)
        (primaryComponent y.toLinearMap j) =>
          (z : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))) hγδ
      simpa only [Units.val_mul] using h
    have hb0 : (Γ * Δ) (b i₀) = (Δ * Γ) (b i₀) := by rw [hΓΔ]
    have hlhs : (Γ * Δ) (b i₀) = ((ν : AdjoinRoot j))⁻¹ • b i₁ := by
      calc (Γ * Δ) (b i₀) = Γ (Δ (b i₀)) := rfl
        _ = Γ (b (Equiv.swap i₀ i₁ i₀)) := by rw [hδapp]
        _ = Γ (b i₁) := by rw [Equiv.swap_apply_left]
        _ = (twoDiag i₀ i₁ ν i₁ : AdjoinRoot j) • b i₁ := hγapp i₁
        _ = ((ν : AdjoinRoot j))⁻¹ • b i₁ := by
              rw [twoDiag_apply_right hi01, Units.val_inv_eq_inv_val]
    have hrhs : (Δ * Γ) (b i₀) = (ν : AdjoinRoot j) • b i₁ := by
      calc (Δ * Γ) (b i₀) = Δ (Γ (b i₀)) := rfl
        _ = Δ ((twoDiag i₀ i₁ ν i₀ : AdjoinRoot j) • b i₀) := by rw [hγapp]
        _ = (twoDiag i₀ i₁ ν i₀ : AdjoinRoot j) • Δ (b i₀) := by rw [map_smul]
        _ = (ν : AdjoinRoot j) • Δ (b i₀) := by
              rw [ggLieSU3Fixed_twoDiag_apply_left i₀ i₁ hi01]
        _ = (ν : AdjoinRoot j) • b i₁ := by rw [hδapp, Equiv.swap_apply_left]
    have hνinv : ((ν : AdjoinRoot j))⁻¹ = (ν : AdjoinRoot j) := by
      have h0 : (((ν : AdjoinRoot j))⁻¹ - (ν : AdjoinRoot j)) • b i₁ = 0 := by
        rw [sub_smul, ← hlhs, ← hrhs, hb0, sub_self]
      have hbne : b i₁ ≠ 0 := b.ne_zero i₁
      exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hbne)
    have hνinvu : ν⁻¹ = ν := by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val]
      exact hνinv
    have hν2 : ν ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [hνinvu.symm]
      rw [inv_mul_cancel]
    have hνone : ν = 1 := by
      have h := hν3
      simpa [pow_succ, hν2] using h
    exact hν1 hνone

end CFSG.StandardType

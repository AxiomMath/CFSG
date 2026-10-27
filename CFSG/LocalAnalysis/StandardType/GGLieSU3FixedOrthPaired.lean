module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
import CFSG.RankThree.PartOne.KC.CommonEigenbasis
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentBlocks
import CFSG.RankThree.CentralLift.DefiningUnitary
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Reduction
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.StandardType

open CFSG Polynomial Module CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.AGLEmbedding.ToralCensus

theorem ggLieSU3Fixed_torus_paired {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {y : V ≃ₗ[K] V} (hy : OddOrderIsometry Q 3 y) {j : K[X]}
    (hj : j ∈ primaryFactors y.toLinearMap) (hj1 : j ≠ X - 1)
    (hjp : j ≠ reciprocalPolynomial j) (hm : 2 ≤ primaryMultiplicity y.toLinearMap j)
    (E : Set (V ≃ₗ[K] V)) (hEy : E ⊆ isometryCentralizer Q y)
    (hEc : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ t ∈ specialBlock Q y j, (∀ x ∈ E, t * x = x * t) ∧
      ∃ u ∈ specialBlock Q y j, t * u ≠ u * t := by
  classical
  haveI : Fact (Irreducible j) := ⟨irreducible_of_mem_primaryFactors hj⟩
  haveI : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      (fun _ _ he => LinearEquiv.ext (congrFun he))
  haveI : Finite ↥E := Finite.of_injective (fun x : ↥E => (x : V ≃ₗ[K] V))
    (fun _ _ h => Subtype.ext h)
  have hω : orderOf (AdjoinRoot.root j) = 3 := by
    obtain ⟨h0, hord⟩ := hy.orderOf_root Nat.prime_three hj hj1
    rw [← hord, ← orderOf_units]
    rfl
  have hζ : IsPrimitiveRoot (AdjoinRoot.root j) 3 := IsPrimitiveRoot.iff_orderOf.mpr hω
  obtain ⟨ν, hνval, hν3, hν1⟩ := exists_unit_of_orderOf_eq_three hω
  have hν2 : ν ^ 2 ≠ 1 := by
    intro h2
    apply hν1
    calc ν = ν * ν ^ 2 := by rw [h2, mul_one]
      _ = ν ^ 3 := by group
      _ = 1 := hν3
  have hν_ne : ν⁻¹ ≠ ν := by
    intro h
    apply hν2
    have hh : ν * ν = 1 := by
      calc ν * ν = ν * ν⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel ν
    simpa [pow_two] using hh
  let cent (x : ↥E) : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) :=
    ⟨x.1, (Subgroup.mem_inf.mp (hEy x.2)).2⟩
  let Funit (x : ↥E) : BlockGL y j := centralizerGL y j (cent x)
  have hFcomm : ∀ x z : ↥E, Funit x * Funit z = Funit z * Funit x := by
    intro x z
    show centralizerGL y j (cent x) * centralizerGL y j (cent z) =
      centralizerGL y j (cent z) * centralizerGL y j (cent x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEc x.1 x.2 z.1 z.2)
  have hFpow : ∀ x : ↥E, Funit x ^ 3 = 1 := by
    intro x
    show centralizerGL y j (cent x) ^ 3 = 1
    rw [← map_pow, show cent x ^ 3 = 1 from Subtype.ext (hE3 x.1 x.2), map_one]
  let f (x : ↥E) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j) :=
    (Funit x : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))
  have hcomm : ∀ x z : ↥E, Commute (f x) (f z) := by
    intro x z
    show f x * f z = f z * f x
    rw [← Units.val_mul, ← Units.val_mul, hFcomm x z]
  have hpow : ∀ x : ↥E, f x ^ 3 = 1 := by
    intro x
    show (↑(Funit x) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, hFpow x, Units.val_one]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_pow_eq_one
    (p := 3) hζ f hcomm hpow
  have hm2 : 2 ≤ finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j) := by
    simpa using hm
  let i₀ : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)) := ⟨0, by omega⟩
  let i₁ : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)) := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hμne : ∀ (x : ↥E)
      (i : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))), μ x i ≠ 0 := by
    intro x i h0
    have h1 : (Funit x : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b i) = 0 := by
      rw [hb x i, h0, zero_smul]
    have h2 : (((Funit x)⁻¹ : BlockGL y j) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))
        ((Funit x : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b i)) = b i := by
      have hmul : (((Funit x)⁻¹ : BlockGL y j) :
          Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) *
          (Funit x : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have := congrArg (fun g : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j) =>
        g (b i)) hmul
      simpa only [Module.End.mul_apply, Module.End.one_apply] using this
    rw [h1, map_zero] at h2
    exact b.ne_zero i h2.symm
  let νx (x : ↥E)
      (i : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) : (AdjoinRoot j)ˣ :=
    Units.mk0 (μ x i) (hμne x i)
  have htoLin'_eq : ∀ M : GL (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
      (AdjoinRoot j),
      ((Matrix.GeneralLinearGroup.toLin' b M : BlockGL y j) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) =
      Matrix.toLin b b (M : Matrix (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
        (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j)) := by
    intro M
    ext v
    rw [Matrix.toLin_apply, CFSG.RankThree.CentralLift.toLin'_basis_apply,
      Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply]
  have hc_eq : ∀ x : ↥E, Funit x =
      Matrix.GeneralLinearGroup.toLin' b (diagGL (finrank (AdjoinRoot j)
        (primaryComponent y.toLinearMap j)) (AdjoinRoot j) (νx x)) := by
    intro x
    apply Units.ext
    refine Module.Basis.ext b (fun i => ?_)
    rw [hb x i]
    rw [htoLin'_eq (diagGL (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))
      (AdjoinRoot j) (νx x)), Matrix.toLin_self]
    simp only [coe_diagGL]
    rw [Fintype.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]; rfl
    · intro k hki
      rw [Matrix.diagonal_apply_ne (fun k => (νx x k : AdjoinRoot j)) hki, zero_smul]
  let Mγ : GL (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j) :=
    diagGL (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (AdjoinRoot j)
      (twoDiag i₀ i₁ ν)
  let γ : BlockGL y j := Matrix.GeneralLinearGroup.toLin' b Mγ
  have hγ_apply : ∀ i : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)),
      ((γ : BlockGL y j) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b i) =
      ((twoDiag i₀ i₁ ν i : AdjoinRoot j) • b i) := by
    intro i
    rw [show γ = Matrix.GeneralLinearGroup.toLin' b Mγ from rfl]
    rw [htoLin'_eq Mγ, Matrix.toLin_self]
    rw [show (Mγ : Matrix (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
        (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j)) =
        (diagGL (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (AdjoinRoot j)
          (twoDiag i₀ i₁ ν) : Matrix _ _ (AdjoinRoot j)) from rfl]
    simp only [coe_diagGL]
    rw [Fintype.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro k hki
      rw [Matrix.diagonal_apply_ne (fun k => (twoDiag i₀ i₁ ν k : AdjoinRoot j)) hki, zero_smul]
  have hγ0 : ((γ : BlockGL y j) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))
      (b i₀) = (ν : AdjoinRoot j) • b i₀ := by
    rw [hγ_apply i₀]
    congr 1
    simp [twoDiag, hi01]
  have hγ1 : ((γ : BlockGL y j) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))
      (b i₁) = ((ν⁻¹ : (AdjoinRoot j)ˣ) : AdjoinRoot j) • b i₁ := by
    rw [hγ_apply i₁]
    congr 1
    simp [twoDiag, hi01]
  have hγcomm : ∀ x : ↥E, (centralizerGL y j (cent x)) * γ = γ * (centralizerGL y j (cent x)) := by
    intro x
    apply Units.ext
    refine Module.Basis.ext b (fun i => ?_)
    simp only [Units.val_mul]
    rw [Module.End.mul_apply, Module.End.mul_apply]
    conv_lhs => rw [hγ_apply i, map_smul, hb x i, smul_smul]
    conv_rhs => rw [hb x i, map_smul, hγ_apply i, smul_smul]
    rw [mul_comm]
  let t : ↥(supportedBlock Q y j) := (pairedBlockEquiv hy hj hjp).symm γ
  have htγ : blockGL Q y j t = γ := by
    change (pairedBlockEquiv hy hj hjp) t = γ
    exact (pairedBlockEquiv hy hj hjp).apply_symm_apply γ
  have hdetγ : LinearMap.det ((γ : BlockGL y j) :
      Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) = 1 := by
    have h1 : LinearMap.det ((γ : BlockGL y j) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) =
        (Mγ : Matrix (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
          (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j)).det := by
      rw [show γ = Matrix.GeneralLinearGroup.toLin' b Mγ from rfl]
      exact CFSG.RankThree.CentralLift.det_toLin'_basis b Mγ
    rw [h1]
    exact det_diagGL_twoDiag i₀ i₁ ν
  have htF : t.1 ∈ specialBlock Q y j := by
    refine mem_specialBlock.mpr ⟨t.2, ?_⟩
    rw [blockDet_apply, htγ]
    exact hdetγ
  have ht_cent : ∀ x ∈ E, t.1 * x = x * t.1 := by
    intro x hxE
    have hxcent : x ∈ Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp (hEy hxE)).2
    have hmem : x * t.1 * x⁻¹ ∈ supportedBlock Q y j := conj_mem_supportedBlock (hEy hxE) t.2
    have hconj_eq : (⟨x * t.1 * x⁻¹, hmem⟩ : ↥(supportedBlock Q y j)) = t := by
      apply OddOrderIsometry.blockGL_injective hy hj
      have htcent : (⟨t.1, supportedBlock_le_centralizer j t.2⟩ :
          ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V)))) =
          Subgroup.inclusion (supportedBlock_le_centralizer j) t := rfl
      have hprod : blockGL Q y j ⟨x * t.1 * x⁻¹, hmem⟩ =
          (centralizerGL y j ⟨x, hxcent⟩) * (centralizerGL y j ⟨t.1,
            supportedBlock_le_centralizer j t.2⟩) * (centralizerGL y j ⟨x, hxcent⟩)⁻¹ := by
        show centralizerGL y j ⟨x * t.1 * x⁻¹, supportedBlock_le_centralizer j hmem⟩ =
            (centralizerGL y j ⟨x, hxcent⟩) * (centralizerGL y j ⟨t.1,
              supportedBlock_le_centralizer j t.2⟩) * (centralizerGL y j ⟨x, hxcent⟩)⁻¹
        rw [← map_inv, ← map_mul, ← map_mul]
        exact congrArg (centralizerGL y j) (Subtype.ext rfl)
      have hcL : centralizerGL y j ⟨x, hxcent⟩ = centralizerGL y j (cent ⟨x, hxE⟩) := rfl
      have hC : blockGL Q y j ⟨x * t.1 * x⁻¹, hmem⟩ = γ := by
        rw [hprod, htcent, show centralizerGL y j (Subgroup.inclusion
          (supportedBlock_le_centralizer j) t) = blockGL Q y j t from rfl, htγ]
        rw [hcL, hγcomm ⟨x, hxE⟩]
        rw [mul_assoc, mul_inv_cancel, mul_one]
      rw [hC, htγ]
    have : x * t.1 * x⁻¹ = t.1 := congrArg Subtype.val hconj_eq
    calc t.1 * x = (x * t.1 * x⁻¹) * x := by rw [this]
      _ = x * t.1 := by group
  let Mδ : GL (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero ((Equiv.swap i₀ i₁).permMatrix (AdjoinRoot j)) (by
      rw [Matrix.det_permutation]
      simpa using (Units.map (Int.castRingHom (AdjoinRoot j)).toMonoidHom
        (Equiv.Perm.sign (Equiv.swap i₀ i₁))).ne_zero)
  let δ : BlockGL y j := Matrix.GeneralLinearGroup.toLin' b Mδ
  have hperm_apply : ∀ (τ : Equiv.Perm (Fin (finrank (AdjoinRoot j)
      (primaryComponent y.toLinearMap j))))
      (i k : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))),
      (τ.permMatrix (AdjoinRoot j)) i k = if k = τ i then 1 else 0 := by
    intro τ i k
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    by_cases h : k = τ i
    · simp [h]
    · have h' : τ i ≠ k := fun hh => h hh.symm
      simp [h, h']
  have hδ_apply : ∀ i : Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)),
      ((δ : BlockGL y j) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b i) =
      b (Equiv.swap i₀ i₁ i) := by
    intro i
    rw [show δ = Matrix.GeneralLinearGroup.toLin' b Mδ from rfl]
    rw [htoLin'_eq Mδ, Matrix.toLin_self]
    rw [show (Mδ : Matrix (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
        (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j)) =
        (Equiv.swap i₀ i₁).permMatrix (AdjoinRoot j) from
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _]
    rw [Fintype.sum_eq_single (Equiv.swap i₀ i₁ i)]
    · rw [hperm_apply]
      simp
    · intro k hk
      rw [hperm_apply]
      have hki : i ≠ Equiv.swap i₀ i₁ k := by
        intro h
        exact hk (by rw [h, Equiv.swap_apply_self])
      simp [hki]
  have hδ0 : ((δ : BlockGL y j) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))
      (b i₀) = b i₁ := by
    rw [hδ_apply i₀, Equiv.swap_apply_left]
  have hδ1 : ((δ : BlockGL y j) : Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j))
      (b i₁) = b i₀ := by
    rw [hδ_apply i₁, Equiv.swap_apply_right]
  have hdetδ : LinearMap.det ((δ : BlockGL y j) :
      Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) = 1 := by
    haveI : CharP (AdjoinRoot j) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AdjoinRoot j)).injective 2
    have h1 : LinearMap.det ((δ : BlockGL y j) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) =
        (Mδ : Matrix (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
          (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j)).det := by
      rw [show δ = Matrix.GeneralLinearGroup.toLin' b Mδ from rfl]
      exact CFSG.RankThree.CentralLift.det_toLin'_basis b Mδ
    rw [h1]
    rw [show (Mδ : Matrix (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j)))
        (Fin (finrank (AdjoinRoot j) (primaryComponent y.toLinearMap j))) (AdjoinRoot j)) =
        (Equiv.swap i₀ i₁).permMatrix (AdjoinRoot j) from
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _]
    rw [Matrix.det_permutation, Equiv.Perm.sign_swap hi01]
    have h2 : (2 : AdjoinRoot j) = 0 := CharP.cast_eq_zero (AdjoinRoot j) 2
    have h2' : (1 : AdjoinRoot j) + 1 = 0 := by
      rw [show (1 : AdjoinRoot j) + 1 = 2 by norm_num, h2]
    have hneg : ((↑(-1 : ℤˣ) : ℤ) : AdjoinRoot j) = 1 := by
      rw [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      exact neg_eq_iff_add_eq_zero.mpr h2'
    exact hneg
  let uB : ↥(supportedBlock Q y j) := (pairedBlockEquiv hy hj hjp).symm δ
  have huBδ : blockGL Q y j uB = δ := by
    change (pairedBlockEquiv hy hj hjp) uB = δ
    exact (pairedBlockEquiv hy hj hjp).apply_symm_apply δ
  have huF : uB.1 ∈ specialBlock Q y j := by
    refine mem_specialBlock.mpr ⟨uB.2, ?_⟩
    rw [blockDet_apply, huBδ]
    exact hdetδ
  have htu_ne : t.1 * uB.1 ≠ uB.1 * t.1 := by
    intro h
    have hblock : γ * δ = δ * γ := by
      have e1 : (⟨t.1 * uB.1, mul_mem t.2 uB.2⟩ : ↥(supportedBlock Q y j)) = t * uB :=
        Subtype.ext rfl
      have e2 : (⟨uB.1 * t.1, mul_mem uB.2 t.2⟩ : ↥(supportedBlock Q y j)) = uB * t :=
        Subtype.ext rfl
      have h2 : (⟨t.1 * uB.1, mul_mem t.2 uB.2⟩ : ↥(supportedBlock Q y j)) =
          ⟨uB.1 * t.1, mul_mem uB.2 t.2⟩ := Subtype.ext h
      calc γ * δ = blockGL Q y j t * blockGL Q y j uB := by rw [htγ, huBδ]
        _ = blockGL Q y j (t * uB) := (map_mul (blockGL Q y j) t uB).symm
        _ = blockGL Q y j ⟨t.1 * uB.1, mul_mem t.2 uB.2⟩ := by rw [e1]
        _ = blockGL Q y j ⟨uB.1 * t.1, mul_mem uB.2 t.2⟩ := by rw [h2]
        _ = blockGL Q y j (uB * t) := by rw [e2]
        _ = blockGL Q y j uB * blockGL Q y j t := map_mul (blockGL Q y j) uB t
        _ = δ * γ := by rw [htγ, huBδ]
    have key : ((γ * δ : BlockGL y j) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b i₀) =
        ((δ * γ : BlockGL y j) :
        Module.End (AdjoinRoot j) (primaryComponent y.toLinearMap j)) (b i₀) := by rw [hblock]
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hδ0, hγ1, hγ0, map_smul, hδ0] at key
    exact hν_ne (Units.ext (smul_left_injective (AdjoinRoot j) (b.ne_zero i₁) key))
  exact ⟨t.1, htF, ht_cent, uB.1, huF, htu_ne⟩

end CFSG.StandardType

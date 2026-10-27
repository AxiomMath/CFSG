module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAD
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTenCommutant
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.GH74.KGroups.L27
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H Subgroup Polynomial
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Matrix Pointwise

private theorem s16h_e3_centralizer_le_scalars {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
          Set (MulAut (StdMod s16h_H5E3RkιA K))) ≤
      natImage (StatedScalars s16h_H5E3RkιA K) := by
  intro g hg
  have hΓ : HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) :=
    S18.hasScalarCommutant_statedOmegaMinus2 hirr
  let f : (s16h_H5E3RkιA → K) →+ (s16h_H5E3RkιA → K) :=
    AddMonoidHom.mk' (toAddMap g) (fun v w => toAddMap_add g v w)
  have hcomm : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v : s16h_H5E3RkιA → K,
      f ((γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v) =
        (γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ f v := by
    intro γ hγ v
    have hmem : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ ∈
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) := ⟨_, rfl⟩
    have hc : natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g =
        g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ :=
      (Subgroup.mem_centralizer_iff.mp hg) _ hmem
    change toAddMap g ((γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v) =
        (γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ toAddMap g v
    calc toAddMap g ((γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v)
        = toAddMap (g * natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩) v := by
          rw [toAddMap_mul, toAddMap_natAut]
      _ = toAddMap (natAut (StatedOmega (StatedQuadMinus 2 K b c)) ⟨γ, hγ⟩ * g) v := by
          rw [← hc]
      _ = (γ : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ toAddMap g v := by
          rw [toAddMap_mul, toAddMap_natAut]
  obtain ⟨μ, hμ⟩ := hΓ f hcomm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hsingle : (Pi.single (Sum.inl (0 : Fin 1)) (1 : K) : s16h_H5E3RkιA → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 1))
      simpa using this
    refine hsingle ((toAddMap_eq_zero_iff g).mp ?_)
    have h1 : f (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0 := by
      rw [hμ, h0, zero_smul]
    change toAddMap g (Pi.single (Sum.inl (0 : Fin 1)) (1 : K)) = 0
    exact h1
  let u : Kˣ := Units.mk0 μ hμ0
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar s16h_H5E3RkιA u, ⟨u, rfl⟩⟩, ?_⟩
  apply toAddMap_injective
  intro v
  rw [toAddMap_natAut]
  change ((Matrix.GeneralLinearGroup.scalar s16h_H5E3RkιA u :
      GL s16h_H5E3RkιA K) : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ v =
    toAddMap g v
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext x
  rw [Matrix.mulVec_diagonal]
  exact congrFun (hμ v).symm x

private theorem s16h_e3_card_statedScalars_natImage {K : Type} [Field K] [Finite K] :
    Nat.card (natImage (StatedScalars s16h_H5E3RkιA K)) = Nat.card K - 1 := by
  have hInj : Function.Injective (natAut (StatedScalars s16h_H5E3RkιA K)) :=
    matHom_injective.comp (Subgroup.subtype_injective (StatedScalars s16h_H5E3RkιA K))
  calc Nat.card (natImage (StatedScalars s16h_H5E3RkιA K))
      = Nat.card ↥(StatedScalars s16h_H5E3RkιA K) :=
        (Nat.card_congr (MonoidHom.ofInjective hInj).toEquiv).symm
    _ = Nat.card Kˣ :=
        (Nat.card_congr (MonoidHom.ofInjective
          (CFSG.LinearAlgebra.generalLinearGroup_scalar_injective
            (ι := s16h_H5E3RkιA) (R := K))).toEquiv).symm
    _ = Nat.card K - 1 := Nat.card_units K

private theorem s16h_e3_scalars_commute_natImage {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {mu g : MulAut (StdMod ι K)}
    (hmu : mu ∈ natImage (StatedScalars ι K)) (hg : g ∈ natImage Γ) : mu * g = g * mu := by
  obtain ⟨u, rfl⟩ := hmu
  obtain ⟨γ, rfl⟩ := hg
  obtain ⟨s, hs⟩ := u.2
  change matHom u.1 * matHom γ.1 = matHom γ.1 * matHom u.1
  rw [← map_mul, ← map_mul]
  congr 1
  rw [← hs]
  exact Matrix.GeneralLinearGroup.scalar_commute s γ.1

private theorem s16h_e3_normalizerMonoidHom_conj {G : Type} [Group G] (Ω : Subgroup G)
    (y : ↥Ω) :
    Ω.normalizerMonoidHom ⟨y.1, Subgroup.le_normalizer y.2⟩ = MulAut.conj y := by
  ext z
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
  rfl

private theorem s16h_e3_centralizer_eq_scalars {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.centralizer
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
          Set (MulAut (StdMod s16h_H5E3RkιA K))) =
      natImage (StatedScalars s16h_H5E3RkιA K) := by
  refine le_antisymm (s16h_e3_centralizer_le_scalars (K := K) hirr) ?_
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (s16h_e3_scalars_commute_natImage (Γ := StatedOmega (StatedQuadMinus 2 K b c))
    hg hh).symm

private theorem s16h_e3_outer_card_dvd {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(natImage (StatedOmega (StatedQuadMinus 2 K b c)))) ∣ 6 := by
  classical
  let Γ : Subgroup (GL s16h_H5E3RkιA K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) := natImage Γ
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : IsL2 ↥Ω (2 * 3) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  have hm : CFSG.Open.StatedClassicalModel ↥Ω .PSL 2 2 (2 * 3) :=
    hL2.statedClassicalModel (by decide)
  obtain ⟨⟨-, -, -⟩, L', hL'f, hL'fin, hL'card, ⟨ePSL⟩⟩ := hm
  letI : Field L' := hL'f
  letI : Finite L' := hL'fin
  let e' : ↥Ω ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) L' :=
    ePSL.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 L').symm
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
    Nat.prime_two L' hL'card).2 ↥Ω ⟨e'⟩
  have hdvd6 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥Ω) ∣ 6 := by
    have h6 : (2 * 3) * Nat.gcd 2 (2 ^ (2 * 3) - 1) = 6 := by norm_num
    rwa [h6] at hdvd
  exact hdvd6

private theorem s16h_e3_D_le_scalars_sup {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5E3RkιA K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 7 D) (hDcard : Nat.card ↥D = 7 ^ 2) :
    D ≤ natImage (StatedScalars s16h_H5E3RkιA K) ⊔
      natImage (StatedOmega (StatedQuadMinus 2 K b c)) := by
  classical
  let Γ : Subgroup (GL s16h_H5E3RkιA K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) := natImage Γ
  let C : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) :=
    natImage (StatedScalars s16h_H5E3RkιA K)
  have hCeq : Subgroup.centralizer (Ω : Set (MulAut (StdMod s16h_H5E3RkιA K))) = C :=
    s16h_e3_centralizer_eq_scalars (K := K) hirr
  have hOut : Nat.card (Outer ↥Ω) ∣ 6 := s16h_e3_outer_card_dvd (K := K) hK hirr
  let ψ : ↥D →* MulAut ↥Ω :=
    (Subgroup.normalizerMonoidHom Ω).comp (Subgroup.inclusion hDN)
  let φ : ↥D →* Outer ↥Ω :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner Ω)).comp ψ
  have hφ1 : φ = 1 := by
    refine MonoidHom.ext fun x => ?_
    have hx7 : (φ x) ^ 7 = 1 := by
      have hx : x ^ 7 = 1 := Subtype.ext (hDab.2 x.1 x.2)
      calc (φ x) ^ 7 = φ (x ^ 7) := (map_pow φ x 7).symm
        _ = φ 1 := by rw [hx]
        _ = 1 := map_one φ
    have hdvd7 : orderOf (φ x) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hx7
    have hdvdOut : orderOf (φ x) ∣ Nat.card (Outer ↥Ω) := orderOf_dvd_natCard (φ x)
    have hdvd : orderOf (φ x) ∣ Nat.gcd 7 6 := Nat.dvd_gcd hdvd7 (hdvdOut.trans hOut)
    have h1 : orderOf (φ x) = 1 := Nat.dvd_one.mp (by simpa using hdvd)
    exact orderOf_eq_one_iff.mp h1
  have htop : (⊤ : Subgroup ↥D).map (Subgroup.subtype D) = D := by
    ext g
    constructor
    · rintro ⟨x, -, rfl⟩
      exact x.2
    · intro hg
      exact ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩
  have hker_le : (φ.ker).map (Subgroup.subtype D) ≤ C ⊔ Ω := by
    rintro x ⟨d, hd, rfl⟩
    have hdmem : ψ d ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Ω :=
      (QuotientGroup.eq_one_iff (ψ d)).mp (MonoidHom.mem_ker.mp hd)
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hdmem
    obtain ⟨ω, hω⟩ := hdmem
    have hψω : ψ d = Ω.normalizerMonoidHom ⟨ω.1, Subgroup.le_normalizer ω.2⟩ := by
      rw [s16h_e3_normalizerMonoidHom_conj Ω ω, hω]
    have hmemC : (d : ↥D) * ω.1⁻¹ ∈ C := by
      have hker : Subgroup.inclusion hDN d *
          (⟨ω.1, Subgroup.le_normalizer ω.2⟩ :
            ↥(Subgroup.normalizer (Ω : Set (MulAut (StdMod s16h_H5E3RkιA K)))))⁻¹ ∈
          C.subgroupOf (Subgroup.normalizer (Ω : Set (MulAut (StdMod s16h_H5E3RkιA K)))) := by
        rw [← hCeq, ← Subgroup.normalizerMonoidHom_ker, MonoidHom.mem_ker, map_mul, map_inv]
        rw [show Ω.normalizerMonoidHom (Subgroup.inclusion hDN d) =
            Ω.normalizerMonoidHom ⟨ω.1, Subgroup.le_normalizer ω.2⟩ from hψω, mul_inv_cancel]
      simpa using Subgroup.mem_subgroupOf.mp hker
    simpa [mul_assoc] using Subgroup.mul_mem_sup hmemC ω.2
  rw [hφ1, MonoidHom.ker_one, htop] at hker_le
  exact hker_le

private theorem s16h_e3_X7_splits {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) : (X ^ 7 - 1 : K[X]).Splits := by
  haveI : Fintype ↥(⊤ : Subgroup Kˣ) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(⊤ : Subgroup Kˣ) = 7 := by
    rw [← Nat.card_eq_fintype_card, Subgroup.card_top, Nat.card_units, hK]
    norm_num
  have h := Lagrange.nodal_subgroup_eq_X_pow_card_sub_one (R := K) (⊤ : Subgroup Kˣ)
  rw [hcard] at h
  rw [← h]
  exact Splits.prod (fun μ _ => Splits.X_sub_C (μ : K))

private theorem s16h_e3_eq_one_of_forall_eigenvalue_eq_one {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ 3)
    {f : Module.End K (s16h_H5E3RkιA → K)} (hf7 : f ^ 7 = 1)
    (hall : ∀ μ : K, f.HasEigenvalue μ → μ = 1) : f = 1 := by
  classical
  have hint : IsIntegral K f :=
    Algebra.IsIntegral.isIntegral (A := Module.End K (s16h_H5E3RkιA → K)) f
  have hmonic : (minpoly K f).Monic :=
    minpoly.monic (A := K) (B := Module.End K (s16h_H5E3RkιA → K)) (x := f) hint
  have hdvd : minpoly K f ∣ (X : K[X]) ^ 7 - 1 := by
    refine minpoly.dvd (A := K) (B := Module.End K (s16h_H5E3RkιA → K)) (x := f) ?_
    simp [hf7]
  have hsep : (minpoly K f).Separable :=
    (Polynomial.separable_X_pow_sub_C (1 : K) (by
      intro h
      have hd : (2 : ℕ) ∣ 7 := (CharP.cast_eq_zero_iff K 2 7).mp h
      norm_num at hd) one_ne_zero).of_dvd hdvd
  have hmne : minpoly K f ≠ 0 :=
    minpoly.ne_zero (A := K) (B := Module.End K (s16h_H5E3RkιA → K)) (x := f) hint
  have hX7ne : (X ^ 7 - 1 : K[X]) ≠ 0 :=
    (monic_X_pow_sub_C (1 : K) (by norm_num : (7 : ℕ) ≠ 0)).ne_zero
  have hsplit : (minpoly K f).Splits :=
    Splits.of_dvd (s16h_e3_X7_splits (K := K) hK) hX7ne hdvd
  have hsplitM : ((minpoly K f).map (algebraMap K K)).Splits := by simpa using hsplit
  have hcard : Fintype.card ((minpoly K f).rootSet K) = (minpoly K f).natDegree :=
    Polynomial.card_rootSet_eq_natDegree (K := K) hsep hsplitM
  have hdeg : (minpoly K f).degree ≠ 0 :=
    (minpoly.degree_pos (A := K) (B := Module.End K (s16h_H5E3RkιA → K)) (x := f) hint).ne'
  obtain ⟨μ, hμroot⟩ := hsplit.exists_eval_eq_zero hdeg
  have hμ : f.HasEigenvalue μ := Module.End.hasEigenvalue_of_isRoot hμroot
  have hμ1 : μ = 1 := hall μ hμ
  have h1eig : f.HasEigenvalue 1 := by simpa [hμ1] using hμ
  have h1root : (1 : K) ∈ (minpoly K f).rootSet K := by
    rw [hmonic.mem_rootSet]
    have hroot : (minpoly K f).IsRoot 1 := Module.End.isRoot_of_hasEigenvalue h1eig
    simpa [Polynomial.IsRoot.def, Polynomial.aeval_def] using hroot
  have hsubset : (minpoly K f).rootSet K ⊆ ({1} : Set K) := by
    intro y hy
    rw [Set.mem_singleton_iff]
    have hyroot : (minpoly K f).IsRoot y := by
      rw [hmonic.mem_rootSet] at hy
      simpa [Polynomial.IsRoot.def, Polynomial.aeval_def] using hy
    exact hall y (Module.End.hasEigenvalue_of_isRoot hyroot)
  have hrootSet : (minpoly K f).rootSet K = {1} := by
    apply Set.Subset.antisymm hsubset
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h1root
  have hcard1 : Fintype.card ((minpoly K f).rootSet K) = 1 := by
    calc Fintype.card ((minpoly K f).rootSet K) = Fintype.card ({1} : Set K) :=
          Fintype.card_congr (Set.equivOfEq hrootSet)
      _ = 1 := by simp
  have hnat : (minpoly K f).natDegree = 1 := by omega
  obtain ⟨a, ha⟩ := (minpoly.natDegree_eq_one_iff).mp hnat
  obtain ⟨v, hv⟩ := h1eig.exists_hasEigenvector
  have hfv : f v = v := by simpa using hv.apply_eq_smul
  have hact : a • v = v := by
    rw [← Module.algebraMap_end_apply K K (s16h_H5E3RkιA → K) a v, ha, hfv]
  have h : a - 1 = 0 := by
    have hzero : (a - 1) • v = 0 := by
      rw [sub_smul, hact, one_smul, sub_self]
    exact (smul_eq_zero_iff_left hv.2).mp hzero
  have ha1 : a = 1 := sub_eq_zero.mp h
  rw [← ha, ha1, map_one]

private theorem s16h_e3_eigen_ne_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3)
    {f : Module.End K (s16h_H5E3RkιA → K)} (hf7 : f ^ 7 = 1) (hfne : f ≠ 1) :
    ∃ μ : K, μ ≠ 1 ∧ f.HasEigenvalue μ := by
  by_contra hcon
  have hall : ∀ μ : K, f.HasEigenvalue μ → μ = 1 := by
    intro μ hμ
    by_contra hne
    exact hcon ⟨μ, hne, hμ⟩
  exact hfne (s16h_e3_eq_one_of_forall_eigenvalue_eq_one (K := K) hK hf7 hall)

private theorem s16h_e3_pRank_omega_le_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Open.pRank 7 (natImage (StatedOmega (StatedQuadMinus 2 K b c))) ≤ 1 := by
  classical
  let Γ : Subgroup (GL s16h_H5E3RkιA K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) := natImage Γ
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : IsL2 ↥Ω (2 * 3) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  have hm : CFSG.Open.StatedClassicalModel ↥Ω .PSL 2 2 (2 * 3) :=
    hL2.statedClassicalModel (by decide)
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ω]
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even hm Nat.prime_seven (by norm_num)

private theorem s16h_e3_center_omega_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.center ↥(natImage (StatedOmega (StatedQuadMinus 2 K b c))) = ⊥ := by
  classical
  let Γ : Subgroup (GL s16h_H5E3RkιA K) := StatedOmega (StatedQuadMinus 2 K b c)
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) := natImage Γ
  have hInj : Function.Injective (natAut Γ) :=
    matHom_injective.comp (Subgroup.subtype_injective Γ)
  let eImg : ↥Γ ≃* ↥Ω := MonoidHom.ofInjective hInj
  have hL2 : IsL2 ↥Ω (2 * 3) :=
    uc22p22d_isL2_of_omegaMinus4 (by norm_num) hK b c hirr eImg.symm
  obtain ⟨hsimple, hnonab⟩ :=
    CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel hL2
  haveI : IsSimpleGroup ↥Ω := hsimple
  exact GL83.I713.center_eq_bot_of_simple hnonab

private theorem s16h_e3_inf_scalars_omega_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    natImage (StatedScalars s16h_H5E3RkιA K) ⊓
      natImage (StatedOmega (StatedQuadMinus 2 K b c)) = ⊥ := by
  classical
  let Ω : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) :=
    natImage (StatedOmega (StatedQuadMinus 2 K b c))
  let C : Subgroup (MulAut (StdMod s16h_H5E3RkιA K)) :=
    natImage (StatedScalars s16h_H5E3RkιA K)
  have hcenter : Subgroup.center ↥Ω = ⊥ := s16h_e3_center_omega_eq_bot (K := K) hK hirr
  have hCeq : Subgroup.centralizer (Ω : Set (MulAut (StdMod s16h_H5E3RkιA K))) = C :=
    s16h_e3_centralizer_eq_scalars (K := K) hirr
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxcenter : (⟨x, (Subgroup.mem_inf.mp hx).2⟩ : ↥Ω) ∈ Subgroup.center ↥Ω := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (by
      rw [hCeq]; exact (Subgroup.mem_inf.mp hx).1)) z.1 z.2)
  rw [hcenter] at hxcenter
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxcenter)

private theorem s16h_e3_scalars_normalize_omega {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    natImage (StatedOmega (StatedQuadMinus 2 K b c)) ≤
      Subgroup.normalizer (natImage (StatedScalars s16h_H5E3RkιA K) :
        Set (MulAut (StdMod s16h_H5E3RkιA K))) := by
  classical
  have hCeq := s16h_e3_centralizer_eq_scalars (K := K) (b := b) (c := c) hirr
  intro ω hω
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hCeq, Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have hz' : ω⁻¹ * z * ω ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
          Set (MulAut (StdMod s16h_H5E3RkιA K)))).inv_mem
            (Subgroup.le_normalizer hω)) z).mp hz
    have h1 := hx _ hz'
    calc z * (ω * x * ω⁻¹) = ω * (ω⁻¹ * z * ω * x) * ω⁻¹ := by group
      _ = ω * (x * (ω⁻¹ * z * ω)) * ω⁻¹ := by rw [h1]
      _ = (ω * x * ω⁻¹) * z := by group
  · intro hx
    rw [← hCeq, Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have hz' : ω * z * ω⁻¹ ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hω) z).mp hz
    have h1 := hx _ hz'
    calc z * x = ω⁻¹ * (ω * z * ω⁻¹ * (ω * x * ω⁻¹)) * ω := by group
      _ = ω⁻¹ * ((ω * x * ω⁻¹) * (ω * z * ω⁻¹)) * ω := by rw [h1]
      _ = x * z := by group

private theorem s16h_e3_quotient_sup_omega_card {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ((natImage (StatedScalars s16h_H5E3RkιA K) ⊔
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) : Subgroup
          (MulAut (StdMod s16h_H5E3RkιA K))) ⧸
      (natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
        (natImage (StatedScalars s16h_H5E3RkιA K) ⊔
          natImage (StatedOmega (StatedQuadMinus 2 K b c)))) = 7 := by
  classical
  have hCinfΩ := s16h_e3_inf_scalars_omega_eq_bot (K := K) (b := b) (c := c) hK hirr
  have hCcard : Nat.card ↥(natImage (StatedScalars s16h_H5E3RkιA K)) = 7 := by
    rw [s16h_e3_card_statedScalars_natImage (K := K), hK]
    norm_num
  have hCnorm : natImage (StatedScalars s16h_H5E3RkιA K) ≤
      Subgroup.normalizer (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
        Set (MulAut (StdMod s16h_H5E3RkιA K))) := by
    rw [← s16h_e3_centralizer_eq_scalars (K := K) hirr]
    exact Subgroup.centralizer_le_normalizer _
  haveI : ((natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
      (natImage (StatedScalars s16h_H5E3RkιA K))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hCnorm
  haveI : ((natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
      (natImage (StatedScalars s16h_H5E3RkιA K) ⊔
        natImage (StatedOmega (StatedQuadMinus 2 K b c)))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le hCnorm (fun _ hx => Subgroup.le_normalizer hx))
  have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient
    (natImage (StatedScalars s16h_H5E3RkιA K))
    (natImage (StatedOmega (StatedQuadMinus 2 K b c))) hCnorm
  have hbot : (natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
      (natImage (StatedScalars s16h_H5E3RkιA K)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine Subtype.ext (Subgroup.mem_bot.mp ?_)
    rw [← hCinfΩ]
    exact ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
  have h1 : Nat.card ((natImage (StatedScalars s16h_H5E3RkιA K)) ⧸
      (natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
        (natImage (StatedScalars s16h_H5E3RkιA K))) = 7 := by
    rw [hbot, Nat.card_congr (QuotientGroup.quotientBot
      (G := natImage (StatedScalars s16h_H5E3RkιA K))).toEquiv]
    exact hCcard
  rw [← Nat.card_congr hiso.toEquiv]
  exact h1

private theorem s16h_e3_pRank_quotient_sup_scalars_le_one {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ 3) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
        natImage (StatedScalars s16h_H5E3RkιA K))).Normal] :
    CFSG.Open.pRank 7 (⊤ : Subgroup ((natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
        natImage (StatedScalars s16h_H5E3RkιA K) : Subgroup
          (MulAut (StdMod s16h_H5E3RkιA K))) ⧸
      (natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
          natImage (StatedScalars s16h_H5E3RkιA K)))) ≤ 1 := by
  classical
  have hCinfΩ := s16h_e3_inf_scalars_omega_eq_bot (K := K) (b := b) (c := c) hK hirr
  have hΩnormC := s16h_e3_scalars_normalize_omega (K := K) (b := b) (c := c) hirr
  haveI : ((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c)))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hΩnormC
  have hbot : (natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    refine Subtype.ext (Subgroup.mem_bot.mp ?_)
    rw [← hCinfΩ]
    exact ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩
  have hN : ¬ 7 ∣ Nat.card ↥((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c)))) := by
    rw [hbot]; norm_num
  have h1 : CFSG.Open.pRank 7 (⊤ : Subgroup ((natImage (StatedOmega (StatedQuadMinus 2 K b c))) ⧸
      (natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
        (natImage (StatedOmega (StatedQuadMinus 2 K b c))))) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq
        ((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
          (natImage (StatedOmega (StatedQuadMinus 2 K b c)))) hN,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)))]
    exact s16h_e3_pRank_omega_le_one (K := K) hK hirr
  haveI : ((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
        natImage (StatedScalars s16h_H5E3RkιA K))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le hΩnormC (fun _ hx => Subgroup.le_normalizer hx))
  have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient
    (natImage (StatedOmega (StatedQuadMinus 2 K b c)))
    (natImage (StatedScalars s16h_H5E3RkιA K)) hΩnormC
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 7) (by norm_num) hiso
  rw [← h2]
  exact h1

private theorem s16h_e3_scalars_le_D {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5E3RkιA K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 7 D) (hDcard : Nat.card ↥D = 7 ^ 2) :
    natImage (StatedScalars s16h_H5E3RkιA K) ≤ D := by
  classical
  have hDCO : D ≤ natImage (StatedScalars s16h_H5E3RkιA K) ⊔
      natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
    s16h_e3_D_le_scalars_sup (K := K) hK hirr hDN hDab hDcard
  have hDCO' : D ≤ natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
      natImage (StatedScalars s16h_H5E3RkιA K) := by
    rw [sup_comm]; exact hDCO
  have hΩnormC := s16h_e3_scalars_normalize_omega (K := K) (b := b) (c := c) hirr
  haveI : ((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
        natImage (StatedScalars s16h_H5E3RkιA K))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le hΩnormC (fun _ hx => Subgroup.le_normalizer hx))
  have hprankQuot := s16h_e3_pRank_quotient_sup_scalars_le_one (K := K) hK hirr
  let π : ↥D →* ((natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
      natImage (StatedScalars s16h_H5E3RkιA K) : Subgroup
        (MulAut (StdMod s16h_H5E3RkιA K))) ⧸
      (natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
        (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
          natImage (StatedScalars s16h_H5E3RkιA K))) :=
    (QuotientGroup.mk' ((natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
      (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
        natImage (StatedScalars s16h_H5E3RkιA K)))).comp
      (Subgroup.inclusion hDCO')
  have hπab : IsElemAbelian 7 π.range := by
    have htop : IsElemAbelian 7 (⊤ : Subgroup ↥D) := by
      rw [← Subgroup.subgroupOf_self (H := D)]
      exact hDab.subgroupOf D
    have := IsElemAbelian.map htop π
    simpa [MonoidHom.range_eq_map] using this
  have hπle : Nat.card ↥π.range ≤ 7 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hπab.isPGroup
    have hk1 : k ≤ CFSG.Open.pRank 7 π.range :=
      CFSG.SectionRank.le_pRank (by norm_num) le_rfl hπab hk
    have hmono : CFSG.Open.pRank 7 π.range ≤
        CFSG.Open.pRank 7 (⊤ : Subgroup ((natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
          natImage (StatedScalars s16h_H5E3RkιA K) : Subgroup
            (MulAut (StdMod s16h_H5E3RkιA K))) ⧸
          (natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf
            (natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊔
              natImage (StatedScalars s16h_H5E3RkιA K)))) :=
      CFSG.SectionRank.pRank_mono (by norm_num) le_top
    calc Nat.card ↥π.range = 7 ^ k := hk
      _ ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num)
          (hk1.trans (hmono.trans hprankQuot))
      _ = 7 := pow_one 7
  have hcardmul : Nat.card ↥π.ker * Nat.card ↥π.range = Nat.card ↥D := by
    rw [← Subgroup.index_ker π, Subgroup.card_mul_index]
  have hker7 : 7 ≤ Nat.card ↥π.ker := by
    rw [hDcard] at hcardmul
    have h1 : Nat.card ↥π.ker * Nat.card ↥π.range ≤ Nat.card ↥π.ker * 7 :=
      Nat.mul_le_mul_left _ hπle
    omega
  have hker_eq : π.ker = (D ⊓ natImage (StatedScalars s16h_H5E3RkιA K)).subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨x.2, (QuotientGroup.eq_one_iff (Subgroup.inclusion hDCO' x)).mp hx⟩
    · rintro ⟨-, hxC⟩
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hDCO' x)).mpr hxC
  have hle : Nat.card ↥π.ker ≤ Nat.card ↥(D ⊓ natImage (StatedScalars s16h_H5E3RkιA K)) := by
    refine (Nat.card_le_card_of_injective (Subgroup.inclusion hker_eq.le)
      (Subgroup.inclusion_injective hker_eq.le)).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hinf7 : 7 ≤ Nat.card ↥(D ⊓ natImage (StatedScalars s16h_H5E3RkιA K)) :=
    hker7.trans hle
  have hCcard : Nat.card ↥(natImage (StatedScalars s16h_H5E3RkιA K)) = 7 := by
    rw [s16h_e3_card_statedScalars_natImage (K := K), hK]
    norm_num
  have hinfdvd : Nat.card ↥(D ⊓ natImage (StatedScalars s16h_H5E3RkιA K)) ∣ 7 := by
    rw [← hCcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hinfcard : Nat.card ↥(D ⊓ natImage (StatedScalars s16h_H5E3RkιA K)) = 7 := by
    rcases Nat.dvd_prime Nat.prime_seven |>.mp hinfdvd with h | h
    · omega
    · exact h
  have hCeq : D ⊓ natImage (StatedScalars s16h_H5E3RkιA K) =
      natImage (StatedScalars s16h_H5E3RkιA K) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hinfcard, hCcard])
  exact hCeq ▸ inf_le_left

private theorem s16h_e3_inf_omega_nontrivial {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5E3RkιA K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 7 D) (hDcard : Nat.card ↥D = 7 ^ 2) :
    ∃ y ∈ D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c)), y ≠ 1 := by
  classical
  have hDCO : D ≤ natImage (StatedScalars s16h_H5E3RkιA K) ⊔
      natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
    s16h_e3_D_le_scalars_sup (K := K) hK hirr hDN hDab hDcard
  have hQuotCard := s16h_e3_quotient_sup_omega_card (K := K) hK hirr
  have hCnorm : natImage (StatedScalars s16h_H5E3RkιA K) ≤
      Subgroup.normalizer (natImage (StatedOmega (StatedQuadMinus 2 K b c)) :
        Set (MulAut (StdMod s16h_H5E3RkιA K))) := by
    rw [← s16h_e3_centralizer_eq_scalars (K := K) hirr]
    exact Subgroup.centralizer_le_normalizer _
  haveI : ((natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
      (natImage (StatedScalars s16h_H5E3RkιA K) ⊔
        natImage (StatedOmega (StatedQuadMinus 2 K b c)))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le hCnorm (fun _ hx => Subgroup.le_normalizer hx))
  let π : ↥D →* ((natImage (StatedScalars s16h_H5E3RkιA K) ⊔
      natImage (StatedOmega (StatedQuadMinus 2 K b c)) : Subgroup
        (MulAut (StdMod s16h_H5E3RkιA K))) ⧸
      (natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
        (natImage (StatedScalars s16h_H5E3RkιA K) ⊔
          natImage (StatedOmega (StatedQuadMinus 2 K b c)))) :=
    (QuotientGroup.mk' ((natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
      (natImage (StatedScalars s16h_H5E3RkιA K) ⊔
        natImage (StatedOmega (StatedQuadMinus 2 K b c))))).comp
      (Subgroup.inclusion hDCO)
  have hker_eq : π.ker = (D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨x.2, (QuotientGroup.eq_one_iff (Subgroup.inclusion hDCO x)).mp hx⟩
    · rintro ⟨-, hxC⟩
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hDCO x)).mpr hxC
  have hπle : Nat.card ↥π.range ≤ 7 := by
    calc Nat.card ↥π.range ≤ Nat.card ((natImage (StatedScalars s16h_H5E3RkιA K) ⊔
          natImage (StatedOmega (StatedQuadMinus 2 K b c)) : Subgroup
            (MulAut (StdMod s16h_H5E3RkιA K))) ⧸
          (natImage (StatedOmega (StatedQuadMinus 2 K b c))).subgroupOf
            (natImage (StatedScalars s16h_H5E3RkιA K) ⊔
              natImage (StatedOmega (StatedQuadMinus 2 K b c)))) :=
          Nat.card_le_card_of_injective _ (Subgroup.subtype_injective π.range)
      _ = 7 := hQuotCard
  have hcardmul : Nat.card ↥π.ker * Nat.card ↥π.range = Nat.card ↥D := by
    rw [← Subgroup.index_ker π, Subgroup.card_mul_index]
  have hker7 : 7 ≤ Nat.card ↥π.ker := by
    rw [hDcard] at hcardmul
    have h1 : Nat.card ↥π.ker * Nat.card ↥π.range ≤ Nat.card ↥π.ker * 7 :=
      Nat.mul_le_mul_left _ hπle
    omega
  have hle : Nat.card ↥π.ker ≤
      Nat.card ↥(D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c))) := by
    refine (Nat.card_le_card_of_injective (Subgroup.inclusion hker_eq.le)
      (Subgroup.inclusion_injective hker_eq.le)).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hgt : 1 < Nat.card ↥(D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c))) :=
    lt_of_lt_of_le (by norm_num) (hker7.trans hle)
  haveI : Nontrivial ↥(D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c))) :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨y, hyne⟩ := exists_ne (1 : ↥(D ⊓ natImage (StatedOmega (StatedQuadMinus 2 K b c))))
  exact ⟨y.1, y.2, fun h => hyne (Subtype.ext h)⟩

theorem s16h_H5_omegaMinusFour_singular_common_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {D : Subgroup (MulAut (StdMod s16h_H5E3RkιA K))}
    (hDN : D ≤ natNorm (StatedOmega (StatedQuadMinus 2 K b c)))
    (hDab : IsElemAbelian 7 D) (hDcard : Nat.card ↥D = 7 ^ 2) :
    ∃ u : StdMod s16h_H5E3RkιA K, u ≠ 1 ∧
      StatedQuadMinus 2 K b c (Multiplicative.toAdd u) = 0 ∧
      ∃ d ∈ D, d ≠ 1 ∧ d u = u := by
  classical
  have hCD : natImage (StatedScalars s16h_H5E3RkιA K) ≤ D :=
    s16h_e3_scalars_le_D (K := K) hK hirr hDN hDab hDcard
  obtain ⟨y, hy, hyne⟩ := s16h_e3_inf_omega_nontrivial (K := K) hK hirr hDN hDab hDcard
  have hyD : y ∈ D := (Subgroup.mem_inf.mp hy).1
  have hyΩ : y ∈ natImage (StatedOmega (StatedQuadMinus 2 K b c)) := (Subgroup.mem_inf.mp hy).2
  have hy7 : y ^ 7 = 1 := hDab.2 y hyD
  obtain ⟨γ, hγ⟩ := hyΩ
  let f : Module.End K (s16h_H5E3RkιA → K) :=
    Matrix.toLin' ((γ : GL s16h_H5E3RkιA K) : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K)
  have hf_apply : ∀ v : s16h_H5E3RkιA → K, f v = toAddMap y v := by
    intro v
    rw [← hγ]
    simp only [f, Matrix.toLin'_apply, toAddMap_natAut]
  have hf7 : f ^ 7 = 1 := by
    apply LinearMap.ext
    intro v
    have hpow : ∀ k : ℕ, (f ^ k) v = toAddMap (y ^ k) v := by
      intro k
      induction k with
      | zero => simp [toAddMap_one]
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, hf_apply, ih, ← toAddMap_mul, pow_succ']
    rw [hpow 7, hy7, toAddMap_one, Module.End.one_apply]
  have hfne : f ≠ 1 := by
    intro h
    apply hyne
    apply toAddMap_injective
    intro v
    rw [toAddMap_one, ← hf_apply v, h, Module.End.one_apply]
  obtain ⟨μ, hμne, hμeig⟩ := s16h_e3_eigen_ne_one (K := K) hK hf7 hfne
  obtain ⟨u, hu⟩ := hμeig.exists_hasEigenvector
  have hfu : f u = μ • u := hu.apply_eq_smul
  have hu0 : u ≠ 0 := hu.2
  have hμ0 : μ ≠ 0 := by
    have hμ7 : μ ^ 7 = 1 := by
      have h := hu.pow_apply 7
      rw [hf7, Module.End.one_apply] at h
      have h2 : (μ ^ 7 - 1) • u = 0 := by
        rw [sub_smul, one_smul, ← h, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero_iff_left hu0).mp h2)
    intro h0
    rw [h0, zero_pow (by norm_num : 7 ≠ 0)] at hμ7
    exact zero_ne_one hμ7
  have hQy : StatedQuadMinus 2 K b c (toAddMap y u) = StatedQuadMinus 2 K b c u := by
    have hmem : (γ : GL s16h_H5E3RkιA K) ∈
        CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c) :=
      (CFSG.GroupTheory.WeirSylow.statedOmega_le_isometryCore
        (StatedQuadMinus 2 K b c)) γ.2
    have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore
      (Q₀ := StatedQuadMinus 2 K b c) hmem u
    simpa [← hγ, toAddMap_natAut] using h
  have hQsmul : StatedQuadMinus 2 K b c (μ • u) = μ ^ 2 * StatedQuadMinus 2 K b c u := by
    have hQ : StatedQuadMinus 2 K b c = ⇑(CFSG.LieType.Universal.Spin.quadMinus 2 K b c) :=
      (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c).symm
    rw [hQ, QuadraticMap.map_smul]
    simp [smul_eq_mul, pow_two]
  have hQu : StatedQuadMinus 2 K b c u = 0 := by
    have h1 : StatedQuadMinus 2 K b c (toAddMap y u) = StatedQuadMinus 2 K b c u := hQy
    rw [← hf_apply u, hfu, hQsmul] at h1
    have h2 : (μ ^ 2 - 1) * StatedQuadMinus 2 K b c u = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    have hμ2 : μ ^ 2 - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero, pow_two] at h
      rcases mul_self_eq_one_iff.mp h with h1 | h1
      · exact hμne h1
      · rw [CharTwo.neg_eq] at h1
        exact hμne h1
    exact (mul_eq_zero.mp h2).resolve_left hμ2
  let uμ : Kˣ := Units.mk0 μ hμ0
  let s' : GL s16h_H5E3RkιA K := Matrix.GeneralLinearGroup.scalar s16h_H5E3RkιA uμ⁻¹
  have hs'C : matAut s' ∈ natImage (StatedScalars s16h_H5E3RkιA K) :=
    ⟨⟨s', ⟨uμ⁻¹, rfl⟩⟩, rfl⟩
  have hs'D : matAut s' ∈ D := hCD hs'C
  have hs'u : ((s' : GL s16h_H5E3RkιA K) : Matrix s16h_H5E3RkιA s16h_H5E3RkιA K) *ᵥ u =
      μ⁻¹ • u := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    simp only [uμ, Units.val_inv_eq_inv_val, Units.val_mk0]
  refine ⟨Multiplicative.ofAdd u, ?_, ?_, y * matAut s', D.mul_mem hyD hs'D, ?_, ?_⟩
  · intro h
    exact hu0 (by simpa using congrArg Multiplicative.toAdd h)
  · simpa using hQu
  · intro hd
    have hyC : y ∈ natImage (StatedScalars s16h_H5E3RkιA K) := by
      have hyinv : y = (matAut s')⁻¹ := by
        calc y = y * matAut s' * (matAut s')⁻¹ := by group
          _ = 1 * (matAut s')⁻¹ := by rw [hd]
          _ = (matAut s')⁻¹ := one_mul _
      rw [hyinv]
      exact (natImage (StatedScalars s16h_H5E3RkιA K)).inv_mem hs'C
    have hmem : y ∈ natImage (StatedScalars s16h_H5E3RkιA K) ⊓
        natImage (StatedOmega (StatedQuadMinus 2 K b c)) :=
      ⟨hyC, (Subgroup.mem_inf.mp hy).2⟩
    rw [s16h_e3_inf_scalars_omega_eq_bot (K := K) hK hirr] at hmem
    exact hyne (Subgroup.mem_bot.mp hmem)
  · apply Multiplicative.toAdd.injective
    show toAddMap (y * matAut s') u = u
    rw [toAddMap_mul, toAddMap_matAut, hs'u, ← hf_apply]
    rw [map_smul, hfu, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.PhanDn CFSG.Timmesfeld.ClassicalOrders
open CFSG.LieType.BorelTits Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)

private theorem oaB_eq_zero_or_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ∀ a : F, a = 0 ∨ a = 1 := by
  classical
  intro a
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 := by rwa [Nat.card_eq_fintype_card] at hF
  have huniv : (Finset.univ : Finset F) = {0, 1} := Finset.univ_of_card_le_two (by omega)
  have ha : a ∈ ({0, 1} : Finset F) := by rw [← huniv]; exact Finset.mem_univ a
  simpa using ha

private theorem oaB_zeta_cube {K : Type} [Field K] {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ζ ^ 3 = 1 := by
  have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by rw [hζ, mul_zero]
  have h' : ζ ^ 3 - 1 = 0 := by linear_combination h
  exact sub_eq_zero.mp h'

private theorem oaB_cube_root_mem {K : Type} [Field K] {ζ c : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hc : c ^ 3 = 1) : c = 1 ∨ c = ζ ∨ c = ζ ^ 2 := by
  have h1 : (c - 1) * (c ^ 2 + c + 1) = 0 := by
    have h : c ^ 3 - 1 = 0 := by linear_combination hc
    linear_combination h
  rcases mul_eq_zero.1 h1 with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · have h2 : (c - ζ) * (c - ζ ^ 2) = 0 := by
      linear_combination h + (ζ - 1 - c) * hζ
    rcases mul_eq_zero.1 h2 with h' | h'
    · exact Or.inr (Or.inl (sub_eq_zero.1 h'))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h'))

private theorem oaB_exists_zeta_pow {K : Type} [Field K] {ζ c : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hc : c ^ 3 = 1) : ∃ n : ℕ, n < 3 ∧ c = ζ ^ n := by
  have hζ3 := oaB_zeta_cube hζ
  rcases oaB_cube_root_mem hζ hc with h | h | h
  · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
  · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  · exact ⟨2, by norm_num, h⟩

theorem exists_normHyp_isometry_of_normFrame {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {A : Subgroup ↥(orthDerived Q)} {k : ℕ} {M : Type} [Field M] [Finite M] [Algebra F M]
    {τ : M ≃+* M} {U : Type} [AddCommGroup U] [Module F U] (Φ : ((Fin k → M) × U) ≃ₗ[F] V)
    (hM : Nat.card M = 4) (hτ : ∀ y, τ y = y ^ 2) (hU : Module.finrank F U = 2)
    (hN : ∀ d w, algebraMap F M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap F M (Q (Φ (0, w))))
    (hdiag : ∀ e ∈ A, ∃ a : Fin k → M, (∀ i, a i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => a i * d i, w))
    (hfull : ∀ a : Fin k → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ A,
      ∀ d w, (e : V ≃ₗ[F] V) (Φ (d, w)) = Φ (fun i => a i * d i, w))
    {e f : U} (he : Q (Φ (0, e)) = 0) (hf : Q (Φ (0, f)) = 0)
    (hef : QuadraticMap.polarBilin Q (Φ (0, e)) (Φ (0, f)) = 1)
    {K : Type} [Field K] [Algebra F K] [Finite K] [CharP K 2]
    (E : QuadExt F K (unitaryInvolution K 2 1)) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ∃ Θ : ((F × F) × (Fin k → K)) ≃ₗ[F] V, (∀ v, Q (Θ v) = normHypForm E k v) ∧
      (∀ a ∈ A, ∃ t : Fin k → Multiplicative (ZMod 3), ∀ v,
        (a : V ≃ₗ[F] V) (Θ v) = Θ (v.1, fun i => ζ ^ (toAdd (t i)).val * v.2 i)) ∧
      ∀ t : Fin k → Multiplicative (ZMod 3), ∃ a ∈ A, ∀ v,
        (a : V ≃ₗ[F] V) (Θ v) = Θ (v.1, fun i => ζ ^ (toAdd (t i)).val * v.2 i) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have : Fintype M := Fintype.ofFinite M
  have hK4 : Nat.card K = 4 := by
    have : Module.Finite F K := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hF, E.finrank_eq]
    norm_num
  have hone : ∀ a : F, a = 0 ∨ a = 1 := oaB_eq_zero_or_one hF
  have hcardKM : Fintype.card K = Fintype.card M := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK4, hM]
  let ι : K ≃+* M := FiniteField.ringEquivOfCardEq hcardKM
  have hcompat : ∀ c : F, ι (algebraMap F K c) = algebraMap F M c := by
    intro c
    rcases hone c with rfl | rfl <;> simp
  let ιl : K ≃ₗ[F] M := (AlgEquiv.ofRingEquiv (f := ι) hcompat).toLinearEquiv
  have hΦadd : ∀ w₁ w₂ : U, Φ (0, w₁ + w₂) = Φ (0, w₁) + Φ (0, w₂) := by
    intro w₁ w₂
    simpa using Φ.map_add (0, w₁) (0, w₂)
  have hΦsmul : ∀ (c : F) (w : U), Φ (0, c • w) = c • Φ (0, w) := by
    intro c w
    simpa using Φ.map_smul c (0, w)
  have hEF : QuadraticMap.polar Q (Φ (0, e)) (Φ (0, f)) = 1 := by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact hef
  have hkey : ∀ a b : F, a • e + b • f = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have hlin : Φ (0, a • e + b • f) = a • Φ (0, e) + b • Φ (0, f) := by
      rw [hΦadd, hΦsmul, hΦsmul]
    have hE2 : a • Φ (0, e) + b • Φ (0, f) = 0 := by
      rw [← hlin, h]
      simp
    rcases hone a with rfl | rfl <;> rcases hone b with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      have hf0 : Φ (0, f) = 0 := by simpa using hE2
      rw [hf0] at hef
      simp at hef
    · exfalso
      have he0 : Φ (0, e) = 0 := by simpa using hE2
      rw [he0] at hef
      simp at hef
    · exfalso
      have hsum : Φ (0, e) + Φ (0, f) = 0 := by simpa using hE2
      have hQ : Q (Φ (0, e) + Φ (0, f)) = 0 := by rw [hsum, QuadraticMap.map_zero]
      rw [QuadraticMap.map_add Q (Φ (0, e)) (Φ (0, f)), he, hf, hEF] at hQ
      norm_num at hQ
  let φ : (F × F) →ₗ[F] U :=
    (LinearMap.toSpanSingleton F U e).comp (LinearMap.fst F F F) +
      (LinearMap.toSpanSingleton F U f).comp (LinearMap.snd F F F)
  have hφ_apply : ∀ a b : F, φ (a, b) = a • e + b • f := by
    intro a b
    simp [φ]
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have h0 : φ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    have hp : p - q = 0 := by
      obtain ⟨a, b, hab⟩ : ∃ a b : F, p - q = (a, b) := ⟨_, _, rfl⟩
      have h0' : φ (a, b) = 0 := by rwa [hab] at h0
      have h : a • e + b • f = 0 := by rw [hφ_apply] at h0'; exact h0'
      obtain ⟨ha, hb⟩ := hkey a b h
      rw [hab]
      simp [ha, hb]
    exact sub_eq_zero.mp hp
  have : FiniteDimensional F U := FiniteDimensional.of_finrank_pos (by rw [hU]; norm_num)
  let P : (F × F) ≃ₗ[F] U :=
    LinearMap.linearEquivOfInjective φ hφ_inj
      (by rw [hU, Module.finrank_prod, Module.finrank_self])
  have hP_apply : ∀ a b : F, P (a, b) = a • e + b • f := fun a b => hφ_apply a b
  let π : (Fin k → K) ≃ₗ[F] (Fin k → M) := LinearEquiv.piCongrRight (fun _ : Fin k => ιl)
  let Θ : ((F × F) × (Fin k → K)) ≃ₗ[F] V :=
    (LinearEquiv.prodComm F (F × F) (Fin k → K)).trans
      ((LinearEquiv.prodCongr π P).trans Φ)
  have hΘ : ∀ v : (F × F) × (Fin k → K),
      Θ v = Φ (fun i => ι (v.2 i), P v.1) := by
    intro v
    simp only [Θ, π, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
      LinearEquiv.prodCongr_apply]
    rfl
  refine ⟨Θ, ?_, ?_, ?_⟩
  ·
    intro v
    obtain ⟨⟨p, q⟩, x⟩ := v
    have hquad : ∀ a b : F, Q (Φ (0, a • e + b • f)) = a * b := by
      intro a b
      rcases hone a with rfl | rfl <;> rcases hone b with rfl | rfl
      · have h0 : Φ (0, (0 : F) • e + (0 : F) • f) = 0 := by
          rw [zero_smul, zero_smul, add_zero]
          exact LinearEquiv.map_zero Φ
        rw [h0, QuadraticMap.map_zero, zero_mul]
      · rw [zero_smul, one_smul, zero_add, hf, zero_mul]
      · rw [one_smul, zero_smul, add_zero, he, mul_zero]
      · have hlin : Φ (0, (1 : F) • e + (1 : F) • f) = Φ (0, e) + Φ (0, f) := by
          rw [one_smul, one_smul, hΦadd]
        rw [hlin, QuadraticMap.map_add Q (Φ (0, e)) (Φ (0, f)), he, hf, hEF]
        norm_num
    have hQpq : Q (Φ (0, P (p, q))) = p * q := by
      rw [hP_apply]
      exact hquad p q
    have hsum : (∑ i, τ (ι (x i)) * ι (x i)) = algebraMap F M (Qn E k x) := by
      have hterm : ∀ i, τ (ι (x i)) * ι (x i) = ι (x i * unitaryInvolution K 2 1 (x i)) := by
        intro i
        rw [hτ, ← map_pow, ← map_mul]
        congr 1
        rw [unitaryInvolution_apply, pow_one]
        exact mul_comm _ _
      simp only [hterm]
      rw [← map_sum, ← algebraMap_Qn E k x]
      exact hcompat (Qn E k x)
    apply (algebraMap F M).injective
    have hL : algebraMap F M (Q (Θ ((p, q), x))) =
        algebraMap F M (Qn E k x) + algebraMap F M (p * q) := by
      rw [hΘ, hN (fun i => ι (x i)) (P (p, q)), hsum, hQpq]
    have hR : algebraMap F M (normHypForm E k ((p, q), x)) =
        algebraMap F M (p * q) + algebraMap F M (Qn E k x) := by
      rw [show normHypForm E k ((p, q), x) = p * q + Qn E k x from
        hypSum_apply (Qn E k) ((p, q), x)]
      rw [map_add]
    rw [hL, hR, add_comm]
  ·
    intro g hg
    obtain ⟨a, ha3, hact⟩ := hdiag g hg
    have hex : ∀ i, ∃ n : ℕ, n < 3 ∧ a i = ι (ζ ^ n) := by
      intro i
      have hb3 : (ι.symm (a i)) ^ 3 = 1 := by
        rw [← map_pow, ha3 i, map_one]
      obtain ⟨n, hn, hc⟩ := oaB_exists_zeta_pow hζ hb3
      exact ⟨n, hn, by rw [← hc, ι.apply_symm_apply]⟩
    choose n hn using hex
    let t : Fin k → Multiplicative (ZMod 3) := fun i => ofAdd ((n i : ℕ) : ZMod 3)
    refine ⟨t, ?_⟩
    have ht : ∀ i, (toAdd (t i)).val = n i := fun i => ZMod.val_cast_of_lt (hn i).1
    intro v
    obtain ⟨⟨p, q⟩, x⟩ := v
    have h1 : Θ ((p, q), x) = Φ (fun i => ι (x i), P (p, q)) := hΘ _
    have h2 : Θ ((p, q), fun i => ζ ^ (toAdd (t i)).val * x i) =
        Φ (fun i => ι (ζ ^ (toAdd (t i)).val * x i), P (p, q)) := hΘ _
    have hfun : (fun i => a i * ι (x i)) =
        fun i => ι (ζ ^ (toAdd (t i)).val * x i) := by
      funext i
      rw [ht i, (hn i).2, ← map_mul]
    rw [h1, h2, hact (fun i => ι (x i)) (P (p, q)), hfun]
  ·
    intro t
    let a : Fin k → M := fun i => ι (ζ ^ (toAdd (t i)).val)
    have ha3 : ∀ i, a i ^ 3 = 1 := by
      intro i
      have hζ3 : ζ ^ 3 = 1 := oaB_zeta_cube hζ
      have hpow : (ζ ^ (toAdd (t i)).val) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
      rw [show a i = ι (ζ ^ (toAdd (t i)).val) from rfl, ← map_pow, hpow, map_one]
    obtain ⟨g, hg, hact⟩ := hfull a ha3
    refine ⟨g, hg, ?_⟩
    intro v
    obtain ⟨⟨p, q⟩, x⟩ := v
    have h1 : Θ ((p, q), x) = Φ (fun i => ι (x i), P (p, q)) := hΘ _
    have h2 : Θ ((p, q), fun i => ζ ^ (toAdd (t i)).val * x i) =
        Φ (fun i => ι (ζ ^ (toAdd (t i)).val * x i), P (p, q)) := hΘ _
    have hfun : (fun i => a i * ι (x i)) =
        fun i => ι (ζ ^ (toAdd (t i)).val * x i) := by
      funext i
      rw [show a i = ι (ζ ^ (toAdd (t i)).val) from rfl, ← map_mul]
    rw [h1, h2, hact (fun i => ι (x i)) (P (p, q)), hfun]

end CFSG.StandardType.OrthAnchor

end

module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.ClassicalInvolution.Asc77.AscT7TTrace
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
import CFSG.ClassicalInvolution.Orders.Classical
import CFSG.GH74.Orders.LieType
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalGeometry
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalAction
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Perm.ChainSpec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

private theorem uc22s2112r34_uniqo_sl2_sub_one {K : Type} [Field K] {A : SL(2, K)} {r : ℕ}
    (hA1 : A ≠ 1) (hrK : (r : K) ≠ 0) (hAr : A ^ r = 1) :
    ∀ X : Matrix (Fin 2) (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K) * X = X → X = 0 := by
  classical
  have hMr : (A : Matrix (Fin 2) (Fin 2) K) ^ r = 1 := by
    simpa using congrArg (fun z : SL(2, K) => (z : Matrix (Fin 2) (Fin 2) K)) hAr
  intro X hX
  have hXker : ((A : Matrix (Fin 2) (Fin 2) K) - 1) * X = 0 := by
    rw [sub_mul, one_mul, hX, sub_self]
  have hdetne : ((A : Matrix (Fin 2) (Fin 2) K) - 1).det ≠ 0 := by
    intro h0
    have hdet1 : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := A.det_coe
    have ht : (A : Matrix (Fin 2) (Fin 2) K).trace = 2 := by
      have h := CFSG.ClassicalInvolution.Asc77.T7T.det_sub_one hdet1
      rw [h0] at h
      exact (sub_eq_zero.mp h.symm).symm
    have hCH : (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
        (2 : K) • (A : Matrix (Fin 2) (Fin 2) K) - 1 := by
      have h := CFSG.ClassicalInvolution.Asc77.T7T.sq_eq_trace_smul_sub_det
        (A : Matrix (Fin 2) (Fin 2) K)
      rw [hdet1, ht, one_smul] at h
      exact h
    have hN : ((A : Matrix (Fin 2) (Fin 2) K) - 1) *
        ((A : Matrix (Fin 2) (Fin 2) K) - 1) = 0 := by
      calc ((A : Matrix (Fin 2) (Fin 2) K) - 1) * ((A : Matrix (Fin 2) (Fin 2) K) - 1)
          = (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K)
            - (A : Matrix (Fin 2) (Fin 2) K) - (A : Matrix (Fin 2) (Fin 2) K) + 1 := by
            noncomm_ring
        _ = 0 := by rw [hCH, two_smul]; abel
    have hpow := CFSG.ClassicalInvolution.Asc77.T7T.one_add_pow_of_sq_eq_zero hN r
    have h1M : (1 : Matrix (Fin 2) (Fin 2) K) +
        ((A : Matrix (Fin 2) (Fin 2) K) - 1) = (A : Matrix (Fin 2) (Fin 2) K) := by abel
    rw [h1M, hMr] at hpow
    have hzero : (r : K) • ((A : Matrix (Fin 2) (Fin 2) K) - 1) = 0 :=
      add_left_cancel (a := (1 : Matrix (Fin 2) (Fin 2) K)) (by simpa using hpow.symm)
    have hM1 : (A : Matrix (Fin 2) (Fin 2) K) - 1 = 0 :=
      (smul_eq_zero.mp hzero).resolve_left hrK
    exact hA1 (Subtype.ext (by simpa using sub_eq_zero.mp hM1))
  have h1 : ((A : Matrix (Fin 2) (Fin 2) K) - 1).det • X = 0 := by
    have h := congrArg
      (fun Y => Matrix.adjugate ((A : Matrix (Fin 2) (Fin 2) K) - 1) * Y) hXker
    rw [mul_zero, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.one_mul] at h
    exact h
  exact (smul_eq_zero.mp h1).resolve_left hdetne

private theorem uc22s2112r34_uniqo_fix_iff {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (F : OFrame Q) {A : SL(2, K)} {r : ℕ}
    (hA1 : A ≠ 1) (hrK : (r : K) ≠ 0) (hAr : A ^ r = 1) {v : V} :
    F.La A v = v ↔ F.coords v = 0 := by
  constructor
  · intro hv
    have h2 : v + F.incl ((A : Matrix (Fin 2) (Fin 2) K) * F.coords v - F.coords v) = v := by
      rw [← F.La_apply]
      exact hv
    have h1 : F.incl ((A : Matrix (Fin 2) (Fin 2) K) * F.coords v - F.coords v) = 0 :=
      add_left_cancel (a := v) (by simpa using h2)
    have h3 : (A : Matrix (Fin 2) (Fin 2) K) * F.coords v - F.coords v = 0 :=
      F.incl_injective (by simpa using h1)
    exact uc22s2112r34_uniqo_sl2_sub_one hA1 hrK hAr (F.coords v) (sub_eq_zero.mp h3)
  · intro hv
    rw [F.La_apply, hv, mul_zero, sub_self, map_zero, add_zero]

private theorem uc22s2112r34_uniqo_perp_eq_orthogonal {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (F : OFrame Q) :
    F.perp = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) F.span := by
  ext x
  rw [F.mem_perp_iff_forall_incl, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hx n hn
    obtain ⟨Y, rfl⟩ := hn
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hx Y
  · intro hx Y
    have h := hx (F.incl Y) ⟨Y, rfl⟩
    rwa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at h

theorem uc22s2112r34_frame_La_range_eq_of_mem {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {H H' : OFrame Q} {g : V ≃ₗ[K] V}
    (hg : g ∈ H.La.range) (hg' : g ∈ H'.La.range) (hg1 : g ≠ 1) {r : ℕ} (hr : Odd r)
    (hrK : (r : K) ≠ 0) (hgr : g ^ r = 1) : H.La.range = H'.La.range := by
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hg
  obtain ⟨A', hA'⟩ := MonoidHom.mem_range.mp hg'
  have hA1 : A ≠ 1 := by
    intro h
    exact hg1 (by rw [← hA, h, map_one])
  have hA'1 : A' ≠ 1 := by
    intro h
    exact hg1 (by rw [← hA', h, map_one])
  have hAr : A ^ r = 1 := by
    apply H.La_injective
    rw [map_pow, hA, hgr, map_one]
  have hA'r : A' ^ r = 1 := by
    apply H'.La_injective
    rw [map_pow, hA', hgr, map_one]
  have hfix : ∀ v, g v = v ↔ H.coords v = 0 := by
    intro v
    rw [← hA]
    exact uc22s2112r34_uniqo_fix_iff H hA1 hrK hAr
  have hfix' : ∀ v, g v = v ↔ H'.coords v = 0 := by
    intro v
    rw [← hA']
    exact uc22s2112r34_uniqo_fix_iff H' hA'1 hrK hA'r
  have hperp : H.perp = H'.perp := by
    ext v
    rw [H.mem_perp_iff, H'.mem_perp_iff, ← hfix v, ← hfix' v]
  have horth : LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) H.span =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) H'.span := by
    rw [← uc22s2112r34_uniqo_perp_eq_orthogonal H,
      ← uc22s2112r34_uniqo_perp_eq_orthogonal H', hperp]
  have hrefl : (QuadraticMap.polarBilin Q).IsRefl :=
    (QuadraticMap.isSymm_polarBilin Q).isRefl
  have hspan : H.span = H'.span := by
    calc H.span = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
          (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) H.span) :=
          (LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl H.span).symm
      _ = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
          (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) H'.span) := by
          rw [horth]
      _ = H'.span := LinearMap.BilinForm.orthogonal_orthogonal hQ hrefl H'.span
  have hLa : H'.La (-1) = H.La (-1) := H.La_neg_one_eq_of_span_eq hspan.symm
  rcases H.La_range_eq_or_eq_swap h2 hLa with heq | hswap
  · exact heq.symm
  · exfalso
    have hgswap : g ∈ H.swap.La.range := hswap ▸ hg'
    have hgmem : H.La A ∈ H.swap.La.range := by rwa [hA]
    rcases (H.La_mem_swap_range_iff A).mp hgmem with h1 | hneg
    · exact hg1 (by rw [← hA, h1, map_one])
    · have hg2 : g ^ 2 = 1 := by
        rw [pow_two, ← hA, hneg]
        exact H.La_neg_one_mul_self
      have hgpow : g ^ r = g := by
        obtain ⟨k, hk⟩ := hr
        rw [hk, pow_succ, pow_mul, hg2, one_pow, one_mul]
      rw [hgpow] at hgr
      exact hg1 hgr


private theorem uc22s2112r34_uniqo_eq_of_mem_inf_orth_aux {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {t : StatedLieTag} {n p f : ℕ} [fact : Fact p.Prime]
    (hp : p.Prime) (hp2 : p ≠ 2) (ht : t = .POmegaOdd ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K)
    (hK' : IsFundamentalOver (p ^ f) K') {x : X} (hxK : x ∈ K) (hxK' : x ∈ K')
    (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2) (hxp : orderOf x ≠ p) : K = K' := by
  classical
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    rcases ht with rfl | rfl <;> trivial
  have hnA1 : ¬ (t = .PSL ∧ n = 2) := by
    rcases ht with rfl | rfl <;> simp
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t n p f
    Fact.out hp2 hfund hadm X hX
  obtain ⟨hZ, -, hL2, -⟩ := fundamental_ambient_of_lieModel hp hp2 hadm hX hnA1 hK
  obtain ⟨R, hR, hRK, hRker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general Fact.out hp2 hadm hX
      hfund hnA1 hL2 ψ hψ hker hK
  obtain ⟨R', hR', hR'K, hR'ker⟩ :=
    exists_mem_fundamentalSubgroups_of_isFundamentalOver_general Fact.out hp2 hadm hX
      hfund hnA1 hL2 ψ hψ hker hK'
  have ht' : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus := by
    rcases ht with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  obtain ⟨D⟩ := exists_paired_orthogonal_model (t := t) (n := n) (p := p) (e := f)
    hp2 ht' hadm
  have hxKmap : x ∈ R.map ψ := by rw [← hRK]; exact hxK
  have hxK'map : x ∈ R'.map ψ := by rw [← hR'K]; exact hxK'
  obtain ⟨a, haR, hψa⟩ := Subgroup.mem_map.mp hxKmap
  obtain ⟨b, hbR, hψb⟩ := Subgroup.mem_map.mp hxK'map
  have ha_r : a ^ orderOf x = 1 := by
    have hmem : a ^ orderOf x ∈ R ⊓ ψ.ker := by
      refine ⟨pow_mem haR _, ?_⟩
      change ψ (a ^ orderOf x) = 1
      rw [map_pow, hψa, pow_orderOf_eq_one]
    rw [hRker] at hmem
    simpa using hmem
  have hb_r : b ^ orderOf x = 1 := by
    have hmem : b ^ orderOf x ∈ R' ⊓ ψ.ker := by
      refine ⟨pow_mem hbR _, ?_⟩
      change ψ (b ^ orderOf x) = 1
      rw [map_pow, hψb, pow_orderOf_eq_one]
    rw [hR'ker] at hmem
    simpa using hmem
  have ha1 : a ≠ 1 := by
    intro ha
    have hx1 : x = 1 := by rw [← hψa, ha, map_one]
    exact hxr.ne_one (by rw [hx1, orderOf_one])
  let ζ := a * b⁻¹
  have hζker : ζ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    change ψ (a * b⁻¹) = 1
    rw [map_mul, map_inv, hψa, hψb, mul_inv_cancel]
  have hζcenter := hker hζker
  have hζcomm : Commute ζ b := (Subgroup.mem_center_iff.mp hζcenter b).symm
  have haeq : a = ζ * b := by
    change a = (a * b⁻¹) * b
    group
  have hζpow : ζ ^ orderOf x = 1 := by
    have h1 : a ^ orderOf x = (ζ ^ orderOf x) * (b ^ orderOf x) := by
      rw [haeq]
      exact hζcomm.mul_pow (orderOf x)
    rw [ha_r, hb_r, mul_one] at h1
    exact h1.symm
  obtain ⟨H, hH⟩ := D.hmap R hR
  obtain ⟨H', hH'⟩ := D.hmap R' hR'
  have hπQ : ∀ (z : (CFSG.ClassicalInvolution.Generic.modelUniv t n p f Fact.out).K) (v : D.V),
      D.Q (D.π z v) = D.Q v := by
    intro z v
    rw [D.hπ]
    exact CFSG.LieType.Universal.Spin.map_spinAction D.Q (D.η.toMonoidHom z) v
  obtain ⟨c, hc⟩ :=
    (CFSG.ClassicalGroups.Orthogonal.mem_scalars (K := GaloisField p f) (V := D.V)).mp
      (D.hscalar ζ hζcenter)
  have hvQ : D.Q (H.e₁ + H.f₁) = 1 := by
    have h : H.e₁ + H.f₁ = H.incl (1 : Matrix (Fin 2) (Fin 2) (GaloisField p f)) := by
      rw [H.incl_apply]
      simp
    rw [h, H.Q_incl, Matrix.det_one]
  have hwne : H.e₁ + H.f₁ ≠ 0 := by
    intro h0
    have h1 : D.Q (H.e₁ + H.f₁) = 0 := by rw [h0, QuadraticMap.map_zero]
    rw [hvQ] at h1
    exact one_ne_zero h1
  have hc2 : c ^ 2 = 1 := by
    have h1 : D.Q (D.π ζ (H.e₁ + H.f₁)) = 1 := by
      rw [hπQ ζ (H.e₁ + H.f₁), hvQ]
    rw [hc (H.e₁ + H.f₁), QuadraticMap.map_smul, hvQ] at h1
    simpa [pow_two, smul_eq_mul] using h1
  have hc_r : c ^ orderOf x = 1 := by
    have hpow : ∀ (m : ℕ) (v : D.V), ((D.π ζ) ^ m) v = (c ^ m) • v := by
      intro m
      induction m with
      | zero => intro v; simp
      | succ m ih =>
          intro v
          rw [pow_succ, LinearEquiv.mul_apply, hc, ih, smul_smul, ← pow_succ]
    have h1 : ((D.π ζ) ^ orderOf x) (H.e₁ + H.f₁) = H.e₁ + H.f₁ := by
      rw [← map_pow, hζpow, map_one]
      rfl
    rw [hpow (orderOf x)] at h1
    have h2 : (c ^ orderOf x - 1) • (H.e₁ + H.f₁) = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hwne
    exact sub_eq_zero.mp h3
  have hc1 : c = 1 := by
    have hcop : Nat.Coprime 2 (orderOf x) :=
      Nat.coprime_two_left.mpr (hxr.odd_of_ne_two hx2)
    exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hc2, hc_r⟩
  have hπζ1 : D.π ζ = 1 := by
    ext v
    rw [hc v, hc1, one_smul]
    rfl
  have hπab : D.π a = D.π b := by
    rw [haeq, map_mul, hπζ1, one_mul]
  have hgH : D.π a ∈ H.La.range := by
    rw [← hH]
    exact Subgroup.mem_map_of_mem D.π haR
  have hgH' : D.π a ∈ H'.La.range := by
    rw [← hH', hπab]
    exact Subgroup.mem_map_of_mem D.π hbR
  have hgr : (D.π a) ^ orderOf x = 1 := by
    rw [← map_pow, ha_r, map_one]
  have hg1 : D.π a ≠ 1 := by
    intro h
    have haKer : a ∈ D.π.ker := MonoidHom.mem_ker.mpr h
    have haz : a ∈ Subgroup.center
        (CFSG.ClassicalInvolution.Generic.modelUniv t n p f Fact.out).K := D.hker haKer
    have hxcenter : ψ a ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := hψ y
      show ψ w * ψ a = ψ a * ψ w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp haz w]
    have hmem : ψ a ∈ (⊥ : Subgroup X) := by rwa [← hZ]
    rw [Subgroup.mem_bot] at hmem
    have hx1 : x = 1 := by rw [← hψa, hmem]
    exact hxr.ne_one (by rw [hx1, orderOf_one])
  have h2F : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hrK : ((orderOf x : ℕ) : GaloisField p f) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (GaloisField p f) hxr (Ne.symm hxp)
  have hframe : H.La.range = H'.La.range :=
    uc22s2112r34_frame_La_range_eq_of_mem (K := GaloisField p f) (V := D.V) (H := H)
      (H' := H') (g := D.π a) (r := orderOf x) h2F D.hQ hgH hgH' hg1
      (hxr.odd_of_ne_two hx2) hrK hgr
  have hmapEq : R.map D.π = R'.map D.π := by
    rw [hH, hH', hframe]
  have hRR' : R = R' :=
    eq_modelFund_of_map_eq hp2 hfund hadm D.π D.hker hR hR' hmapEq
  rw [hRK, hR'K, hRR']

theorem uc22s2112r34_eq_of_mem_inf_orth {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t = .POmegaOdd ∨ t = .POmegaMinus) (hadm : StatedLieAdmissible t n p f)
    (hX : CFSG.Blueprint.LieModel X t n p f) {K K' : Subgroup X}
    (hK : IsFundamentalOver (p ^ f) K) (hK' : IsFundamentalOver (p ^ f) K') {x : X}
    (hxK : x ∈ K) (hxK' : x ∈ K') (hxr : (orderOf x).Prime) (hx2 : orderOf x ≠ 2)
    (hxp : orderOf x ≠ p) : K = K' :=
  uc22s2112r34_uniqo_eq_of_mem_inf_orth_aux (fact := ⟨hp⟩) hp hp2 ht hadm hX hK hK' hxK hxK'
    hxr hx2 hxp

end CFSG.LocalAnalysis.UniquenessCase.UC22

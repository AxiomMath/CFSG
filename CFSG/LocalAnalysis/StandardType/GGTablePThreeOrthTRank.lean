module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalReciprocal
public import CFSG.Assembly.GL83LieDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsRank
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDPlane
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitFrame
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om6
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
import CFSG.CGT.Timmesfeld75.Forms
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om4
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om5
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsMat
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Exc
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU
import CFSG.RankThree.GF2n.Stroth80.Anisotropic
import CFSG.RankThree.GF2n.Stroth80.FrobClause
import CFSG.RankThree.GF2n.Stroth80.GlobalModel
import CFSG.RankThree.GF2n.Stroth80.Sec36
import CFSG.RankThree.GF2n.SupIndepDecomp
import CFSG.RankThree.GF2n.Tim79CentC
import CFSG.RankThree.GF2n.Tim79CentL
import CFSG.RankThree.GF2n.Tim79Mod
import CFSG.Timmesfeld.Orders.ClassicalLinearThree

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

private theorem orthTRank_commute {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x y : ↥(orthDerived Q)} {Â : Subgroup ↥(orthDerived Q)}
    (hÂ : CFSG.Open.IsElemAbelian 3 Â) (hxÂ : x ∈ Â) (hy : y ∈ Â) :
    Commute (y : V ≃ₗ[K] V) (x : V ≃ₗ[K] V) := by
  have : IsMulCommutative ↥Â := (CFSG.Open.IsElemAbelian.isElementaryAbelian hÂ).toIsMulCommutative
  have hc : (⟨y, hy⟩ : ↥Â) * ⟨x, hxÂ⟩ = ⟨x, hxÂ⟩ * ⟨y, hy⟩ := mul_comm' _ _
  exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) (congrArg Subtype.val hc)

private theorem orthTRank_block_scalar {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x y : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap)
    (hyc : Commute (y : V ≃ₗ[K] V) (x : V ≃ₗ[K] V))
    (hscal : ∃ c : (AdjoinRoot h)ˣ, ∀ v : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h,
      (y : V ≃ₗ[K] V) (v : V) =
        (((c : AdjoinRoot h) • v : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) : V)) :
    ∀ g ∈ componentImage Q (x : V ≃ₗ[K] V) h,
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y * g =
        g * QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y := by
  intro g hg
  obtain ⟨f, hf, hfg⟩ := Subgroup.mem_map.mp hg
  rw [← hfg]
  have hf' : (f : V ≃ₗ[K] V) ∈ specialBlock Q (x : V ≃ₗ[K] V) h :=
    Subgroup.mem_subgroupOf.mp hf
  have hfB : (f : V ≃ₗ[K] V) ∈ supportedBlock Q (x : V ≃ₗ[K] V) h :=
    specialBlock_le_supportedBlock h hf'
  have hf_iso : (f : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
    (Subgroup.mem_inf.mp hfB).1
  have hf_orth : (f : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp hf_iso).1
  have hf_cent : (f : V ≃ₗ[K] V) ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp hf_iso).2
  have hf_fix : ∀ w ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap h,
      (f : V ≃ₗ[K] V) w = w := (mem_supportedBlock.mp hfB).2
  have hy_orth : (y : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hy_cent : (y : V ≃ₗ[K] V) ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hyc.symm
  let c : V ≃ₗ[K] V :=
    (y : V ≃ₗ[K] V) * (f : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)⁻¹ * (f : V ≃ₗ[K] V)⁻¹
  have hc_orth : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    dsimp [c]
    exact mul_mem (mul_mem (mul_mem hy_orth hf_orth) (inv_mem hy_orth)) (inv_mem hf_orth)
  have hc_cent : c ∈ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    dsimp [c]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy_cent hf_cent)
      (Subgroup.inv_mem _ hy_cent)) (Subgroup.inv_mem _ hf_cent)
  have hc_fix : ∀ v ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap h, c v = v := by
    intro v hv
    have hf_inv_fix : (f : V ≃ₗ[K] V)⁻¹ v = v := by
      have h1 : (f : V ≃ₗ[K] V) v = v := hf_fix v hv
      calc (f : V ≃ₗ[K] V)⁻¹ v
          = (f : V ≃ₗ[K] V)⁻¹ ((f : V ≃ₗ[K] V) v) := by rw [h1]
        _ = v := LinearEquiv.symm_apply_apply (f : V ≃ₗ[K] V) v
    have hy_inv_mem : (y : V ≃ₗ[K] V)⁻¹ v ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap h :=
      mem_othersSpace_of_apply (Subgroup.inv_mem _ hy_cent) hv
    change ((y : V ≃ₗ[K] V) * (f : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V)⁻¹ *
      (f : V ≃ₗ[K] V)⁻¹) v = v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hf_inv_fix, hf_fix _ hy_inv_mem]
    exact LinearEquiv.apply_symm_apply (y : V ≃ₗ[K] V) v
  have hcB : c ∈ supportedBlock Q (x : V ≃ₗ[K] V) h :=
    mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨hc_orth, hc_cent⟩, hc_fix⟩
  have hc_gl : blockGL Q (x : V ≃ₗ[K] V) h ⟨c, hcB⟩ = 1 := by
    obtain ⟨c_y, hc_y⟩ := hscal
    let Y : ↥(Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) :=
      ⟨(y : V ≃ₗ[K] V), hy_cent⟩
    let F : ↥(Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) :=
      ⟨(f : V ≃ₗ[K] V), hf_cent⟩
    have hY_scalar : centralizerGL (x : V ≃ₗ[K] V) h Y = scalarGL (x : V ≃ₗ[K] V) h c_y := by
      refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
      rw [coe_centralizerGL, coe_scalarGL]
      exact hc_y v
    have hYF : (Subgroup.inclusion (supportedBlock_le_centralizer h)) ⟨c, hcB⟩ =
        Y * F * Y⁻¹ * F⁻¹ := by
      apply Subtype.ext
      rfl
    change (centralizerGL (x : V ≃ₗ[K] V) h)
      ((Subgroup.inclusion (supportedBlock_le_centralizer h)) ⟨c, hcB⟩) = 1
    rw [hYF, map_mul, map_mul, map_mul, map_inv, map_inv, hY_scalar]
    have hcentral : (centralizerGL (x : V ≃ₗ[K] V) h F) * (scalarGL (x : V ≃ₗ[K] V) h c_y) =
        (scalarGL (x : V ≃ₗ[K] V) h c_y) * (centralizerGL (x : V ≃ₗ[K] V) h F) :=
      Subgroup.mem_center_iff.mp (scalarGL_mem_center (x := (x : V ≃ₗ[K] V)) h c_y)
        (centralizerGL (x : V ≃ₗ[K] V) h F)
    rw [← hcentral]
    group
  have hc_eq : (⟨c, hcB⟩ : ↥(supportedBlock Q (x : V ≃ₗ[K] V) h)) = 1 :=
    hx.eq_one_of_blockGL_eq_one hh hc_gl
  have hcomm_yf : (y : V ≃ₗ[K] V) * (f : V ≃ₗ[K] V) =
      (f : V ≃ₗ[K] V) * (y : V ≃ₗ[K] V) := by
    have h1 : c = 1 := congrArg Subtype.val hc_eq
    dsimp [c] at h1
    refine mul_inv_eq_one.mp ?_
    rw [mul_inv_rev, mul_assoc]
    exact h1
  have hyf : (y : ↥(orthDerived Q)) * f = f * (y : ↥(orthDerived Q)) := Subtype.ext hcomm_yf
  calc QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y *
        QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) f
      = QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
          ((y : ↥(orthDerived Q)) * f) :=
        (map_mul (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) y f).symm
    _ = QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
          (f * (y : ↥(orthDerived Q))) := by rw [hyf]
    _ = QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) f *
        QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y :=
        map_mul (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) f y

private theorem orthTRank_pgl_two {E : Type} [Field E] [Finite E]
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (hU : Module.finrank E U = 2) (hE3 : ¬ 3 ∣ Nat.card E)
    {B : Subgroup (U ≃ₗ[E] U)} (hB : CFSG.Open.IsElemAbelian 3 B) :
    Nat.card B ≤ 3 ^ 2 := by
  let b : Module.Basis (Fin 2) E U := (Module.finBasis E U).reindex (finCongr hU)
  let e : GL (Fin 2) E ≃* (U ≃ₗ[E] U) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv E U)
  have hcard : Nat.card (B.map e.symm.toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective e.symm.injective
  have hB' : CFSG.Open.IsElemAbelian 3 (B.map e.symm.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hB e.symm.toMonoidHom
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.card_le_nine_of_elemAbelian_GL2
    (K := E) hE3 hB'
  rw [hcard] at h
  simpa using h

private theorem orthTRank_block {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V)) (hx1 : x ≠ 1)
    {Â : Subgroup ↥(orthDerived Q)} (hÂ : CFSG.Open.IsElemAbelian 3 Â) (hxÂ : x ∈ Â)
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hm2 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 2)
    {J' : Subgroup (ProjOrthDerived Q)} (hJ : J' ≤ componentImage Q (x : V ≃ₗ[K] V) h)
    (hker : ∀ y ∈ Â, (∀ g ∈ J', QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y * g =
        g * QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y) →
        y ∈ Subgroup.zpowers x) :
    Nat.card Â ≤ 3 ^ 2 := by
  have hcent : ∀ y ∈ Â, (y : V ≃ₗ[K] V) ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (orthTRank_commute hÂ hxÂ hy).symm
  have : IsMulCommutative ↥Â := hÂ.1
  let Vh := primaryComponent (x : V ≃ₗ[K] V).toLinearMap h
  let ψ : ↥Â →* ↥(Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) :=
    { toFun := fun y => ⟨(y : V ≃ₗ[K] V), hcent y y.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let φ : ↥Â →* (Vh ≃ₗ[AdjoinRoot h] Vh) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h) Vh).toMonoidHom.comp
      ((centralizerGL (x : V ≃ₗ[K] V) h).comp ψ)
  have hU : Module.finrank (AdjoinRoot h) Vh = 2 := by
    simpa only [Vh, primaryMultiplicity] using hm2
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hroot3 : AdjoinRoot.root h ^ 3 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hroot0 : AdjoinRoot.root h ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 3 ≠ 0)] at hroot3
    exact zero_ne_one hroot3
  let xÂ : ↥Â := ⟨x, hxÂ⟩
  have hVh_ne : Vh ≠ ⊥ := primaryComponent_ne_bot hx.squarefree_minpoly hh
  have hker_le : φ.ker ≤ Subgroup.zpowers xÂ := by
    intro y hy
    have hy1 : φ y = 1 := MonoidHom.mem_ker.mp hy
    have hcy1 : centralizerGL (x : V ≃ₗ[K] V) h (ψ y) = 1 :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h) Vh).injective (by
        simpa [φ] using hy1)
    have hscal : ∃ c : (AdjoinRoot h)ˣ, ∀ v : Vh,
        ((y : ↥(orthDerived Q)) : V ≃ₗ[K] V) (v : V) =
          (((c : AdjoinRoot h) • v : Vh) : V) := by
      refine ⟨1, fun v => ?_⟩
      have hh' := coe_centralizerGL (x : V ≃ₗ[K] V) h (ψ y) v
      rw [hcy1] at hh'
      simpa [ψ] using hh'.symm
    have hyx : (y : ↥(orthDerived Q)) ∈ Subgroup.zpowers x :=
      hker (y : ↥(orthDerived Q)) y.2 (fun g hg =>
        orthTRank_block_scalar (Q := Q) (y := (y : ↥(orthDerived Q))) hx hh
          (orthTRank_commute hÂ hxÂ y.2) hscal g (hJ hg))
    rw [Subgroup.mem_zpowers_iff] at hyx ⊢
    obtain ⟨k, hk⟩ := hyx
    exact ⟨k, Subtype.ext hk⟩
  have hx_not_ker : xÂ ∉ φ.ker := by
    intro hxker
    have hx1 : φ xÂ = 1 := hxker
    have hcx1 : centralizerGL (x : V ≃ₗ[K] V) h (ψ xÂ) = 1 :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h) Vh).injective (by
        simpa [φ] using hx1)
    have hxscalar : centralizerGL (x : V ≃ₗ[K] V) h (ψ xÂ) =
        scalarGL (x : V ≃ₗ[K] V) h (Units.mk0 (AdjoinRoot.root h) hroot0) := by
      refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
      rw [coe_centralizerGL, coe_scalarGL]
      exact (coe_root_smul_primaryComponent
        (x := (x : V ≃ₗ[K] V).toLinearMap) (a := h) v).symm
    have hroot1 : AdjoinRoot.root h = 1 := by
      have h1 : scalarGL (x : V ≃ₗ[K] V) h (Units.mk0 (AdjoinRoot.root h) hroot0) = 1 := by
        rw [← hxscalar]; exact hcx1
      have h2 : Units.mk0 (AdjoinRoot.root h) hroot0 = 1 :=
        scalarGL_injective h hVh_ne (by rw [h1, scalarGL_one])
      simpa using congrArg (fun u : (AdjoinRoot h)ˣ => (u : AdjoinRoot h)) h2
    exact root_ne_one hmon hne1 hroot1
  have hker_bot : φ.ker = ⊥ := by
    by_contra hne
    have hx3 : xÂ ^ 3 = 1 := Subtype.ext (Subtype.ext hx.pow_eq_one)
    have hxne1 : xÂ ≠ 1 := fun h =>
      hx1 (congrArg (fun z : ↥Â => (z : ↥(orthDerived Q))) h)
    have hord : orderOf xÂ = 3 := orderOf_eq_prime hx3 hxne1
    have hcard_z : Nat.card (Subgroup.zpowers xÂ) = 3 := by rw [Nat.card_zpowers, hord]
    have hdvd : Nat.card φ.ker ∣ 3 := by
      have := Subgroup.card_dvd_of_le hker_le
      rwa [hcard_z] at this
    have hlt : 1 < Nat.card φ.ker := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    have h3 : Nat.card φ.ker = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · omega
      · exact h3
    have heq : φ.ker = Subgroup.zpowers xÂ := by
      refine Subgroup.eq_of_le_of_card_ge hker_le ?_
      rw [h3, hcard_z]
    exact hx_not_ker (heq ▸ Subgroup.mem_zpowers xÂ)
  have hrange : CFSG.Open.IsElemAbelian 3 φ.range :=
    ⟨⟨⟨fun a b => Subtype.ext (by
        obtain ⟨a', ha'⟩ := a.2
        obtain ⟨b', hb'⟩ := b.2
        show (↑a : Vh ≃ₗ[AdjoinRoot h] Vh) * ↑b = ↑b * ↑a
        rw [← ha', ← hb']
        rw [← map_mul, ← map_mul]
        exact congrArg φ (mul_comm' a' b'))⟩⟩,
      fun x hx => by
        obtain ⟨a, rfl⟩ := hx
        have ha : a ^ 3 = 1 := Subtype.ext (hÂ.2 a a.2)
        rw [← map_pow, ha, map_one]⟩
  have hE3 : ¬ 3 ∣ Nat.card (AdjoinRoot h) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, -, hn⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_eq_pow_of_charP K 2
    have hcard : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h),
        (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
    rw [hcard, hn]
    intro h3
    have h3' : 3 ∣ 2 ^ n := Nat.prime_three.dvd_of_dvd_pow h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3') (by norm_num)
  have hcard_range : Nat.card φ.range ≤ 3 ^ 2 :=
    orthTRank_pgl_two (U := Vh) (E := AdjoinRoot h) hU hE3 hrange
  have hcard := Subgroup.card_ker_mul_card_range φ
  calc Nat.card Â = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ = 1 * Nat.card φ.range := by rw [hker_bot, Subgroup.card_bot]
    _ ≤ 1 * 3 ^ 2 := by gcongr
    _ = 3 ^ 2 := by norm_num

private theorem orthTRank_fixed_trivial {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x y : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    (hyc : Commute (y : V ≃ₗ[K] V) (x : V ≃ₗ[K] V))
    (h1 : ∀ w : fixedSpace (x : V ≃ₗ[K] V), (y : V ≃ₗ[K] V) (w : V) = (w : V)) :
    ∀ g ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V),
      Commute (y : V ≃ₗ[K] V) g := by
  intro g hg
  show (y : V ≃ₗ[K] V) * g = g * (y : V ≃ₗ[K] V)
  ext v
  obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
  have hgB : g ∈ supportedBlock Q (x : V ≃ₗ[K] V) (X - 1) :=
    (mem_supportedFixedDerived.mp hg).1
  have hgcent : g ∈ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) :=
    (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _ hgB)).2
  have hgfix : ∀ r ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1), g r = r :=
    (mem_supportedBlock.mp hgB).2
  have hycent : (y : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hyc.symm
  have hgw : g (w : V) ∈ fixedSpace (x : V ≃ₗ[K] V) := mem_fixedSpace_of_apply hgcent hw
  have hyr : (y : V ≃ₗ[K] V) r ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1) :=
    mem_othersSpace_of_apply hycent hr
  simp only [LinearEquiv.mul_apply, map_add]
  rw [h1 ⟨g (w : V), hgw⟩, h1 ⟨w, hw⟩, hgfix _ hr, hgfix _ hyr]

private theorem orthTRank_fixed {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V))
    {Â : Subgroup ↥(orthDerived Q)} (hÂ : CFSG.Open.IsElemAbelian 3 Â) (hxÂ : x ∈ Â)
    {J' : Subgroup (ProjOrthDerived Q)}
    (hdim : Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype))
    (hJ : J' ≤ fixedComponentImage Q (x : V ≃ₗ[K] V))
    (hker : ∀ y ∈ Â, (∀ g ∈ J', QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y * g =
        g * QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y) →
        y ∈ Subgroup.zpowers x) :
    Nat.card Â ≤ 3 ^ 2 := by
  have : IsMulCommutative ↥Â :=
    (CFSG.Open.IsElemAbelian.isElementaryAbelian hÂ).toIsMulCommutative
  have hcent : ∀ y ∈ Â, (y : V ≃ₗ[K] V) ∈
      Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (orthTRank_commute hÂ hxÂ hy).symm
  let W := fixedSpace (x : V ≃ₗ[K] V)
  let φ : ↥Â →* (W ≃ₗ[K] W) :=
    { toFun := fun y => restrictEquiv W (y : V ≃ₗ[K] V)
        (fun w hw => mem_fixedSpace_of_apply (hcent y y.2) hw)
        (fun w hw => mem_fixedSpace_of_apply (inv_mem (hcent y y.2)) hw)
      map_one' := LinearEquiv.ext fun w => Subtype.ext rfl
      map_mul' := fun a b => LinearEquiv.ext fun w => Subtype.ext rfl }
  have hcentral : ∀ y : ↥Â, y ∈ φ.ker → ∀ g ∈ J',
      QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) (y : ↥(orthDerived Q)) * g =
        g * QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) (y : ↥(orthDerived Q)) := by
    intro y hy g hg
    have hy1 : φ y = 1 := MonoidHom.mem_ker.mp hy
    have hfix : ∀ w : W, (y : V ≃ₗ[K] V) (w : V) = (w : V) := by
      intro w
      have h := congrArg (fun e : W ≃ₗ[K] W => ((e w : W) : V)) hy1
      simpa [φ, W, coe_restrictEquiv] using h
    have htriv := orthTRank_fixed_trivial (Q := Q) hx (orthTRank_commute hÂ hxÂ y.2) hfix
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp (hJ hg)
    have hf' : (f : V ≃ₗ[K] V) ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V) :=
      Subgroup.mem_subgroupOf.mp hf
    have hfy : (y : ↥(orthDerived Q)) * f = f * (y : ↥(orthDerived Q)) :=
      Subtype.ext (htriv (f : V ≃ₗ[K] V) hf')
    rw [← map_mul, ← map_mul, hfy]
  have hker_card : Nat.card φ.ker ≤ 3 := by
    have hx3 : x ^ 3 = 1 := Subtype.ext hx.pow_eq_one
    have hdvd : Nat.card (Subgroup.zpowers x) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hx3
    have hcard_le : Nat.card (Subgroup.zpowers x) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    refine le_trans ?_ hcard_le
    refine Nat.card_le_card_of_injective
      (fun y : φ.ker => (⟨((y : ↥Â) : ↥(orthDerived Q)),
        hker _ (y : ↥Â).2 (hcentral (y : ↥Â) y.2)⟩ : Subgroup.zpowers x)) ?_
    intro y z hyz
    have h1 : ((y : ↥Â) : ↥(orthDerived Q)) = ((z : ↥Â) : ↥(orthDerived Q)) :=
      congrArg (fun w : Subgroup.zpowers x => (w : ↥(orthDerived Q))) hyz
    exact Subtype.ext (Subtype.ext h1)
  have hrange_card : Nat.card φ.range ≤ 3 := by
    have hreg : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate := by
      simpa [W] using hx.polarBilin_fixed_nondegenerate
    refine CFSG.StandardType.SmallOrthUn.card_le_of_four_minus hreg (by simpa [W] using hdim)
      (by simpa [W] using hminus) Nat.prime_three (by norm_num) _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro w
      change Q (((φ y) w : W) : V) = Q (w : V)
      rw [show (((φ y) w : W) : V) = (y : V ≃ₗ[K] V) (w : V) from coe_restrictEquiv W _ _ _ w]
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (orthDerived_le_orthogonalGroup (y : ↥(orthDerived Q)).2) (w : V)
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm' a b]
    · rintro _ ⟨a, rfl⟩
      have ha : a ^ 3 = 1 := Subtype.ext (hÂ.2 a a.2)
      rw [← map_pow, ha, map_one]
  have hcard := Subgroup.card_ker_mul_card_range φ
  calc Nat.card Â = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker_card hrange_card
    _ = 3 ^ 2 := by norm_num

theorem orthT_rankA1 {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V)) (hx1 : x ≠ 1)
    {Â : Subgroup ↥(orthDerived Q)} (hÂ : CFSG.Open.IsElemAbelian 3 Â) (hxÂ : x ∈ Â)
    {J' : Subgroup (ProjOrthDerived Q)}
    (hJ : (∃ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 ∧
          primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 2 ∧ J' ≤ componentImage Q (x : V ≃ₗ[K] V) h) ∨
        (Module.finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 4 ∧
          ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) ∧
          J' ≤ fixedComponentImage Q (x : V ≃ₗ[K] V)))
    (hker : ∀ y ∈ Â, (∀ g ∈ J', QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y * g =
        g * QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) y) → y ∈ Subgroup.zpowers x) :
    Nat.card Â ≤ 3 ^ 2 := by
  rcases hJ with ⟨h, hh, hne1, hm2, hJle⟩ | ⟨hdim, hminus, hJle⟩
  · exact orthTRank_block hx hx1 hÂ hxÂ hh hne1 hm2 hJle hker
  · exact orthTRank_fixed hx hÂ hxÂ hdim hminus hJle hker

end CFSG.StandardType.TablePThreeKG

end

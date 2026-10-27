module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCentralizer
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Simple
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar
import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Models
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartTwo.Sec12.Hering129D4HSL2
import CFSG.GroupTheory.GroupAction.PerfectCommutingSL2
import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCore
import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcComp
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorChart
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalPairs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrAxis
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSplitFourRadical
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.GroupTheory.CentralizerMap
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

variable {f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]

private theorem planeScalars_apply_eq_self_iff (E : QuadExt F K (unitaryInvolution K 2 f))
    {r : ℕ} (P : Finset (Fin r)) {T : normOmega E r} (lam : Fin r → K)
    (hT : ∀ v : (F × F) × (Fin r → K),
      (T : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))) v = (v.1, fun i => lam i * v.2 i))
    (hlam : ∀ i, i ∉ P → lam i ≠ 1) (hlamP : ∀ i ∈ P, lam i = 1)
    (v : (F × F) × (Fin r → K)) :
    (T : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))) v = v ↔
      v ∈ CFSG.RankThree.PartOne.KCOrthogonal.coordSupport
        (LinearEquiv.refl F ((F × F) × (Fin r → K))) P := by
  rw [mem_coordSupport_refl_iff E P v, hT v]
  constructor
  · intro h j hj
    have h2 : lam j * v.2 j = v.2 j := congrFun (congrArg Prod.snd h) j
    by_contra hne
    exact hlam j hj (mul_right_cancel₀ hne (h2.trans (one_mul _).symm))
  · intro h
    refine Prod.ext rfl (funext fun j => ?_)
    by_cases hj : j ∈ P
    · simp [hlamP j hj]
    · simp [h j hj]

theorem mem_normalizer_normBlock_of_commute_planeScalars
    (E : QuadExt F K (unitaryInvolution K 2 f)) {r : ℕ} (P : Finset (Fin r))
    {T s : normOmega E r} (lam : Fin r → K)
    (hT : ∀ v : (F × F) × (Fin r → K),
      (T : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))) v = (v.1, fun i => lam i * v.2 i))
    (hlam : ∀ i, i ∉ P → lam i ≠ 1) (hlamP : ∀ i ∈ P, lam i = 1) (hs : s * T = T * s) :
    s ∈ Subgroup.normalizer (normBlock E r P : Set (normOmega E r)) := by
  classical
  let V := (F × F) × (Fin r → K)
  let R : Submodule F V :=
    CFSG.RankThree.PartOne.KCOrthogonal.coordSupport (LinearEquiv.refl F V) P
  have hfix := planeScalars_apply_eq_self_iff E P lam hT hlam hlamP
  have hmapR : ∀ u : normOmega E r, u * T = T * u →
      R.map (u : V ≃ₗ[F] V).toLinearMap = R := by
    intro u hu
    have hle : ∀ w : normOmega E r, w * T = T * w →
        R.map (w : V ≃ₗ[F] V).toLinearMap ≤ R := by
      intro w hw
      rintro _ ⟨v, hv, rfl⟩
      have hTv : (T : V ≃ₗ[F] V) v = v := (hfix v).2 hv
      refine (hfix _).1 ?_
      have h := congrArg (fun z : normOmega E r => (z : V ≃ₗ[F] V) v) hw
      simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, hTv] at h
      exact h.symm
    refine le_antisymm (hle u hu) ?_
    intro v hv
    have hu' : u⁻¹ * T = T * u⁻¹ := (Commute.inv_left (show Commute u T from hu)).eq
    have hv' : (u⁻¹ : normOmega E r).1.toLinearMap v ∈ R :=
      hle u⁻¹ hu' ⟨v, hv, rfl⟩
    refine ⟨(u⁻¹ : normOmega E r).1.toLinearMap v, hv', ?_⟩
    change (u : V ≃ₗ[F] V) (((u⁻¹ : normOmega E r) : V ≃ₗ[F] V) v) = v
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
    rfl
  have hconj : ∀ u : normOmega E r, u * T = T * u → ∀ h ∈ normBlock E r P,
      u * h * u⁻¹ ∈ normBlock E r P := by
    intro u hu h hh
    have hO : (u : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r) :=
      CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup_of_commutator _ u.2
    have hmap := CFSG.RankThree.PartOne.KCOrthogonal.map_supportedDerived_conj_of_map_eq
      (u : V ≃ₗ[F] V) hO (hmapR u hu)
    have hh' : (h : V ≃ₗ[F] V) ∈
        CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived (normHypForm E r) R :=
      Subgroup.mem_subgroupOf.mp hh
    have hmem : (u : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (u : V ≃ₗ[F] V)⁻¹ ∈
        CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived (normHypForm E r) R := by
      rw [← hmap]
      exact ⟨h, hh', rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj s hs h, fun hh => ?_⟩
  have hs' : s⁻¹ * T = T * s⁻¹ := (Commute.inv_left (show Commute s T from hs)).eq
  have := hconj s⁻¹ hs' _ hh
  simpa [mul_assoc] using this

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.PhanDn
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

private theorem center_eq_bot_of_simple_of_perfect {Q : Type*} [Group Q]
    (hs : IsSimpleGroup Q) (hp : Group.IsPerfect Q) : Subgroup.center Q = ⊥ := by
  have hcomm : commutator Q = ⊤ := by
    rw [commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hab : commutator Q = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b)
    have htop : (⊤ : Subgroup Q) = ⊥ := hcomm.symm.trans hab
    obtain ⟨a, b, hab'⟩ := (IsSimpleGroup.toNontrivial (G := Q)).exists_pair_ne
    exact hab' ((Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top a)).trans
      (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top b)).symm)

private theorem assembly_isQuasisimple_of_simple_of_perfect {Q : Type*} [Group Q]
    (hs : IsSimpleGroup Q) (hp : Group.IsPerfect Q) : CFSG.Assembly.IsQuasisimple Q := by
  have hcomm : commutator Q = ⊤ := by
    rw [commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have := hs
  exact ⟨hcomm, ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_simple_of_perfect hs hp)).trans
      (QuotientGroup.quotientBot (G := Q))).isSimpleGroup⟩

variable {G : Type} [Group G] [Finite G] {f : ℕ} {F K : Type} [Field F] [Field K] [Algebra F K]
  [Finite K] [CharP K 2]

omit [Finite G] in
theorem GGSecFiveBPermOmKFrame.isComponentOf_map_normBlock_inf_centralizer_of_subnormal
    {p n r : ℕ} [Fact p.Prime] {E : QuadExt F K (unitaryInvolution K 2 f)} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1) (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {M Y : Subgroup G} (hMX : M ≤ X) (hM : CFSG.Assembly.IsSubnormal M Y) {d : G} (hd : d ∈ Bs)
    (P : Finset (Fin r)) (hP : P.Nonempty) (hPM : (normBlock E r P).map κ ≤ M)
    (hdP : ∀ i, eta ⟨d, hd⟩ (π i.castSucc) = 1 ↔ i ∈ P) :
    CFSG.Assembly.IsComponentOf ((normBlock E r P).map κ) (Y ⊓ Subgroup.centralizer {d}) := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  obtain ⟨hκ, hκX, hχ, hact⟩ := hframe
  obtain ⟨T, hTact, hTconj⟩ := hact ⟨d, hd⟩
  let u : Fin r → Multiplicative (ZMod p) := fun i => eta ⟨d, hd⟩ (π i.castSucc)
  let τ := normPlaneTorus E (by omega : 2 ≤ r) hpq χ
  have hTeq : T = τ u := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [hTact v, normPlaneTorus_apply]
  have hTmem : T ∈ (Subgroup.pi (P : Set (Fin r))
      (fun _ => (⊥ : Subgroup (Multiplicative (ZMod p))))).map τ := by
    rw [hTeq]
    refine Subgroup.mem_map.mpr ⟨u, fun i hi => ?_, rfl⟩
    exact Subgroup.mem_bot.mpr ((hdP i).mpr hi)
  have hblockC : normBlock E r P ≤ Subgroup.centralizer ({T} : Set (normOmega E r)) := by
    have hder := commutator_centralizer_normPlaneTorus_eq_normBlock_of_dvd E hr hpq χ hχ P hP
    intro h hh
    rw [← hder] at hh
    have hhC := Subgroup.commutator_le_self _ hh
    rw [Subgroup.mem_centralizer_iff] at hhC ⊢
    intro t ht
    rw [Set.mem_singleton_iff.mp ht]
    exact hhC T hTmem
  have hnorm : ∀ s : normOmega E r, s * T = T * s →
      s ∈ Subgroup.normalizer (normBlock E r P : Set (normOmega E r)) := by
    intro s hs
    refine mem_normalizer_normBlock_of_commute_planeScalars E P (fun i => (χ (u i) : K))
      hTact (fun i hi => ?_) (fun i hi => ?_) hs
    · intro h1
      apply hi
      apply (hdP i).mp
      apply hχ
      rw [map_one]
      exact Units.ext h1
    · simp only [u, (hdP i).mpr hi, map_one, Units.val_one]
  have hcent : ∀ s : normOmega E r, κ s ∈ Subgroup.centralizer ({d} : Set G) ↔ s * T = T * s := by
    intro s
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : d * κ s * d⁻¹ = κ (T * s * T⁻¹) := hTconj s
    constructor
    · intro h
      have h' : κ (T * s * T⁻¹) = κ s := by
        rw [← hconj, ← h, mul_inv_cancel_right]
      have h'' := hκ h'
      calc s * T = T * s * T⁻¹ * T := by rw [h'']
        _ = T * s := by group
    · intro h
      have h' : d * κ s * d⁻¹ = κ s := by
        rw [hconj]
        congr 1
        rw [← h, mul_inv_cancel_right]
      calc κ s * d = d * κ s * d⁻¹ * d := by rw [h']
        _ = d * κ s := by group
  have hAle : (normBlock E r P).map κ ≤ M ⊓ Subgroup.centralizer ({d} : Set G) := by
    refine le_inf hPM ?_
    rintro _ ⟨h, hh, rfl⟩
    exact (hcent h).mpr
      ((Subgroup.mem_centralizer_iff.mp (hblockC hh) T (Set.mem_singleton T)).symm)
  have hAnormal :
      (((normBlock E r P).map κ).subgroupOf (M ⊓ Subgroup.centralizer ({d} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAle]
    intro m g hm hg
    obtain ⟨hgM, hgC⟩ := hg
    obtain ⟨s, rfl⟩ : g ∈ κ.range := hκX ▸ hMX hgM
    obtain ⟨h, hh, rfl⟩ := hm
    have hsN := hnorm s ((hcent s).mp hgC)
    refine ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN h).mp hh, ?_⟩
    simp only [map_mul, map_inv]
  have hsub : CFSG.Assembly.IsSubnormal ((normBlock E r P).map κ)
      (Y ⊓ Subgroup.centralizer ({d} : Set G)) :=
    CFSG.Assembly.IsSubnormal.step hAle hAnormal (hM.inf _)
  have hsimple : IsSimpleGroup ↥(normBlock E r P) := isSimpleGroup_normBlock E hr P hP
  have hperf : Group.IsPerfect ↥(normBlock E r P) := isPerfect_normBlock E hr P hP
  have hq : CFSG.Assembly.IsQuasisimple ↥(normBlock E r P) :=
    assembly_isQuasisimple_of_simple_of_perfect hsimple hperf
  exact ⟨hsub.le, hsub, CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_map_of_injective hκ hq⟩

omit [Finite G] in
theorem GGSecFiveBPermOmKFrame.isComponentOf_map_normBlock_inf_centralizer
    {p n r : ℕ} [Fact p.Prime] {E : QuadExt F K (unitaryInvolution K 2 f)} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1) (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {Y : Subgroup G} (hX : CFSG.Assembly.IsSubnormal X Y) {d : G} (hd : d ∈ Bs)
    (P : Finset (Fin r)) (hP : P.Nonempty)
    (hdP : ∀ i, eta ⟨d, hd⟩ (π i.castSucc) = 1 ↔ i ∈ P) :
    CFSG.Assembly.IsComponentOf ((normBlock E r P).map κ) (Y ⊓ Subgroup.centralizer {d}) :=
  GGSecFiveBPermOmKFrame.isComponentOf_map_normBlock_inf_centralizer_of_subnormal hr hpq hframe
    le_rfl hX hd P hP
    (by simpa [hframe.2.1] using Subgroup.map_le_range κ (normBlock E r P)) hdP

private theorem normBlock_le_centralizer_normPlaneTorus_of_trivial
    (E : QuadExt F K (unitaryInvolution K 2 f)) {p : ℕ} [Fact p.Prime]
    {r : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1)
    (χ : Multiplicative (ZMod p) →* Kˣ) (hχ : Function.Injective χ)
    (S : Finset (Fin r)) (hS : S.Nonempty)
    {u : Fin r → Multiplicative (ZMod p)} (hu : ∀ i ∈ S, u i = 1) :
    normBlock E r S ≤ Subgroup.centralizer
      ({normPlaneTorus E (by omega : 2 ≤ r) hpq χ u} : Set (normOmega E r)) := by
  classical
  have hder :=
    commutator_centralizer_normPlaneTorus_eq_normBlock_of_dvd E hr hpq χ hχ S hS
  intro h hh
  rw [← hder] at hh
  have hhC := Subgroup.commutator_le_self _ hh
  rw [Subgroup.mem_centralizer_iff] at hhC ⊢
  intro t ht
  rw [Set.mem_singleton_iff.mp ht]
  exact hhC _ (Subgroup.mem_map.mpr
    ⟨u, fun i hi => Subgroup.mem_bot.mpr (hu i hi), rfl⟩)

omit [Finite G] in
theorem GGSecFiveBPermOmKFrame.isComponentOf_map_normBlock_inf_centralizer_of_subset
    {p n r : ℕ} [Fact p.Prime] {E : QuadExt F K (unitaryInvolution K 2 f)} {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f + 1) (hframe : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    {Q : Finset (Fin r)} {Y : Subgroup G}
    (hQ : CFSG.Assembly.IsSubnormal ((normBlock E r Q).map κ) Y) {d : G} (hd : d ∈ Bs)
    (P : Finset (Fin r)) (hP : P.Nonempty) (hPQ : P ⊆ Q)
    (hdP : ∀ i ∈ Q, eta ⟨d, hd⟩ (π i.castSucc) = 1 ↔ i ∈ P) :
    CFSG.Assembly.IsComponentOf ((normBlock E r P).map κ) (Y ⊓ Subgroup.centralizer {d}) := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  obtain ⟨hκ, hκX, hχ, hact⟩ := hframe
  obtain ⟨T, hTact, hTconj⟩ := hact ⟨d, hd⟩
  let u : Fin r → Multiplicative (ZMod p) := fun i => eta ⟨d, hd⟩ (π i.castSucc)
  let τ := normPlaneTorus E (by omega : 2 ≤ r) hpq χ
  have hTeq : T = τ u := by
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    rw [hTact v, normPlaneTorus_apply]
  let P' : Finset (Fin r) := Finset.univ.filter fun i => u i = 1
  have hPP' : P ⊆ P' := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hdP i (hPQ hi)).mpr hi⟩
  have hP'ne : P'.Nonempty := by
    obtain ⟨i, hi⟩ := hP
    exact ⟨i, hPP' hi⟩
  have hblockP : normBlock E r P ≤ Subgroup.centralizer ({T} : Set (normOmega E r)) := by
    have h := normBlock_le_centralizer_normPlaneTorus_of_trivial E hr hpq χ hχ P' hP'ne
      fun i hi => (Finset.mem_filter.mp hi).2
    rw [hTeq]
    exact (normBlock_mono E r hPP').trans h
  have hcent : ∀ s : normOmega E r, κ s ∈ Subgroup.centralizer ({d} : Set G) ↔
      s * T = T * s := by
    intro s
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : d * κ s * d⁻¹ = κ (T * s * T⁻¹) := hTconj s
    constructor
    · intro h
      have h' : κ (T * s * T⁻¹) = κ s := by
        rw [← hconj, ← h, mul_inv_cancel_right]
      have h'' := hκ h'
      calc s * T = T * s * T⁻¹ * T := by rw [h'']
        _ = T * s := by group
    · intro h
      have h' : d * κ s * d⁻¹ = κ s := by
        rw [hconj]
        congr 1
        rw [← h, mul_inv_cancel_right]
      calc κ s * d = d * κ s * d⁻¹ * d := by rw [h']
        _ = d * κ s := by group
  have hnorm : ∀ s : normOmega E r, s ∈ normBlock E r Q → s * T = T * s →
      s ∈ Subgroup.normalizer (normBlock E r P : Set (normOmega E r)) := by
    intro s hsQ hsT
    let u'' : Fin r → Multiplicative (ZMod p) :=
      fun i => if i ∈ Q then u i else Multiplicative.ofAdd 1
    let v : Fin r → Multiplicative (ZMod p) := u'' * u⁻¹
    have huv : u'' = u * v := by
      funext i
      change u'' i = u i * (u'' i * (u i)⁻¹)
      rw [← mul_assoc, mul_comm (u i) (u'' i), mul_assoc, mul_inv_cancel, mul_one]
    have hT''eq : τ u'' = T * τ v := by
      rw [huv, map_mul, ← hTeq]
    have hvQ : ∀ i ∈ Q, v i = 1 := by
      intro i hi
      show (if i ∈ Q then u i else Multiplicative.ofAdd 1) * (u i)⁻¹ = 1
      rw [if_pos hi, mul_inv_cancel]
    let Q' : Finset (Fin r) := Finset.univ.filter fun i => v i = 1
    have hQQ' : Q ⊆ Q' := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvQ i hi⟩
    have hQne : Q.Nonempty := by
      obtain ⟨i, hi⟩ := hP
      exact ⟨i, hPQ hi⟩
    have hQ'ne : Q'.Nonempty := by
      obtain ⟨i, hi⟩ := hQne
      exact ⟨i, hQQ' hi⟩
    have hCv : normBlock E r Q ≤ Subgroup.centralizer ({τ v} : Set (normOmega E r)) :=
      (normBlock_mono E r hQQ').trans
        (normBlock_le_centralizer_normPlaneTorus_of_trivial E hr hpq χ hχ Q' hQ'ne
          fun i hi => (Finset.mem_filter.mp hi).2)
    have hsCv : s * τ v = τ v * s :=
      (Subgroup.mem_centralizer_iff.mp (hCv hsQ) (τ v) (Set.mem_singleton (τ v))).symm
    have hsT'' : s * τ u'' = τ u'' * s := by
      rw [hT''eq]
      calc s * (T * τ v) = (s * T) * τ v := (mul_assoc _ _ _).symm
        _ = (T * s) * τ v := by rw [hsT]
        _ = T * (s * τ v) := mul_assoc _ _ _
        _ = T * (τ v * s) := by rw [hsCv]
        _ = (T * τ v) * s := (mul_assoc _ _ _).symm
    have hT''act : ∀ w : (F × F) × (Fin r → K),
        (τ u'' : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))) w =
          (w.1, fun i => (χ (u'' i) : K) * w.2 i) :=
      normPlaneTorus_apply E (by omega : 2 ≤ r) hpq χ u''
    refine mem_normalizer_normBlock_of_commute_planeScalars E P
      (fun i => (χ (u'' i) : K)) hT''act ?_ ?_ hsT''
    ·
      intro i hi h1
      have hχeq : χ (u'' i) = 1 := Units.ext h1
      have hu''1 : u'' i = 1 := hχ (by rw [hχeq, map_one])
      by_cases hiQ : i ∈ Q
      · have hu1 : u i = 1 := by simpa [u'', hiQ] using hu''1
        exact hi ((hdP i hiQ).mp hu1)
      · have hof : u'' i = Multiplicative.ofAdd 1 := by simp [u'', hiQ]
        rw [hof] at hu''1
        have h10 : (1 : ZMod p) = 0 := by
          simpa using congrArg Multiplicative.toAdd hu''1
        exact one_ne_zero h10
    · intro i hi
      have hiQ : i ∈ Q := hPQ hi
      have hu1 : u i = 1 := (hdP i hiQ).mpr hi
      have hu''1 : u'' i = 1 := by simpa [u'', hiQ] using hu1
      simp [hu''1]
  set M : Subgroup G := (normBlock E r P).map κ with hM
  have hMle : M ≤ (normBlock E r Q).map κ ⊓ Subgroup.centralizer ({d} : Set G) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨Subgroup.mem_map_of_mem κ ((normBlock_mono E r hPQ) hh), ?_⟩
    exact (hcent h).mpr
      (Subgroup.mem_centralizer_iff.mp (hblockP hh) T (Set.mem_singleton T)).symm
  have hMnormal : (M.subgroupOf ((normBlock E r Q).map κ ⊓
      Subgroup.centralizer ({d} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMle]
    intro m g hm hg
    obtain ⟨hgQ, hgC⟩ := hg
    obtain ⟨s, hsQ, rfl⟩ := Subgroup.mem_map.mp hgQ
    obtain ⟨h, hh, rfl⟩ := hm
    have hsT : s * T = T * s := (hcent s).mp hgC
    have hsN := hnorm s hsQ hsT
    refine ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN h).mp hh, ?_⟩
    simp only [map_mul, map_inv]
  have hsub : CFSG.Assembly.IsSubnormal M (Y ⊓ Subgroup.centralizer ({d} : Set G)) :=
    CFSG.Assembly.IsSubnormal.step hMle hMnormal (hQ.inf _)
  have hsimple : IsSimpleGroup ↥(normBlock E r P) := isSimpleGroup_normBlock E hr P hP
  have hperf : Group.IsPerfect ↥(normBlock E r P) := isPerfect_normBlock E hr P hP
  have hq : CFSG.Assembly.IsQuasisimple ↥(normBlock E r P) :=
    assembly_isQuasisimple_of_simple_of_perfect hsimple hperf
  exact ⟨hsub.le, hsub,
    CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_map_of_injective hκ hq⟩

omit [Finite G] in
private theorem isComponentOf_map_conj_aux {L K : Subgroup G}
    (h : CFSG.Assembly.IsComponentOf L K) (g : G) :
    CFSG.Assembly.IsComponentOf (L.map (MulAut.conj g).toMonoidHom)
      (K.map (MulAut.conj g).toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map _,
    CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_map_of_injective (MulAut.conj g).injective
      h.2.2⟩

private theorem eq_closure_pair_of_card_sq {p : ℕ} (hp : p.Prime) {D : Subgroup G}
    (hD : Nat.card D = p ^ 2) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hxp : Nat.card (Subgroup.zpowers x) = p) (hyx : y ∉ Subgroup.zpowers x) :
    D = Subgroup.closure {x, y} := by
  have hle : Subgroup.closure {x, y} ≤ D := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff.mp hz]
      exact hy
  have hxC : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hyC : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  have hlt : Subgroup.zpowers x < Subgroup.closure {x, y} := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hxC) ?_
    intro h
    exact hyx (h ▸ hyC)
  have hcardlt : p < Nat.card (Subgroup.closure ({x, y} : Set G)) :=
    hxp ▸ Subgroup.card_lt_of_lt hlt
  have hdvd : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ p ^ 2 :=
    hD ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk2 : k = 2 := by
    interval_cases k
    · rw [hk', pow_zero] at hcardlt
      exact absurd hcardlt (by have := hp.one_lt; omega)
    · rw [hk', pow_one] at hcardlt
      exact absurd hcardlt (lt_irrefl p)
    · rfl
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hD, hk', hk2])).symm

private theorem GGSecFiveBPermOmKFrame.mem_map_normBlock_of_coords
    {E : QuadExt F K (unitaryInvolution K 2 1)} {B Bs L D J : Subgroup G} {x : G} {n r : ℕ}
    (hr : 3 ≤ r) (hcfg : GGConfig 3 B Bs x L D J) (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0) {κ : normOmega E r →* G}
    {χ : Multiplicative (ZMod 3) →* Kˣ} (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    (P : Finset (Fin r)) {z : G} (hz : z ∈ Bs) (hz0 : eta ⟨z, hz⟩ i0 = 1)
    (hzP : ∀ i : Fin r, i ∉ P → eta ⟨z, hz⟩ (π i.castSucc) = 1) :
    z ∈ (normBlock E r P).map κ := by
  classical
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  let u : Fin r → Multiplicative (ZMod 3) := fun i => eta ⟨z, hz⟩ (π i.castSucc)
  let t := normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ u
  have htB : κ t ∈ Bs := hframe.normPlaneTorus_mem_Bs (by omega) hSC u
  have hzt : z = κ t := by
    have heq : (⟨z, hz⟩ : ↥Bs) = ⟨κ t, htB⟩ := by
      apply eta.injective
      funext j
      by_cases hj : j = i0
      · subst hj
        rw [hz0]
        exact (hframe.normPlaneTorus_coord_last hr hcfg hZ hN hLeta u).symm
      · have hjl : π.symm j ≠ Fin.last r := by
          intro h
          apply hj
          rw [← hpi, ← h, Equiv.apply_symm_apply]
        let i : Fin r := (π.symm j).castPred hjl
        have hi : π i.castSucc = j := by
          simp only [i, Fin.castSucc_castPred, Equiv.apply_symm_apply]
        rw [← hi]
        exact (hframe.coords_normPlaneTorus (by omega) hSC u i).symm
    exact congrArg Subtype.val heq
  rw [hzt]
  exact Subgroup.mem_map_of_mem κ (normPlaneTorus_mem_normBlock_of_support E (by omega) χ P u hzP)

omit [Finite G] in
open scoped MatrixGroups in
theorem exists_sl2Hom_of_mem_map_normBlock_singleton
    (E : QuadExt F K (unitaryInvolution K 2 f)) (hF : Nat.card F = 2) {r : ℕ} (hr : 3 ≤ r)
    (c : Fin r) {κ : normOmega E r →* G} (hκ : Function.Injective κ) {e : G}
    (he : e ∈ (normBlock E r {c}).map κ) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    ∃ (E' : Type) (_ : Field E') (_ : Fintype E') (_ : CharP E' 2) (ψ : SL(2, E') →* G)
      (lam : E'ˣ) (t : SL(2, E')), Function.Injective ψ ∧ ψ.range = (normBlock E r {c}).map κ ∧
        orderOf lam = 3 ∧ IsConj t (CFSG.LocalAnalysis.ComponentInitial.sl2Diag E' lam) ∧
          ψ t = e := by
  classical
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  obtain ⟨e1⟩ := nonempty_normOmega_mulEquiv_normBlock E hr ({c} : Finset (Fin r))
  rw [Finset.card_singleton] at e1
  obtain ⟨b, c₀, hirr⟩ := CFSG.GroupTheory.WeirSylow.exists_irreducible_quadratic F
  obtain ⟨e2⟩ := nonempty_normOmega_mulEquiv_minus E (by decide : Odd 1) hirr
  obtain ⟨E', hE', hE'fin, hcard, ⟨e3⟩⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_two_mulEquiv (K := F) (b := b)
      (c := c₀) hirr
  let : Field E' := hE'
  let : Fintype E' := Fintype.ofFinite E'
  have hcard4 : Fintype.card E' = 2 ^ 2 := by
    rw [Fintype.card_eq_nat_card, hcard, hF]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E' 2 := charP_of_card_eq_prime_pow hcard4
  let e4 := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 E'
  let Φ : SL(2, E') ≃* ↥(normBlock E r {c}) := ((e4.trans e3.symm).trans e2.symm).trans e1
  let ψ : SL(2, E') →* G := (κ.comp (normBlock E r {c}).subtype).comp Φ.toMonoidHom
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply Φ.injective
    apply Subtype.ext
    exact hκ hab
  have hrange : ψ.range = (normBlock E r {c}).map κ := by
    ext g
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(Φ a : normOmega E r), (Φ a).2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨Φ.symm ⟨h, hh⟩, ?_⟩
      simp [ψ]
  obtain ⟨h, hh, rfl⟩ := he
  let t : SL(2, E') := Φ.symm ⟨h, hh⟩
  have hψt : ψ t = κ h := by simp [ψ, t]
  have ht3 : t ^ 3 = 1 := hψinj (by rw [map_pow, hψt, he3, map_one])
  have ht1 : t ≠ 1 := fun h1 => he1 (by rw [← hψt, h1, map_one])
  have hunits : Fintype.card E'ˣ = 3 := by
    rw [Fintype.card_units, hcard4]
    norm_num
  have : Nontrivial E'ˣ := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hunits]; norm_num)
  obtain ⟨lam, hlam1⟩ := exists_ne (1 : E'ˣ)
  have hlam : orderOf lam = 3 := by
    have hdvd : orderOf lam ∣ 3 := hunits ▸ orderOf_dvd_card
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hlam1
    · exact h1
  have hDord : orderOf (CFSG.LocalAnalysis.ComponentInitial.sl2Diag E' lam) = 3 := by
    rw [CFSG.orderOf_sl2Diag_eq, hlam]
  have hD3 : (CFSG.LocalAnalysis.ComponentInitial.sl2Diag E' lam) ^ 3 = 1 := by
    rw [← hDord]
    exact pow_orderOf_eq_one _
  have hD1 : CFSG.LocalAnalysis.ComponentInitial.sl2Diag E' lam ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hDord
    norm_num at hDord
  obtain ⟨x1, hx1⟩ := CFSG.RankThree.PartTwo.Sec12.Hering129D4H.sl2_exists_conj_sl2Three ht3 ht1
  obtain ⟨x2, hx2⟩ := CFSG.RankThree.PartTwo.Sec12.Hering129D4H.sl2_exists_conj_sl2Three hD3 hD1
  refine ⟨E', hE', inferInstance, inferInstance, ψ, lam, t, hψinj, hrange, hlam,
    isConj_iff.mpr ⟨x2⁻¹ * x1, ?_⟩, hψt⟩
  calc x2⁻¹ * x1 * t * (x2⁻¹ * x1)⁻¹ = x2⁻¹ * (x1 * t * x1⁻¹) * x2 := by group
    _ = x2⁻¹ * (x2 * CFSG.LocalAnalysis.ComponentInitial.sl2Diag E' lam * x2⁻¹) * x2 := by
        rw [hx1, hx2]
    _ = CFSG.LocalAnalysis.ComponentInitial.sl2Diag E' lam := by group

omit [Finite G] in
private theorem center_map_eq_bot_of_simple_of_perfect {X : Type*} [Group X] {H : Subgroup X}
    {κ : X →* G} (hκ : Function.Injective κ) (hs : IsSimpleGroup ↥H)
    (hp : Group.IsPerfect ↥H) : Subgroup.center ↥(H.map κ) = ⊥ := by
  let e : ↥H ≃* ↥(H.map κ) := Subgroup.equivMapOfInjective H κ hκ
  have := hs
  have := hp
  exact center_eq_bot_of_simple_of_perfect e.symm.isSimpleGroup
    (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

private theorem lab_eq_twD_four_one {lab : CFSG.Assembly.LargeEvenLabel}
    (h : GGSecFiveBCoordBLabel 4 3 lab ∧ (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) :
    lab = ⟨.twD, 4, 1⟩ := by
  obtain ⟨t, l, m⟩ := lab
  obtain ⟨hlab, hn1, htag⟩ := h
  simp only at hn1 htag
  subst hn1
  unfold GGSecFiveBCoordBLabel at hlab
  simp only at hlab
  rcases htag with rfl | rfl
  · rcases hlab with ⟨h', -⟩ | ⟨-, hl, -⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · rcases h' with h' | h' <;> cases h'
    · rw [hl]
    · cases h'
    · cases h'
  · rcases hlab with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, -, hodd, -⟩ | ⟨h', -⟩
    · rcases h' with h' | h' <;> cases h'
    · cases h'
    · exact absurd hodd (by decide)
    · cases h'

private theorem GGConfig.exists_eq_coordZeroOn_pair_of_sparse {B Bs L D J : Subgroup G} {x : G}
    (hcfg : GGConfig 3 B Bs x L D J) (hB : B = Bs) {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n)
    (hLB : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hsp : GGSecFiveBCoordSparse eta i0 D) :
    ∃ c : Fin n, c ≠ i0 ∧ D = ggBsCoordZeroOn Bs eta ({i0, c} : Set (Fin n))ᶜ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hxBs : x ∈ Bs := hB ▸ hxB
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hxB
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hDB : D ≤ Bs := hB ▸ hcfg.2.2.1.1
  have hDcard : Nat.card D = 3 ^ 2 := hcfg.2.2.1.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hxoff : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock Nat.prime_three (by norm_num) hxBs hLx eta i0 hLB
  have hxi0 : eta ⟨x, hxBs⟩ i0 ≠ 1 := by
    intro h
    apply hx1
    have h1 : eta ⟨x, hxBs⟩ = 1 := by
      funext k
      by_cases hk : k = i0
      · rw [hk, h]
        rfl
      · exact hxoff k hk
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff eta).1 h1)
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  obtain ⟨w, hwD, hwx⟩ : ∃ w ∈ D, w ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from h)
    rw [hDcard, hxcard] at hle
    norm_num at hle
  have hwBs : w ∈ Bs := hDB hwD
  have hcard3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card (g' := (eta ⟨w, hwBs⟩ i0)⁻¹) hcard3 hxi0)
  obtain ⟨z, hz⟩ : ∃ z, z = w * x ^ k := ⟨_, rfl⟩
  have hzD : z ∈ D := hz ▸ D.mul_mem hwD (D.zpow_mem hxD k)
  have hzBs : z ∈ Bs := hDB hzD
  have hzeq : (⟨z, hzBs⟩ : ↥Bs) = ⟨w, hwBs⟩ * ⟨x, hxBs⟩ ^ k := Subtype.ext (by simp [hz])
  have hzi0 : eta ⟨z, hzBs⟩ i0 = 1 := by
    rw [hzeq, map_mul, map_zpow, Pi.mul_apply, Pi.pow_apply, hk, mul_inv_cancel]
  have hzx : z ∉ Subgroup.zpowers x := by
    intro h
    apply hwx
    have hw : w = z * x ^ (-k) := by
      rw [hz, zpow_neg]
      group
    rw [hw]
    exact (Subgroup.zpowers x).mul_mem h (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _)
  have hz1 : z ≠ 1 := fun h => hzx (h ▸ (Subgroup.zpowers x).one_mem)
  obtain ⟨c, hc0, hzoff'⟩ := hsp ⟨z, hzBs⟩ hzD (fun h => hz1 (congrArg Subtype.val h)) hzi0
  have hzoff : ∀ j, j ≠ c → eta ⟨z, hzBs⟩ j = 1 := by
    intro j hj
    by_cases hj0 : j = i0
    · rw [hj0]
      exact hzi0
    · exact hzoff' j hj0 hj
  have hzc : eta ⟨z, hzBs⟩ c ≠ 1 := by
    intro h
    apply hz1
    have h1 : eta ⟨z, hzBs⟩ = 1 := by
      funext j
      by_cases hj : j = c
      · rw [hj, h]
        rfl
      · exact hzoff j hj
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff eta).1 h1)
  refine ⟨c, hc0, ?_⟩
  rw [ggBsCoordZeroOn_pair_compl_eq_sup_zpowers eta hxBs hzBs hc0.symm hxi0 hzc hxoff hzoff,
    eq_closure_pair_of_card_sq Nat.prime_three hDcard hxD hzD hxcard hzx, Set.insert_eq,
    Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]

private theorem image_castSucc_erase_eq_compl_pair {n r : ℕ} (π : Fin (r + 1) ≃ Fin n)
    {i0 c : Fin n} (hpi : π (Fin.last r) = i0) {ic : Fin r} (hic : π ic.castSucc = c) :
    (fun i : Fin r => π i.castSucc) '' ((Finset.univ.erase ic : Finset (Fin r)) : Set (Fin r)) =
      ({i0, c} : Set (Fin n))ᶜ := by
  ext j
  simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_image, Set.mem_diff, Set.mem_univ,
    Set.mem_singleton_iff, true_and, Set.mem_compl_iff, Set.mem_insert_iff, not_or]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨fun h => Fin.castSucc_ne_last i (π.injective (h.trans hpi.symm)), fun h => hi ?_⟩
    exact Fin.castSucc_injective _ (π.injective (h.trans hic.symm))
  · rintro ⟨hj0, hjc⟩
    have hl : π.symm j ≠ Fin.last r := fun h => hj0 (by rw [← hpi, ← h, Equiv.apply_symm_apply])
    refine ⟨(π.symm j).castPred hl, fun h => hjc ?_, by simp⟩
    rw [← hic, ← h]
    simp

private theorem GGSecFiveBPermOmKFrame.eq_map_normBlock_of_eq_coordZeroOn
    {E : QuadExt F K (unitaryInvolution K 2 1)} (hF : Nat.card F = 2)
    {B Bs L D J : Subgroup G} {x : G} {n r : ℕ} (hr : 3 ≤ r) (hcfg : GGConfig 3 B Bs x L D J)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ) (P : Finset (Fin r))
    (hP : P.card = 1 ∨ P.card = 2) (hPu : P ≠ Finset.univ)
    (hD : D = ggBsCoordZeroOn Bs eta ((fun i : Fin r => π i.castSucc) '' (P : Set (Fin r)))) :
    J = (normBlock E r P).map κ := by
  have hPne : P.Nonempty := Finset.card_pos.mp (by omega)
  have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hLD := hframe.inf_centralizer_coordZeroOn_eq_map (by omega) (by norm_num : 3 ∣ 2 ^ 1 + 1) P
  rw [← hD] at hLD
  have hcomm : ⁅Subgroup.centralizer (((Subgroup.pi (P : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod 3))))).map
          (normPlaneTorus E (by omega) (by norm_num : 3 ∣ 2 ^ 1 + 1) χ)) : Set (normOmega E r)),
      Subgroup.centralizer (((Subgroup.pi (P : Set (Fin r))
        (fun _ => (⊥ : Subgroup (Multiplicative (ZMod 3))))).map
          (normPlaneTorus E (by omega) (by norm_num : 3 ∣ 2 ^ 1 + 1) χ)) : Set (normOmega E r))⁆ =
      normBlock E r P :=
    commutator_centralizer_normPlaneTorus_eq_normBlock E hF hr χ hframe.2.2.1 P hP hPu
  have hXX : ⁅L ⊓ Subgroup.centralizer (D : Set G), L ⊓ Subgroup.centralizer (D : Set G)⁆ =
      (normBlock E r P).map κ := by
    rw [hLD, ← Subgroup.map_commutator, hcomm]
  have hs : IsSimpleGroup ↥(⁅L ⊓ Subgroup.centralizer (D : Set G),
      L ⊓ Subgroup.centralizer (D : Set G)⁆ : Subgroup G) := by
    rw [hXX]
    have := isSimpleGroup_normBlock E hr P hPne
    exact (Subgroup.equivMapOfInjective _ κ hframe.1).symm.isSimpleGroup
  exact (ggComponent_eq_commutator hJc hs).trans hXX

section Context

theorem GGSecFiveRouteCfg.isComponentOf_ggBlockComm_centralizer_of_qTwoOrth_four
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLB : GGLBalanceInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))) (i0 : Fin 4)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L)
    (hAll : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (S : Finset (Fin 4)) (hS : S.card = 2) {d : G} (hd : d ∈ Bs)
    (hdS : ∀ c ∈ S, eta ⟨d, hd⟩ c = 1) (hdSc : ∀ c ∉ S, eta ⟨d, hd⟩ c ≠ 1) :
    CFSG.Assembly.IsComponentOf (ggBlockComm Bs eta (S : Set (Fin 4)))
      (Subgroup.centralizer {d}) := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨rfl, hZ, hN, F, K, _, _, _, _, _, E, hF2, π, hpi, κ, χ, hframe⟩ :=
    exists_omKFrame_of_qTwoOrth hcfg (le_refl 4) eta hL hLab
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : 3 ≤ 4 - 1 := by norm_num
  have hS3 : CFSG.Assembly.LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS3.2.1
  have hxBs : x ∈ Bs := hB ▸ hxB
  have hx3 : x ^ 3 = 1 := hS3.1.1.2 x hxB
  have hx1 : x ≠ 1 := hS3.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS3.2.2.2.1.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hBsEA := hcfg.2.1.2.1
  have hxoff : ∀ k, k ≠ i0 → eta ⟨x, hxBs⟩ k = 1 :=
    ggBs_coord_eq_one_of_mem_bCoordinateBlock Nat.prime_three (by norm_num) hxBs hLx eta i0 hL
  have hLabT : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twD, 4, 1⟩) 3 Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨lab_eq_twD_four_one hP.1, hP.2⟩) hLab
  obtain ⟨hsp, -⟩ := hcfg.bCoordSparse_and_J_label_of_twD_four_one hRig hB eta i0 hL hLabT
  obtain ⟨c, hc0, hDeq⟩ := hcfg.exists_eq_coordZeroOn_pair_of_sparse hB eta i0 hL hsp
  have hcl : π.symm c ≠ Fin.last (4 - 1) := fun h =>
    hc0 (by rw [← hpi, ← h, Equiv.apply_symm_apply])
  obtain ⟨ic, hic⟩ : ∃ ic : Fin (4 - 1), π ic.castSucc = c := ⟨(π.symm c).castPred hcl, by simp⟩
  obtain ⟨Sab, hSab_def⟩ : ∃ Sab : Finset (Fin (4 - 1)), Sab = Finset.univ.erase ic := ⟨_, rfl⟩
  have hSab2 : Sab.card = 2 := by
    rw [hSab_def, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hSabu : Sab ≠ Finset.univ := by
    intro h
    have hmem := Finset.notMem_erase ic (Finset.univ : Finset (Fin (4 - 1)))
    rw [← hSab_def, h] at hmem
    exact hmem (Finset.mem_univ ic)
  have hS₀ : (fun i : Fin (4 - 1) => π i.castSucc) '' (Sab : Set (Fin (4 - 1))) =
      ({i0, c} : Set (Fin 4))ᶜ := by
    rw [hSab_def]
    exact image_castSucc_erase_eq_compl_pair π hpi hic
  have hDS : D = ggBsCoordZeroOn Bs eta
      ((fun i : Fin (4 - 1) => π i.castSucc) '' (Sab : Set (Fin (4 - 1)))) := by
    rw [hS₀]
    exact hDeq
  have hJeq : J = (normBlock E (4 - 1) Sab).map κ :=
    hframe.eq_map_normBlock_of_eq_coordZeroOn hF2 hr hcfg Sab (Or.inr hSab2) hSabu hDS
  have hJblk : J = ggBlockComm Bs eta ({i0, c} : Set (Fin 4))ᶜ := by
    rw [hJeq, ← hframe.blockComm hF2 hr hcfg hZ hN hL hpi Sab (Or.inr hSab2), hS₀]
  obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp hSab2
  have haS : a ∈ Sab := by
    rw [hSab]
    simp
  have hbS : b ∈ Sab := by
    rw [hSab]
    simp
  have haic : a ≠ ic := by
    rw [hSab_def] at haS
    exact Finset.ne_of_mem_erase haS
  have hbic : b ≠ ic := by
    rw [hSab_def] at hbS
    exact Finset.ne_of_mem_erase hbS
  have hcases : ∀ i : Fin (4 - 1), i = a ∨ i = b ∨ i = ic := by
    intro i
    by_cases hi : i = ic
    · exact Or.inr (Or.inr hi)
    · have hiS : i ∈ Sab := by
        rw [hSab_def]
        exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      rw [hSab] at hiS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiS
      tauto
  obtain ⟨ca, hca⟩ : ∃ ca, π a.castSucc = ca := ⟨_, rfl⟩
  obtain ⟨cb, hcb⟩ : ∃ cb, π b.castSucc = cb := ⟨_, rfl⟩
  have hca0 : ca ≠ i0 := by
    rw [← hca, ← hpi]
    exact fun h => Fin.castSucc_ne_last a (π.injective h)
  have hcb0 : cb ≠ i0 := by
    rw [← hcb, ← hpi]
    exact fun h => Fin.castSucc_ne_last b (π.injective h)
  have hcac : ca ≠ c := by
    rw [← hca, ← hic]
    exact fun h => haic (Fin.castSucc_injective _ (π.injective h))
  have hcbc : cb ≠ c := by
    rw [← hcb, ← hic]
    exact fun h => hbic (Fin.castSucc_injective _ (π.injective h))
  have hcab : ca ≠ cb := by
    rw [← hca, ← hcb]
    exact fun h => hab (Fin.castSucc_injective _ (π.injective h))
  have hScard : Sᶜ.card = 2 := by
    rw [Finset.card_compl, hS]
    simp
  have hcard : Fintype.card {j // j ∈ ({i0, c} : Finset (Fin 4))} =
      Fintype.card {j // j ∈ Sᶜ} := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_pair hc0.symm, hScard]
  let τ : Equiv.Perm (Fin 4) := (Fintype.equivOfCardEq hcard).extendSubtype
  have hτin : ∀ j, j ∈ ({i0, c} : Finset (Fin 4)) → τ j ∉ S := fun j hj =>
    Finset.mem_compl.mp (Equiv.extendSubtype_mem _ j hj)
  have hτout : ∀ j, j ∉ ({i0, c} : Finset (Fin 4)) → τ j ∈ S := fun j hj => by
    have h := Equiv.extendSubtype_not_mem (Fintype.equivOfCardEq hcard) j hj
    simpa [Finset.mem_compl] using h
  have hτS : τ '' (({i0, c} : Set (Fin 4))ᶜ) = (S : Set (Fin 4)) := by
    ext s
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hτout j (by simpa using hj)
    · intro hs
      refine ⟨τ.symm s, ?_, τ.apply_symm_apply s⟩
      intro hj
      have h := hτin (τ.symm s) (by simpa using hj)
      rw [Equiv.apply_symm_apply] at h
      exact h hs
  obtain ⟨g, hg, -, hτ⟩ := exists_ggG0_transporter_of_perm h𝒦 hG0 τ
  obtain ⟨d₀, hd₀_def⟩ : ∃ d₀, d₀ = g⁻¹ * d * g := ⟨_, rfl⟩
  have hd₀B : d₀ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hg d₀).mpr
    (by rw [show g * d₀ * g⁻¹ = d by rw [hd₀_def]; group]; exact hd)
  have hd₀conj : ggConjAut Bs hg ⟨d₀, hd₀B⟩ = ⟨d, hd⟩ :=
    Subtype.ext (by
      rw [ggConjAut_apply]
      show g * d₀ * g⁻¹ = d
      rw [hd₀_def]
      group)
  have hd₀coord : ∀ j, eta ⟨d₀, hd₀B⟩ j = eta ⟨d, hd⟩ (τ j) := fun j => by
    rw [← eta_ggConjAut_apply_of_permAut hg hτ ⟨d₀, hd₀B⟩ j, hd₀conj]
  have hd₀off : ∀ j, j ∉ ({i0, c} : Finset (Fin 4)) → eta ⟨d₀, hd₀B⟩ j = 1 := fun j hj => by
    rw [hd₀coord]
    exact hdS _ (hτout j hj)
  have hd₀i0 : eta ⟨d₀, hd₀B⟩ i0 ≠ 1 := by
    rw [hd₀coord]
    exact hdSc _ (hτin i0 (by simp))
  have hd₀c : eta ⟨d₀, hd₀B⟩ c ≠ 1 := by
    rw [hd₀coord]
    exact hdSc _ (hτin c (by simp))
  have hd₀ca : eta ⟨d₀, hd₀B⟩ ca = 1 := hd₀off ca (by simp [hca0, hcac])
  have hd₀cb : eta ⟨d₀, hd₀B⟩ cb = 1 := hd₀off cb (by simp [hcb0, hcbc])
  have hd₀D : d₀ ∈ D := by
    rw [hDeq]
    exact mem_ggBsCoordZeroOn.2 ⟨hd₀B, fun j hj => hd₀off j (by simpa using hj)⟩
  have hd₀1 : d₀ ≠ 1 := by
    intro h
    apply hd₀i0
    have h1 : (⟨d₀, hd₀B⟩ : ↥Bs) = 1 := Subtype.ext h
    rw [h1, map_one, Pi.one_apply]
  have hd₀x : d₀ ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hd₀c
    have h1 : (⟨d₀, hd₀B⟩ : ↥Bs) = ⟨x, hxBs⟩ ^ k := Subtype.ext (by simp [← hk])
    rw [h1, map_zpow, Pi.pow_apply, hxoff c hc0, one_zpow]
  have hDcard : Nat.card D = 3 ^ 2 := hcfg.2.2.1.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hDd₀ : D = Subgroup.closure {x, d₀} :=
    eq_closure_pair_of_card_sq Nat.prime_three hDcard hxD hd₀D hxcard hd₀x
  obtain ⟨w, hw, -, hτw⟩ := exists_ggG0_transporter_of_perm h𝒦 hG0 (Equiv.swap i0 ca)
  have he₁B : w * x * w⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hw x).mp hxBs
  have he₁conj : ggConjAut Bs hw ⟨x, hxBs⟩ = ⟨w * x * w⁻¹, he₁B⟩ :=
    Subtype.ext (ggConjAut_apply Bs hw ⟨x, hxBs⟩)
  have he₁coord : ∀ j, eta ⟨w * x * w⁻¹, he₁B⟩ (Equiv.swap i0 ca j) = eta ⟨x, hxBs⟩ j :=
    fun j => by
      rw [← he₁conj]
      exact eta_ggConjAut_apply_of_permAut hw hτw ⟨x, hxBs⟩ j
  have he₁i0 : eta ⟨w * x * w⁻¹, he₁B⟩ i0 = 1 := by
    have h := he₁coord ca
    rw [Equiv.swap_apply_right] at h
    rw [h]
    exact hxoff ca hca0
  have he₁P : ∀ i : Fin (4 - 1), i ∉ ({a} : Finset (Fin (4 - 1))) →
      eta ⟨w * x * w⁻¹, he₁B⟩ (π i.castSucc) = 1 := by
    intro i hi
    have hia : i ≠ a := by simpa using hi
    have h0 : π i.castSucc ≠ i0 := by
      rw [← hpi]
      exact fun h => Fin.castSucc_ne_last i (π.injective h)
    have h1 : π i.castSucc ≠ ca := by
      rw [← hca]
      exact fun h => hia (Fin.castSucc_injective _ (π.injective h))
    have h := he₁coord (π i.castSucc)
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1] at h
    rw [h]
    exact hxoff _ h0
  have he₁Q₁ : w * x * w⁻¹ ∈ (normBlock E (4 - 1) {a}).map κ :=
    hframe.mem_map_normBlock_of_coords hr hcfg hZ hN hL hpi {a} he₁B he₁i0 he₁P
  have he₁3 : (w * x * w⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have he₁1 : w * x * w⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  obtain ⟨E', _, _, _, ψ, lam, t, -, hψrange, hlam, ht, hψt⟩ :=
    exists_sl2Hom_of_mem_map_normBlock_singleton E hF2 hr a hframe.1 he₁Q₁ he₁3 he₁1
  have hQ₁J : ψ.range ≤ J := by
    rw [hψrange, hJeq]
    exact Subgroup.map_mono (normBlock_mono E (4 - 1) (Finset.singleton_subset_iff.mpr haS))
  have hpJ : 3 ∣ Nat.card J := by
    have h := Subgroup.orderOf_dvd_natCard J (hQ₁J (by rw [hψrange]; exact he₁Q₁))
    rwa [orderOf_eq_prime he₁3 he₁1] at h
  have hJZ : Subgroup.center ↥J = ⊥ := by
    rw [hJeq]
    exact center_map_eq_bot_of_simple_of_perfect hframe.1
      (isSimpleGroup_normBlock E hr Sab ⟨a, haS⟩) (isPerfect_normBlock E hr Sab ⟨a, haS⟩)
  obtain ⟨hA, hJA, hxA, hor⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hLB) hcfg.1 hcfg.2.2 hpJ hDd₀
  have hxc := hor.resolve_left
    (hR.not_nbr_of_two_ne_one_of_eq_one hX hTCJ hRig hTPn hA8 hraw hiso hFC hB (by norm_num) eta
      h𝒦 hAll hd₀B hc0.symm hd₀i0 hd₀c hd₀ca _)
  have hJ := isComponentOf_inf_centralizer_of_stdSub hS3 hcfg.2.2.1 hDd₀
  have hodd := (hcfg.1.2.2.2.2.2.2.2.2.2.2 D J hcfg.2.2).2 d₀ hd₀D hd₀1
  have hframe_w := hframe.conj_transporter hw hτw
  have hXw : CFSG.Assembly.IsSubnormal (L.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({w * x * w⁻¹} : Set G)) := by
    have h := (hS3.2.2.2.1.2.1 : CFSG.Assembly.IsSubnormal L
      (Subgroup.centralizer ({x} : Set G))).map (MulAut.conj w).toMonoidHom
    rw [CFSG.centralizer_singleton_map, MulAut.conj_apply] at h
    exact h
  have hdP : ∀ i : Fin (4 - 1),
      eta ⟨d₀, hd₀B⟩ ((π.trans (Equiv.swap i0 ca)) i.castSucc) = 1 ↔
        i ∈ ({b} : Finset (Fin (4 - 1))) := by
    intro i
    rw [Equiv.trans_apply, Finset.mem_singleton]
    rcases hcases i with rfl | rfl | rfl
    · rw [hca, Equiv.swap_apply_right]
      exact ⟨fun h => absurd h hd₀i0, fun h => absurd h hab⟩
    · rw [hcb, Equiv.swap_apply_of_ne_of_ne hcb0 hcab.symm]
      exact ⟨fun _ => rfl, fun _ => hd₀cb⟩
    · rw [hic, Equiv.swap_apply_of_ne_of_ne hc0 hcac.symm]
      exact ⟨fun h => absurd h hd₀c, fun h => absurd h.symm hbic⟩
  have hQ₂w := hframe_w.isComponentOf_map_normBlock_inf_centralizer hr
    (by norm_num : 3 ∣ 2 ^ 1 + 1) hXw hd₀B {b} (Finset.singleton_nonempty b) hdP
  have hQ₂eq : (normBlock E (4 - 1) {b}).map ((MulAut.conj w).toMonoidHom.comp κ) =
      (normBlock E (4 - 1) {b}).map κ := by
    rw [← Subgroup.map_map, ← hframe.blockComm hF2 hr hcfg hZ hN hL hpi {b}
      (Or.inl (Finset.card_singleton b)), ggBlockComm_map_conj hw hτw]
    congr 1
    simp only [Finset.coe_singleton, Set.image_singleton, hcb,
      Equiv.swap_apply_of_ne_of_ne hcb0 hcab.symm]
  have hQ₂ : CFSG.Assembly.IsComponentOf ((normBlock E (4 - 1) {b}).map κ)
      (Subgroup.centralizer {d₀} ⊓ Subgroup.centralizer {w * x * w⁻¹}) := by
    rw [inf_comm, ← hQ₂eq]
    exact hQ₂w
  have hQ₂J : (normBlock E (4 - 1) {b}).map κ ≤ J := by
    rw [hJeq]
    exact Subgroup.map_mono (normBlock_mono E (4 - 1) (Finset.singleton_subset_iff.mpr hbS))
  obtain ⟨u, hu⟩ : ∃ u : Fin (4 - 1) → Multiplicative (ZMod 3),
      u = Pi.mulSingle b (Multiplicative.ofAdd 1) := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = κ (normPlaneTorus E (by omega : 2 ≤ 4 - 1)
      (by decide : 3 ∣ 2 ^ 1 + 1) χ u) := ⟨_, rfl⟩
  have he₂B : e₂ ∈ Bs := by
    rw [he₂]
    exact hframe.normPlaneTorus_mem_Bs (by omega) hSC u
  have he₂coord : ∀ i, eta ⟨e₂, he₂B⟩ (π i.castSucc) = u i := by
    intro i
    subst he₂
    exact hframe.coords_normPlaneTorus (by omega) hSC u i
  have he₂Q₂ : e₂ ∈ (normBlock E (4 - 1) {b}).map κ := by
    rw [he₂]
    refine Subgroup.mem_map_of_mem κ
      (normPlaneTorus_mem_normBlock_of_support E (by omega) χ {b} u fun i hi => ?_)
    rw [hu]
    exact Pi.mulSingle_eq_of_ne (by simpa using hi) _
  have he₂1 : e₂ ≠ 1 := by
    intro h
    have hne : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by
      rw [Ne, ofAdd_eq_one]
      exact one_ne_zero
    have h1 := he₂coord b
    have h2 : (⟨e₂, he₂B⟩ : ↥Bs) = 1 := Subtype.ext h
    rw [h2, map_one, Pi.one_apply, hu, Pi.mulSingle_eq_same] at h1
    exact hne h1.symm
  have he₂3 : e₂ ^ 3 = 1 := hBsEA.2 e₂ he₂B
  have hC : Subgroup.zpowers e₂ ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr he₂1
  have hCp : IsPGroup 3 (Subgroup.zpowers e₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime he₂3 he₂1, pow_one])
  have hCQ₂ : Subgroup.zpowers e₂ ≤ (normBlock E (4 - 1) {b}).map κ :=
    Subgroup.zpowers_le.mpr he₂Q₂
  have he₂Ha : e₂ ∈ ggBsCoordZeroOn Bs eta ((fun i : Fin (4 - 1) => π i.castSucc) ''
      ((({a} : Finset (Fin (4 - 1)))) : Set (Fin (4 - 1)))) := by
    refine mem_ggBsCoordZeroOn.2 ⟨he₂B, ?_⟩
    rintro _ ⟨i, hi, rfl⟩
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hi
    subst hi
    rw [he₂coord, hu]
    exact Pi.mulSingle_eq_of_ne hab _
  have hQ₁C : ∀ a' ∈ ψ.range, ∀ b' ∈ Subgroup.zpowers e₂, a' * b' = b' * a' := by
    intro a' ha' b' hb'
    rw [hψrange, ← hframe.blockComm hF2 hr hcfg hZ hN hL hpi {a}
      (Or.inl (Finset.card_singleton a))] at ha'
    have hb'H := (Subgroup.zpowers_le.mpr he₂Ha) hb'
    exact ((Subgroup.mem_centralizer_iff.mp
      (ggBlockComm_le_centralizer Bs eta _ ha')) b' hb'H).symm
  obtain ⟨-, hJd₀⟩ := ggPComponent_eq_of_oddRadical_of_SL2_of_pGroup ψ lam hlam t ht hψt hA hJA
    hJ hpJ hJZ hxA hx3 hxc hodd hQ₁J hQ₂J hQ₂ hCQ₂ hC hCp hQ₁C
  have hfin := isComponentOf_map_conj_aux hJd₀ g
  rw [hJblk, ggBlockComm_map_conj hg hτ, hτS, CFSG.centralizer_singleton_map] at hfin
  have hgd : (MulAut.conj g) d₀ = d := by
    rw [MulAut.conj_apply, hd₀_def]
    group
  rw [hgd] at hfin
  exact hfin

end Context

end CFSG.StandardType

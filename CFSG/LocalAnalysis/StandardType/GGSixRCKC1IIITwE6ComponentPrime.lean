module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6Components
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagTwE6Model
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import CFSG.LargeExtraspecial.A2ModFrFLie
import CFSG.ClassicalInvolution.Orders.Twisted
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Cover
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.HardMathSupport.Dickson.I271.SporGen
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoComp
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StepGen
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Exceptional
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.StandardType.GGK0MarkedArithmetic
open CFSG.HardMathSupport.Dickson.I271


theorem not_mem_centralizer_of_twistedE6_label_row_III
    {X : Type} [Group X] [Finite X] {K J : Subgroup X} {d : X}
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) :
    d ∉ Subgroup.centralizer (K : Set X) := by
  classical
  intro hd
  have hKle : K ≤ Subgroup.centralizer ({d} : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (Subgroup.mem_centralizer_iff.mp hd k hk).symm
  have hinf : K ⊓ Subgroup.centralizer ({d} : Set X) = K := inf_eq_left.mpr hKle
  have hJcompK : IsComponentOf J K := by
    rw [← hinf]
    exact hJcomp
  have hJsub : (J.subgroupOf K).IsSubnormal :=
    CFSG.Assembly.IsSubnormal.subgroupOf hJcompK.2.1
  have hKqN : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp hKq
  have hJeqK : J = K := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKqN hJsub with
      htop | hcent
    · exact le_antisymm hJcompK.1 (Subgroup.subgroupOf_eq_top.mp htop)
    · exfalso
      have hJperf : Group.IsPerfect ↥J := Group.isPerfect_def.2 hJcompK.2.2.1
      have hJqNat : CFSG.IsQuasisimple ↥J :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).mp
          hJcompK.2.2
      have hJnt : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJqNat
      have hJcomm : IsMulCommutative ↥J := by
        refine ⟨⟨fun a b => ?_⟩⟩
        apply Subtype.ext
        show (a : X) * (b : X) = (b : X) * (a : X)
        have ha : (⟨(a : X), hJcompK.1 a.2⟩ : ↥K) ∈ Subgroup.center ↥K :=
          hcent (Subgroup.mem_subgroupOf.mpr a.2)
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp ha ⟨(b : X), hJcompK.1 b.2⟩).symm
      exact (Group.IsPerfect.not_isMulCommutative ↥J) hJcomm
  have hrowK : GGSixRCKJRow .III K := by
    rw [← hJeqK]
    exact hrow
  obtain ⟨lab, hLambda, hhas, R, _, I, F, θ, hrowIII⟩ :=
    largeEvenMarking_exists_hasLabel hrowK
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hiso : GGLabelIso (⟨.twE6, 0, 1⟩ : LargeEvenLabel) lab :=
    hrig ⟨.twE6, 0, 1⟩ lab (↥K ⧸ Subgroup.center ↥K)
      (by simp [LargeEvenInLambda2]) hLambda hlab hhas
  have hnotiso : ¬ GGLabelIso (⟨.twE6, 0, 1⟩ : LargeEvenLabel) lab := by
    intro hiso'
    unfold GGLabelIso at hiso'
    rcases hiso' with rfl | h | h | h | h | h | h | h
    · exact absurd hrowIII (by simp [ggSixRCKLabelRow])
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact absurd h.2 (by simp)
  exact hnotiso hiso

theorem pow_three_mul_card_le_of_twistedE6_label_row_III
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B₁ : Subgroup X} {d : X}
    (hp : p.Prime) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) :
    p ^ 3 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) ≤ Nat.card B₁ := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hJK : J ≤ K := hJcomp.1.trans inf_le_left
  have hcent : Subgroup.centralizer (K : Set X) ≤ Subgroup.centralizer (J : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    exact hx y (hJK hy)
  have hAB : B₁ ⊓ Subgroup.centralizer (K : Set X) ≤
      B₁ ⊓ Subgroup.centralizer (J : Set X) := by
    intro x hx
    exact ⟨hx.1, hcent hx.2⟩
  have hdCJ : d ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx2 : x ∈ Subgroup.centralizer ({d} : Set X) := (hJcomp.1 hx).2
    exact (Subgroup.mem_centralizer_iff.mp hx2 d (Set.mem_singleton d)).symm
  have hdBJ : d ∈ B₁ ⊓ Subgroup.centralizer (J : Set X) := ⟨hdB, hdCJ⟩
  have hdA : d ∉ B₁ ⊓ Subgroup.centralizer (K : Set X) := fun hmem =>
    not_mem_centralizer_of_twistedE6_label_row_III hKq hlab hJcomp hrow hmem.2
  have hne : B₁ ⊓ Subgroup.centralizer (K : Set X) ≠
      B₁ ⊓ Subgroup.centralizer (J : Set X) := by
    intro heq
    exact hdA (heq ▸ hdBJ)
  have hBp : IsPGroup p ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) :=
    (hBab.mono inf_le_left).isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hBp
  have hproper : ((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X))) ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp htop))
  have hidx_gt : 1 < ((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X))).index :=
    Subgroup.one_lt_index_of_ne_top hproper
  have hcard_sub : Nat.card ↥(((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))) =
      Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have hmul : Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) =
      Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) *
        (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
          (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index := by
    have h := Subgroup.card_mul_index ((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))
    rw [hcard_sub] at h
    exact h.symm
  have hidx_dvd : (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index ∣
      Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) := by
    rw [hmul]
    exact dvd_mul_left _ _
  have hidx_dvd_pk : (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index ∣ p ^ k := by
    rw [← hk]
    exact hidx_dvd
  have hidx_ne_one : (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index ≠ 1 :=
    ne_of_gt hidx_gt
  obtain ⟨q, hq, hq_dvd⟩ := Nat.exists_prime_and_dvd hidx_ne_one
  have hq_eq : q = p := by
    refine (Nat.prime_dvd_prime_iff_eq hq hp).mp ?_
    exact hq.dvd_of_dvd_pow (hq_dvd.trans hidx_dvd_pk)
  have hp_dvd_index : p ∣ (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index := by
    rw [← hq_eq]
    exact hq_dvd
  have hidx_ge : p ≤ (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
      (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index :=
    Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hidx_dvd_pk (pow_pos hp.pos k)) hp_dvd_index
  have hBge : p * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) ≤
      Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) := by
    calc
      p * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) =
          Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) * p := Nat.mul_comm _ _
      _ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) *
            (((B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf
              (B₁ ⊓ Subgroup.centralizer (J : Set X)))).index :=
          Nat.mul_le_mul_left _ hidx_ge
      _ = Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) := hmul.symm
  calc
    p ^ 3 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) =
        p ^ 2 * (p * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X))) := by ring
    _ ≤ p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) :=
        Nat.mul_le_mul_left _ hBge
    _ ≤ Nat.card B₁ := by simpa using hrank

theorem nonempty_centerQuot_equiv_twistedE6_of_label
    {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    (hoddK : Odd (Nat.card (Subgroup.center ↥K))) :
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1))) := by
  classical
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    (ggQuasisimple_centerQuot hKq).2
  have hM0 : MarkedModel (⟨.twE6, 0, 1⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) :=
    markedModel_of_label (by simp [LargeEvenInLambda2]) hnab hlab
  have hM : LieModel (↥K ⧸ Subgroup.center ↥K) .twistedE6 0 2 1 := by
    simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM0
  obtain ⟨φ, hφrange, hφker⟩ :=
    exists_ggU_cover_of_lieModel_two hKq.1 hoddK
      (by simp [S2MathFi1035Pos.GGPosTag]) hM
  let U := (ggU .twistedE6 0 1).K
  let C0 := ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1))
  let σ : GaloisField 2 2 ≃+* GaloisField 2 2 :=
    iterateFrobeniusEquiv (GaloisField 2 2) 2 1
  have hσ : ∀ c, σ c = c ^ (2 ^ 1) := fun c => iterateFrobeniusEquiv_def _ 2 1 c
  have hσθ : σ.toRingHom = frobQ 2 1 := RingHom.ext fun c => by
    change σ c = frobQ 2 1 c
    rw [hσ, frobQ_apply]
  have hcentC0 : Subgroup.center C0 = ⊥ := by
    change Subgroup.center
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1)) = ⊥
    rw [← hσθ]
    exact center_graphFixedRootGroup_eq_bot (σ := σ.toRingHom) σ.surjective
  obtain ⟨π, hπsurj, hπker, -, -⟩ :=
    LayerSixE.exists_model_twistedE6 (f := 1) (by norm_num)
  let πU : U →* C0 := by
    change twistedE6Group 2 1 →* C0
    exact π
  have hπUsurj : Function.Surjective πU := by
    change Function.Surjective π
    exact hπsurj
  have hπUker : πU.ker ≤ Subgroup.center U := by
    change π.ker ≤ Subgroup.center (twistedE6Group 2 1)
    exact hπker.le
  have hUperf : Group.IsPerfect U := by
    change Group.IsPerfect (twistedE6Group 2 1)
    exact Group.isPerfect_def.2
      (MpStdTwE6.commutator_twistedE6Group (f := 1) (by norm_num))
  let ψG : U →* ↥K := φ.codRestrict K (fun u => by
    rw [← hφrange]
    exact ⟨u, rfl⟩)
  have hψGsurj : Function.Surjective ψG := by
    intro k
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (by rw [hφrange]; exact k.2)
    exact ⟨u, Subtype.ext hu⟩
  have hψGker : ψG.ker ≤ Subgroup.center U := by
    intro u hu
    have hu' : φ u = 1 := by
      simpa [ψG] using congrArg Subtype.val hu
    exact hφker hu'
  let eψ : (U ⧸ Subgroup.center U) ≃* (↥K ⧸ Subgroup.center ↥K) :=
    quotCenterEquivOfCentral ψG hψGsurj hψGker
  let eπ : (U ⧸ Subgroup.center U) ≃* (C0 ⧸ Subgroup.center C0) :=
    quotCenterEquivOfCentral πU hπUsurj hπUker
  let eC0 : (C0 ⧸ Subgroup.center C0) ≃* C0 :=
    (QuotientGroup.quotientMulEquivOfEq hcentC0).trans QuotientGroup.quotientBot
  exact ⟨eψ.symm.trans (eπ.trans eC0)⟩

theorem prime_eq_three_of_twistedE6_label
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B₁ : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBab : IsElemAbelian p B₁) (hdB : d ∈ B₁)
    (hB1K : B₁ ≤ Subgroup.normalizer (K : Set X))
    (hrank : p ^ 2 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B₁)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K))
    (hoddK : Odd (Nat.card (Subgroup.center ↥K)))
    (hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) :
    p = 3 := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  by_cases hp3 : p = 3
  · exact hp3
  exfalso
  have hp5 : 5 ≤ p := by
    by_contra h
    push Not at h
    have h2 : 2 ≤ p := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · norm_num at hp
  have hrf : ¬ p ∣ 1 := by
    intro h
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) h
    omega
  have hpow3 : p ^ 3 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) ≤ Nat.card B₁ :=
    pow_three_mul_card_le_of_twistedE6_label_row_III hp hBab hdB hrank hKq hlab hJcomp hrow
  let C0 := ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1))
  let σ : GaloisField 2 2 ≃+* GaloisField 2 2 :=
    iterateFrobeniusEquiv (GaloisField 2 2) 2 1
  have hσ : ∀ c, σ c = c ^ (2 ^ 1) := fun c => iterateFrobeniusEquiv_def _ 2 1 c
  have hσθ : σ.toRingHom = frobQ 2 1 := RingHom.ext fun c => by
    change σ c = frobQ 2 1 c
    rw [hσ, frobQ_apply]
  have hcentC0 : Subgroup.center C0 = ⊥ := by
    change Subgroup.center
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 2) (frobQ 2 1)) = ⊥
    rw [← hσθ]
    exact center_graphFixedRootGroup_eq_bot (σ := σ.toRingHom) σ.surjective
  obtain ⟨eC⟩ := nonempty_centerQuot_equiv_twistedE6_of_label hKq hlab hoddK
  let incl : ↥B₁ →* ↥(Subgroup.normalizer (K : Set X)) := Subgroup.inclusion hB1K
  let φHom : ↥B₁ →* MulAut ↥K := (K.normalizerMonoidHom).comp incl
  have hφkerC : ∀ b : ↥B₁, φHom b = 1 →
      (b : X) ∈ Subgroup.centralizer (K : Set X) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hfix : (φHom b) ⟨g, hg⟩ = ⟨g, hg⟩ := by rw [hb, MulAut.one_apply]
    have hconj := congrArg Subtype.val hfix
    have hconj' : (b : X) * g * (b : X)⁻¹ = g := by
      simpa [φHom, incl, Subgroup.normalizerMonoidHom_apply_apply_coe] using hconj
    show g * (b : X) = (b : X) * g
    calc
      g * (b : X) = ((b : X) * g * (b : X)⁻¹) * (b : X) := by rw [hconj']
      _ = (b : X) * g := by group
  have hKperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
  let A : Subgroup ↥B₁ := (B₁ ⊓ Subgroup.centralizer (K : Set X)).subgroupOf B₁
  have hAcard : Nat.card ↥A = Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let αHom : ↥B₁ →* MulAut C0 :=
    (MulAut.congr eC).toMonoidHom.comp ((centerQuotientHom ↥K).comp φHom)
  have hαker_le : αHom.ker ≤ A := by
    intro b hb
    have hb1 : (centerQuotientHom ↥K) (φHom b) = 1 := by
      simpa [αHom] using hb
    have hb2 : φHom b = 1 :=
      (centerQuotientHom_injective ↥K) (by rw [hb1, map_one])
    exact Subgroup.mem_subgroupOf.mpr ⟨b.2, hφkerC b hb2⟩
  have hαHom_pow (b : ↥B₁) : αHom b ^ p = 1 := by
    have hbpowX : (b : X) ^ p = 1 := hBab.2 b b.2
    have hbpow : b ^ p = 1 := Subtype.ext (by simpa using hbpowX)
    have hφpow : φHom b ^ p = 1 := by rw [← map_pow, hbpow, map_one]
    have hqpow : ((centerQuotientHom ↥K) (φHom b)) ^ p = 1 := by
      rw [← map_pow, hφpow, map_one]
    calc
      αHom b ^ p = (MulAut.congr eC)
          (((centerQuotientHom ↥K) (φHom b)) ^ p) := by simp [αHom, map_pow]
      _ = 1 := by rw [hqpow, map_one]
  have hinner : ∀ b : ↥B₁,
      αHom b ∈ (MulAut.conj : C0 →* MulAut C0).range := fun b =>
    OutdiagTwE6.mem_inner_of_pow_eq_one (f := 1) (r := p) (by norm_num) hp hp2 hp3 hrf
      (hαHom_pow b)
  let βHom : ↥B₁ →* (MulAut.conj : C0 →* MulAut C0).range := αHom.codRestrict _ hinner
  let eInn : C0 ≃* (MulAut.conj : C0 →* MulAut C0).range :=
    MonoidHom.ofInjective (CFSG.mulAutConj_injective_of_center_eq_bot hcentC0)
  let eta : ↥B₁ →* C0 := eInn.symm.toMonoidHom.comp βHom
  have heta_ker_le : eta.ker ≤ A := by
    intro b hb
    have hbβ : βHom b = 1 := by
      apply eInn.symm.injective
      simpa [eta] using hb
    have hbα : αHom b = 1 := by
      have := congrArg Subtype.val hbβ
      simpa [βHom] using this
    exact hαker_le hbα
  have hAp3 : p ^ 3 ≤ Nat.card eta.range := by
    have hmul := Subgroup.card_ker_mul_card_range eta
    have hkerle : Nat.card eta.ker ≤
        Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) := by
      rw [← hAcard]
      exact Subgroup.card_le_of_le heta_ker_le
    have h1 : p ^ 3 * Nat.card eta.ker ≤
        Nat.card eta.ker * Nat.card eta.range := by
      calc
        p ^ 3 * Nat.card eta.ker ≤
            p ^ 3 * Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) :=
          Nat.mul_le_mul_left _ hkerle
        _ ≤ Nat.card B₁ := hpow3
        _ = Nat.card eta.ker * Nat.card eta.range := hmul.symm
    have h2 : p ^ 3 * Nat.card eta.ker ≤
        Nat.card eta.range * Nat.card eta.ker := by
      calc
        p ^ 3 * Nat.card eta.ker ≤ Nat.card eta.ker * Nat.card eta.range := h1
        _ = Nat.card eta.range * Nat.card eta.ker := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  let Ap : Subgroup C0 := eta.range
  have hApel : IsElemAbelian p Ap :=
    CFSG.StandardType.isElemAbelian_range_of_isElemAbelian hBab eta
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hApel.isPGroup
  have hk3 : 3 ≤ k := by
    refine (Nat.pow_le_pow_iff_right hp.one_lt).mp ?_
    rwa [hk] at hAp3
  have hpowdvd : p ^ 3 ∣ Nat.card Ap := by
    rw [hk]
    exact pow_dvd_pow p hk3
  have hApdvd : Nat.card Ap ∣ Nat.card C0 := by
    simpa using Subgroup.card_dvd_of_le (le_top : Ap ≤ (⊤ : Subgroup C0))
  have hKcard : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hC0card : Nat.card C0 = CFSG.Open.ordTwistedE6 2 :=
    CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 Nat.prime_two (by norm_num)
      hKcard σ.toRingHom hσ
  have hE6dvd : p ^ 3 ∣ CFSG.Open.ordTwistedE6 2 := by
    rw [← hC0card]
    exact hpowdvd.trans hApdvd
  rw [CFSG.LargeExtraspecial.A2Mod.FrF.ordTwistedE6_two_eq] at hE6dvd
  have hp_not_two : ¬ p ∣ 2 ^ 36 := by
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hp_dvd_n : p ∣ 1113694156575 := by
    rcases hp.dvd_mul.mp (dvd_trans (dvd_pow_self p (by norm_num)) hE6dvd) with h | h
    · exact absurd h hp_not_two
    · exact h
  have hfac : 1113694156575 = 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by norm_num
  rw [hfac] at hp_dvd_n
  have hp_cases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
    have h := hp_dvd_n
    rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · rcases hp.dvd_mul.mp h with h | h
              · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
                  (hp.dvd_of_dvd_pow h))
              · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
                  (hp.dvd_of_dvd_pow h)))
            · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
                (hp.dvd_of_dvd_pow h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))))
  rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp3 rfl
  · norm_num at hE6dvd
  · norm_num at hE6dvd
  · norm_num at hE6dvd
  · norm_num at hE6dvd
  · norm_num at hE6dvd
  · norm_num at hE6dvd

end CFSG.StandardType.RCKC1

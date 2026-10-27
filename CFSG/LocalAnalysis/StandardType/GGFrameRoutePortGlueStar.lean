module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Bstar
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Exc
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteEndNormal
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
import CFSG.LocalAnalysis.SeitzReduction.E7PilotOuter
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFusion
import CFSG.Quasithin.Background.A318PC7
import CFSG.LieType.Steinberg.CentralExt.OrthogonalTwoMultiplier
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2PositionFacts
import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteB
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.ChevTwo
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

theorem isCyclic_of_le_centralizer_of_bstar {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {z : G} (hBs : IsElemAbelian 3 Bs) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hsup : Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {S : Subgroup G} (hS : S ≤ Subgroup.centralizer (K : Set G)) (hS3 : IsPGroup 3 S) :
    IsCyclic S := by
  have hz3 : z ^ 3 = 1 := hBs.2 z hz
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
    have h : z ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hker]
      exact Subgroup.mem_zpowers z
    exact h.2
  have hzcard : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3 hz1
  refine CFSG.LocalAnalysis.GLTheoremA.Prop53.isCyclic_of_forall_isCyclic_inf_centralizer
    Nat.prime_three hzK hz1 hz3 (fun R hR hR3 => ?_) hS hS3
  refine CFSG.Quasithin.A318P.isCyclic_of_unique_three hR3 hzcard fun r hr hro => ?_
  have hrz : r ∈ Subgroup.centralizer ({z} : Set G) := (hR hr).1
  have hrK : r ∈ Subgroup.centralizer (K : Set G) := (hR hr).2
  have hr3 : r ^ 3 = 1 := by
    rw [← hro]
    exact pow_orderOf_eq_one r
  have hle : Subgroup.zpowers z ⊔ (Bs ⊓ K) ≤ Subgroup.centralizer ({r} : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hrz).symm
    · intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hrK b hb.2)
  have hrBs : r ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hsup] at hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  have hmem : r ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := ⟨hBstar r hrBs hr3, hrK⟩
  rwa [hker] at hmem

theorem exists_inner_of_autThreePowInner {G : Type} [Group G] {Bs K : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hAut : AutThreePowInner ↥K) :
    ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹ := by
  intro b hb
  let ψ := ggGamma K hN ⟨b, hb⟩
  have hψ3 : ψ ^ 3 = 1 := by
    have hb3 : (⟨b, hb⟩ : ↥Bs) ^ 3 = 1 := Subtype.ext (hBs.2 b hb)
    rw [← map_pow, hb3, map_one]
  obtain ⟨a, ha⟩ := hAut ψ 1 (by
    intro y
    rw [pow_one]
    have hiter : ψ^[3] y = (ψ ^ 3) y := rfl
    rw [hiter, hψ3]
    rfl)
  refine ⟨a, a.2, fun l hl => ?_⟩
  have h := congrArg Subtype.val (ha ⟨l, hl⟩)
  rw [ggGamma_coe] at h
  simpa using h

theorem sStar_normal_of_component {G : Type} [Group G] [Finite G] {B Bs K : Subgroup G} {z : G}
    {n : ℕ} (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ n) (hn : 3 ≤ n) (hz : z ∈ B) (hz1 : z ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hZ : Subgroup.center ↥K = ⊥) (hAut : AutThreePowInner ↥K)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    Nat.card ↥(Bs ⊓ K) = 3 ^ (n - 1) ∧ Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs ∧
      LargeEvenSStar 3 B z K ∧ (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
  have hzBs : z ∈ Bs := hBBs hz
  obtain ⟨-, hEcard, hsup, -, -⟩ := P10b_bstar_decomp hBs hcard hzBs hz1 hN hker hZ
    (exists_inner_of_autThreePowInner hBs hN hAut) hBstar
  have hSstar : LargeEvenSStar 3 B z K :=
    ⟨hB, hz, hz1, hcomp, fun S hS hS3 =>
      isCyclic_of_le_centralizer_of_bstar hBs hzBs hz1 hker hsup hBstar hS hS3⟩
  refine ⟨hEcard, hsup, hSstar, subgroupOf_centralizer_normal_of_sStar hSstar
    ⟨Bs ⊓ K, inf_le_right, IsPGroup.of_card hEcard, fun hcyc => ?_⟩⟩
  have hexp : Monoid.exponent ↥(Bs ⊓ K) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hBs.2 g g.2.1)
  rw [IsCyclic.exponent_eq_card, hEcard] at hexp
  have h9 : 3 ^ 2 ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.le_of_dvd (by norm_num) hexp
  omega

section D6


theorem center_eq_bot_of_omegaPlusSix_marking {X : Type} [Group X] [Finite X]
    (hm : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1)) :
    Subgroup.center X = ⊥ := by
  obtain ⟨hX, lab, hlab, hraw⟩ := hm
  have hFS : lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1 := by
    obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, hP⟩ := hQ.2.2
    exact hP
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hFS
  obtain ⟨ht, hr, hn⟩ := hFS
  subst ht
  subst hr
  subst hn
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, fieldF, finiteF, hcard, hQ⟩ := hraw
  dsimp only at hcard hQ
  let : Field F := fieldF
  let : Finite F := finiteF
  obtain ⟨hs, -, θ, -⟩ := hQ
  set θ' : X ⧸ Subgroup.center X ≃*
      StatedProj (StatedOmega (StatedQuadPlus 6 F)) := θ with hθ'
  have hcard' : Nat.card F = 2 ^ 1 := by simpa using hcard
  have hF2 : Nat.card F = 2 := by simpa using hcard'
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaPlus_two_hopfMultiplier
      (n := 6) (K := F) (p := 2) (f := 1) (by norm_num) hcard' hF2
  have hcardM : Nat.card (griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus 6 F)))) = 1 := by
    rw [Nat.card_congr eM.toEquiv]
    simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.genericOrders]
  have : Finite (griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus 6 F)))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardM]; exact one_ne_zero)
  have hq0 : CFSG.Assembly.IsQuasisimple X :=
    ⟨hX, (MulEquiv.isSimpleGroup_congr θ').mpr hs⟩
  have hq : CFSG.IsQuasisimple X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp hq0
  have hd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq θ'
  rw [hcardM, Nat.dvd_one] at hd
  exact Subgroup.eq_bot_of_card_eq _ hd

theorem sStar_normal_D6 {G : Type} [Group G] [Finite G] {B Bs K : Subgroup G} {z : G}
    (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 7) (hz : z ∈ B) (hz1 : z ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) 3 Bs K) :
    Subgroup.center ↥K = ⊥ ∧ Nat.card ↥(Bs ⊓ K) = 3 ^ 6 ∧ Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs ∧
      LargeEvenSStar 3 B z K ∧ (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
      LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
  have hmD6 : LargeEvenMarking K
      (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hK
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_omegaPlusSix_marking hmD6
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaPlusSix_of_marking hmD6 hZ
  have hAut : AutThreePowInner ↥K :=
    autThreePowInner_of_goodQ (goodQ_plus (n := 5) (by norm_num))
      (omegaTwoAutInduced_plus_of_four_le (n := 5) (by norm_num)) e
  obtain ⟨hEcard, hsup, hS, hKn⟩ :=
    sStar_normal_of_component hB hBBs hBs hcard (by norm_num) hz hz1 hcomp hN hker hZ hAut hBstar
  have hEcard' : Nat.card ↥(Bs ⊓ K) = 3 ^ 6 := by simpa using hEcard
  exact ⟨hZ, hEcard', hsup, hS, hKn, hmD6⟩

end D6

private theorem glueAux_marking_E7 {X : Type} [Group X] {P : LargeEvenMarkProp X}
    (hP : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → lab.tag = .E7 ∧ lab.n = 1)
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, CFSG.StandardType.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  obtain ⟨ht, hn⟩ := hP lab R I F θ hθ
  refine ⟨hs, hna, θ, ht, ?_, hn⟩
  obtain ⟨t, r, m⟩ := lab
  dsimp only at ht ⊢
  subst ht
  exact hlab.2

section E7


theorem sStar_normal_E7 {G : Type} [Group G] [Finite G] {B Bs K : Subgroup G} {z : G} {n : ℕ}
    (hB : LargeEvenIsBmax 3 B) (hBBs : B ≤ Bs) (hBs : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ B) (hz1 : z ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs K) :
    n = 8 ∧ Subgroup.center ↥K = ⊥ ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ∧
        Nonempty (↥K ≃* adjointGroup .E7 F)) ∧
      Nat.card ↥(Bs ⊓ K) = 3 ^ 7 ∧ Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs ∧
      LargeEvenSStar 3 B z K ∧ (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal ∧
      LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .E7 ∧ lab.rank = 0 ∧ lab.n = 1) := by
  obtain ⟨hn8, F, fieldF, finiteF, hF2, eK, -, -, -⟩ :=
    P10c_E7_eight hBs hcard hn (hBBs hz) hz1 hN hker hBstar hK
  subst hn8
  have hcharF : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
      rw [Fintype.card_eq_nat_card]
      simpa using hF2)
  have hZ : Subgroup.center ↥K = ⊥ := CFSG.SeitzReduction.E7Pilot.center_eq_bot_of_mulEquiv_E7 eK
  have hAut : AutThreePowInner ↥K := fun ψ _ _ => by
    obtain ⟨a, ha⟩ :=
      CFSG.SeitzReduction.E7Pilot.forall_mem_range_conj_of_mulEquiv_E7_two hF2 eK ψ
    exact ⟨a, fun l => by rw [← ha, MulAut.conj_apply]⟩
  obtain ⟨hEcard, hsup, hS, hKn⟩ :=
    sStar_normal_of_component hB hBBs hBs hcard (by norm_num) hz hz1 hcomp hN hker hZ hAut hBstar
  exact ⟨rfl, hZ, ⟨F, fieldF, finiteF, hcharF, hF2, ⟨eK⟩⟩, hEcard, hsup, hS, hKn,
    glueAux_marking_E7 (fun _ _ _ _ _ _ h => h.1) hK⟩

end E7

end CFSG.StandardType.FrameRoute

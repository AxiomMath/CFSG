module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCompCore
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcBridge
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcCenter
public import CFSG.LocalAnalysis.StandardType.GGSixRCKStepZero
public import CFSG.LocalAnalysis.StandardType.GGLieM6cFinal
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBlocks
import CFSG.RankThree.PartOne.S10.FiveSuccessorActor
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Planes
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.U62ThreeCentP6
import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Cover
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourNotToral
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KToral
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModelLift
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenUni
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealKey
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealTriple
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadHigh
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
import CFSG.LocalAnalysis.StandardType.GGTwE6K1Holds
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviMain
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourOutLine
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KType
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFuse
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreCent
import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusDoubleEdge
import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusFields
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModel
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModelRat
import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Subtype
import CFSG.LocalAnalysis.StandardType.GGE6IsoLayerAdj
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import CFSG.HardMathSupport.Dickson.Bal207.Glue
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShellGl
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadCover
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019UniBlocks

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.StandardType.RCKBand (CaseEightV StepZeroRankFloor)

private theorem rckExc_exists_ne_one_centralizer {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {U D : Subgroup X} (hUp : IsPGroup p U) (hUne : U ≠ ⊥) (hDp : IsPGroup p D)
    (hDU : D ≤ Subgroup.normalizer (U : Set X)) :
    ∃ y ∈ U, y ≠ 1 ∧ y ∈ Subgroup.centralizer (D : Set X) := by
  have hB : IsPGroup p (↥(U ⊔ D)) := hUp.to_sup_of_normal_left' hDp hDU
  have hBN : U ⊔ D ≤ Subgroup.normalizer (U : Set X) := sup_le Subgroup.le_normalizer hDU
  haveI : (U.subgroupOf (U ⊔ D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hBN
  haveI : Group.IsNilpotent ↥(U ⊔ D) := hB.isNilpotent
  have hne : U.subgroupOf (U ⊔ D) ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    intro hbot
    apply hu1
    have hmem : (⟨u, Subgroup.mem_sup_left u.2⟩ : ↥(U ⊔ D)) ∈ U.subgroupOf (U ⊔ D) := u.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 : ((⟨u, Subgroup.mem_sup_left u.2⟩ : ↥(U ⊔ D)) : X) = ((1 : ↥(U ⊔ D)) : X) :=
      congrArg Subtype.val hmem
    exact Subtype.ext h2
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  refine ⟨(((a : ↥(U.subgroupOf (U ⊔ D) ⊓ Subgroup.center ↥(U ⊔ D))) : ↥(U ⊔ D)) : X), a.2.1,
    ?_, ?_⟩
  · intro h1
    apply ha1
    exact Subtype.ext (Subtype.ext h1)
  · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 a.2.2 ⟨w, Subgroup.mem_sup_right hw⟩)

@[expose] def RCKExcFloors
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL)),
      RCKBridgeFrame t f p G₀ A θ A' → StepZeroRankFloor t f p A'

private theorem rckExc_mem_center_of_commutators {A : Type} [Group A]
    (hperf : commutator A = ⊤) {N : Subgroup A} (hN : N ≤ Subgroup.center A) {x : A}
    (hx : ∀ z, ⁅x, z⁆ ∈ N) : x ∈ Subgroup.center A := by
  have : Group.IsPerfect A := ⟨hperf⟩
  have hstep : x ∈ Subgroup.upperCentralSeriesStep (Subgroup.center A) := fun z => hN (hx z)
  have h2 : Subgroup.upperCentralSeries A 2 = Subgroup.center A :=
    Group.IsPerfect.upperCentralSeries_eq_center A (by norm_num)
  refine h2 ▸ ?_
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro z
  rw [Subgroup.upperCentralSeries_one]
  exact hstep z

theorem rckExc_center_bot_twE6_core
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .twistedE6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L) (hp3 : p = 3) :
    Subgroup.center ↥G₀ = ⊥ := by
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, -⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K := hGG.2.1.2
  subst hp3
  have hKperf : commutator (ggU .twistedE6 n f).K = ⊤ :=
    MpStdTwE6.commutator_twistedE6Group hf
  have hZK : Nat.card (Subgroup.center (ggU .twistedE6 n f).K) ∣ 3 :=
    TwE6Nonsplit.center_card_dvd_three f hf
  have hZle : (Subgroup.center ↥G₀).map G₀.subtype ≤
      (Subgroup.center (ggU .twistedE6 n f).K).map ψ := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ : (z : X) ∈ ψ.range := by rw [hrange]; exact z.2
    refine ⟨k, rckExc_mem_center_of_commutators hKperf hker (fun x => ?_), hk⟩
    refine MonoidHom.mem_ker.mpr ?_
    rw [map_commutatorElement, hk]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    have hψx : ψ x ∈ G₀ := by rw [← hrange]; exact ⟨x, rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨ψ x, hψx⟩)).symm
  have hdvd3 : Nat.card (Subgroup.center ↥G₀) ∣ 3 :=
    (dvd_of_eq (Subgroup.card_map_of_injective G₀.subtype_injective).symm).trans
      ((Subgroup.card_dvd_of_le hZle).trans
        ((Subgroup.card_map_dvd (Subgroup.center (ggU .twistedE6 n f).K) ψ).trans hZK))
  have hn3 := rck_p_not_dvd_center hp hAel hAnorm hSC hAc
  have h1 : Nat.card (Subgroup.center ↥G₀) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h | h
    · exact h
    · exact absurd (by rw [h] : 3 ∣ Nat.card (Subgroup.center ↥G₀)) hn3
  exact Subgroup.card_eq_one.1 h1

theorem rck_centralizer_L_eq_zpowers_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L) (hBA : B₁ = A) :
    ∃ x, x ∈ D ∧ x ≠ 1 ∧ IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x}) ∧
      A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x ∧
      Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set X)) = p := by
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  obtain ⟨x, hxD, hx1, hxcomp⟩ := hx
  have hDA : D ≤ A := hBA ▸ hDB1
  have hxA : x ∈ A := hDA hxD
  have hxL : x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp ((hxcomp.1 hl).2)
  have hJL : J ≤ L := hJcompL.1.trans inf_le_left
  have hxW : x ∈ A ⊓ Subgroup.centralizer (L : Set X) := ⟨hxA, hxL⟩
  have hWleD : A ⊓ Subgroup.centralizer (L : Set X) ≤ D := by
    intro y hy
    have hyJ : y ∈ Subgroup.centralizer (J : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_iff.mp hy.2 j (hJL hj)
    have hyB : y ∈ B₁ := hBA.symm ▸ hy.1
    exact hB1Jc ▸ (show y ∈ B₁ ⊓ Subgroup.centralizer (J : Set X) from ⟨hyB, hyJ⟩)
  have hDnotc' : ¬ (D : Set X) ⊆ (Subgroup.centralizer (L : Set X) : Set X) := hDnotc
  obtain ⟨c, hcD, hcC⟩ := Set.not_subset.mp hDnotc'
  have hcW : c ∉ A ⊓ Subgroup.centralizer (L : Set X) := fun hc => hcC hc.2
  haveI : Fact p.Prime := ⟨hp⟩
  have hxpow : x ^ p = 1 := hAel.2 x hxA
  have hxord : orderOf x = p := orderOf_eq_prime hxpow hx1
  have hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x :=
    CFSG.RankThree.PartOne.eq_zpowers_of_le_of_card_eq_sq hp hWleD hDcard hcD hcW hxW hxord
  exact ⟨x, hxD, hx1, hxcomp, hWeq, by rw [hWeq, Nat.card_zpowers, hxord]⟩

theorem rckExcCaseVData_of_caseEightV_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L : Subgroup X}
    (ht : GGExcFive t) (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    (hframe : RCKBridgeFrame t f p G₀ A θ A') (hCaseV : CaseEightV t f p A')
    (hlt5 : ¬ 3 ^ 5 ≤ Nat.card A') : RCKExcCaseVData t f p G₀ A B₁ := by
  obtain ⟨hθker, hθrange, hA'le, hA'el, hA'card, hfwd, hbwd⟩ := hframe
  have hcfg := h
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  have h4A : p ^ 4 ≤ Nat.card A := hp4.trans (Subgroup.card_le_of_le hB1A)
  have h4A' : p ^ 4 ≤ Nat.card A' := hA'card ▸ h4A
  obtain ⟨htw, hp3, h3, h9, hA'R⟩ := hCaseV
  subst htw
  subst hp3
  have hcardA' : Nat.card A' ≤ 3 ^ 4 := RCKBand.rckSZ_card_le_pow_four hp hA'el h4A' hlt5
  have hcardA : Nat.card A = 3 ^ 4 := le_antisymm (hA'card ▸ hcardA') h4A
  have hB1 : B₁ = A := Subgroup.eq_of_le_of_card_ge hB1A (by rw [hcardA]; exact hp4)
  have hZ : Subgroup.center ↥G₀ = ⊥ := rckExc_center_bot_twE6_core hcfg rfl
  have hinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, hθker]; exact hZ
  have hAp : IsPGroup 3 A := fun a => ⟨1, by apply Subtype.ext; simpa using hAel.2 a a.2⟩
  let U : Subgroup X :=
    { carrier := {c | c ∈ Subgroup.centralizer (G₀ : Set X) ∧ ∃ g ∈ G₀, ∃ b ∈ A, c = g * b}
      mul_mem' := by
        rintro c c' ⟨hcC, g, hg, b, hb, rfl⟩ ⟨hc'C, g', hg', b', hb', rfl⟩
        refine ⟨(Subgroup.centralizer (G₀ : Set X)).mul_mem hcC hc'C,
          g * (b * g' * b⁻¹), ?_, b * b', A.mul_mem hb hb', by group⟩
        exact G₀.mul_mem hg ((Subgroup.mem_normalizer_iff.mp (hAnorm hb) g').mp hg')
      one_mem' := ⟨Subgroup.one_mem _, 1, G₀.one_mem, 1, A.one_mem, by simp⟩
      inv_mem' := by
        rintro c ⟨hcC, g, hg, b, hb, rfl⟩
        refine ⟨(Subgroup.centralizer (G₀ : Set X)).inv_mem hcC, b⁻¹ * g⁻¹ * b, ?_, b⁻¹,
          A.inv_mem hb, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hAnorm (A.inv_mem hb)) g⁻¹).mp (G₀.inv_mem hg)
        simpa using this }
  have hexp : ∀ u ∈ U, u ^ 3 = 1 := by
    rintro u ⟨huC, g, hg, b, hb, rfl⟩
    have hb3 : b ^ 3 = 1 := hAel.2 b hb
    have hact : ∀ x ∈ G₀, b * x * b⁻¹ = g⁻¹ * x * g := by
      intro x hx
      have h1 := (Subgroup.mem_centralizer_iff.mp huC) x hx
      calc b * x * b⁻¹ = g⁻¹ * (g * b * x) * b⁻¹ := by group
        _ = g⁻¹ * (x * (g * b)) * b⁻¹ := by rw [← h1]
        _ = g⁻¹ * x * g := by group
    have hiter : ∀ k : ℕ, ∀ x ∈ G₀, b ^ k * x * (b ^ k)⁻¹ = (g ^ k)⁻¹ * x * g ^ k := by
      intro k
      induction k with
      | zero => intro x hx; simp
      | succ k ih =>
        intro x hx
        have hx' : g⁻¹ * x * g ∈ G₀ := G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hg) hx) hg
        calc b ^ (k + 1) * x * (b ^ (k + 1))⁻¹ = b ^ k * (b * x * b⁻¹) * (b ^ k)⁻¹ := by group
          _ = b ^ k * (g⁻¹ * x * g) * (b ^ k)⁻¹ := by rw [hact x hx]
          _ = (g ^ k)⁻¹ * (g⁻¹ * x * g) * g ^ k := ih _ hx'
          _ = (g ^ (k + 1))⁻¹ * x * g ^ (k + 1) := by group
    have hg3 : g ^ 3 = 1 := by
      have hmem : (⟨g ^ 3, G₀.pow_mem hg 3⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        have h1 := hiter 3 y y.2
        rw [hb3, inv_one, one_mul, mul_one] at h1
        show (y : X) * g ^ 3 = g ^ 3 * (y : X)
        calc (y : X) * g ^ 3 = g ^ 3 * ((g ^ 3)⁻¹ * (y : X) * g ^ 3) := by group
          _ = g ^ 3 * (y : X) := by rw [← h1]
      rw [hZ] at hmem
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    have hcomm : Commute g b := by
      have h1 := hact g hg
      have h2 : b * g * b⁻¹ = g := by rw [h1]; group
      calc g * b = (b * g * b⁻¹) * b := by rw [h2]
        _ = b * g := by group
    rw [hcomm.mul_pow, hg3, hb3, one_mul]
  have hUp : IsPGroup 3 U := fun u => ⟨1, by apply Subtype.ext; simpa using hexp u u.2⟩
  have hUN : A ≤ Subgroup.normalizer (U : Set X) := by
    have hc : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
      intro a ha u hu
      obtain ⟨huC, g, hg, b, hb, rfl⟩ := hu
      have hcomm : a * b = b * a :=
        congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      refine ⟨?_, a * g * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hAnorm ha) g).mp hg, b, hb, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : a⁻¹ * x * a ∈ G₀ := by
          have := (Subgroup.mem_normalizer_iff.mp (hAnorm (A.inv_mem ha)) x).mp hx
          simpa using this
        have h1 := (Subgroup.mem_centralizer_iff.mp huC) _ hx'
        calc x * (a * (g * b) * a⁻¹) = a * ((a⁻¹ * x * a) * (g * b)) * a⁻¹ := by group
          _ = a * ((g * b) * (a⁻¹ * x * a)) * a⁻¹ := by rw [h1]
          _ = a * (g * b) * a⁻¹ * x := by group
      · calc a * (g * b) * a⁻¹ = a * g * a⁻¹ * (a * b * a⁻¹) := by group
          _ = a * g * a⁻¹ * b := by rw [hcomm]; group
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hc a ha u, fun hu => ?_⟩
    have h1 := hc a⁻¹ (A.inv_mem ha) _ hu
    have h2 : a⁻¹ * (a * u * a⁻¹) * a⁻¹⁻¹ = u := by group
    rw [h2] at h1
    exact h1
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hUtriv : U = ⊥ := by
    by_contra hne
    obtain ⟨y, hyU, hy1, hyC⟩ :=
      rckExc_exists_ne_one_centralizer
        hUp hne hAp hUN
    have hyord : orderOf y = 3 := orderOf_eq_prime (hexp y hyU) hy1
    obtain ⟨huC, g, hg, b, hb, rfl⟩ := hyU
    have hyJ : g * b ∈ A ⊔ G₀ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hg) (Subgroup.mem_sup_left hb)
    have hyA : g * b ∈ A := hSC _ ⟨hyJ, hyC⟩ hyord
    have hy' : g * b ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hyA, huC⟩
    rw [hAc] at hy'
    exact hy1 (Subgroup.mem_bot.mp hy')
  have hAG : A ≤ G₀ := by
    intro d hd
    obtain ⟨a, haA', hacts⟩ := hfwd d hd
    obtain ⟨g₁, hg₁⟩ : a ∈ θ.range := by rw [hθrange]; exact hA'R haA'
    have hconj : ∀ x ∈ G₀, d * x * d⁻¹ = (g₁ : X) * x * (g₁ : X)⁻¹ := by
      intro x hx
      have hdx : d * x * d⁻¹ ∈ G₀ := (Subgroup.mem_normalizer_iff.mp (hAnorm hd) x).mp hx
      have h1 := hacts ⟨x, hx⟩ hdx
      rw [← hg₁] at h1
      have h2 : θ ⟨d * x * d⁻¹, hdx⟩ = θ (g₁ * ⟨x, hx⟩ * g₁⁻¹) :=
        calc θ ⟨d * x * d⁻¹, hdx⟩ = θ g₁ * θ ⟨x, hx⟩ * (θ g₁)⁻¹ := h1
          _ = θ (g₁ * ⟨x, hx⟩ * g₁⁻¹) := by simp [map_mul, map_inv]
      exact congrArg Subtype.val (hinj h2)
    have hcU : (g₁ : X)⁻¹ * d ∈ U := by
      refine ⟨?_, (g₁ : X)⁻¹, G₀.inv_mem g₁.2, d, hd, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * ((g₁ : X)⁻¹ * d) = (g₁ : X)⁻¹ * ((g₁ : X) * x * (g₁ : X)⁻¹) * d := by group
        _ = (g₁ : X)⁻¹ * (d * x * d⁻¹) * d := by rw [hconj x hx]
        _ = (g₁ : X)⁻¹ * d * x := by group
    rw [hUtriv] at hcU
    have h1 : (g₁ : X)⁻¹ * d = 1 := Subgroup.mem_bot.mp hcU
    have h2 : d = (g₁ : X) := by
      calc d = (g₁ : X) * ((g₁ : X)⁻¹ * d) := by group
        _ = (g₁ : X) := by rw [h1, mul_one]
    rw [h2]; exact g₁.2
  exact ⟨rfl, rfl, h3, h9, hcardA, hB1, hAG, hZ⟩

theorem rckExcCaseVData_of_caseEightV
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (ht : GGExcFive t) (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    (hframe : RCKBridgeFrame t f p G₀ A θ A') (hCaseV : CaseEightV t f p A')
    (hlt5 : ¬ 3 ^ 5 ≤ Nat.card A') : RCKExcCaseVData t f p G₀ A B₁ :=
  rckExcCaseVData_of_caseEightV_core ht (rckCompCore_of_rpConfig h) hframe hCaseV hlt5

theorem rckExcCaseVData_of_frame
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L : Subgroup X}
    (ht : GGExcFive t) (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    (hframe : RCKBridgeFrame t f p G₀ A θ A') (hNTA' : ¬ IsToralSubgroup (langTag t) GGL A')
    (hfl : StepZeroRankFloor t f p A') : RCKExcCaseVData t f p G₀ A B₁ := by
  have hframe' := hframe
  obtain ⟨hθker, hθrange, hA'le, hA'el, hA'card, hfwd, hbwd⟩ := hframe
  have hcfg := h
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hrange : ψ.range = G₀ := hGG.2.1.1
  have hker : ψ.ker ≤ Subgroup.center (ggU t n f).K := hGG.2.1.2
  have h4A : p ^ 4 ≤ Nat.card A := hp4.trans (Subgroup.card_le_of_le hB1A)
  have h4A' : p ^ 4 ≤ Nat.card A' := hA'card ▸ h4A
  have hCaseV : CaseEightV t f p A' := by
    by_contra hv
    exact hNTA' (RCKBand.ggLieToralStepZeroRCK_of_M6c CFSG.StandardType.LieCore.M6c.ggLieNonToralRankFour_holds t ht f hf p hp hp2
      A' hA'le hA'el h4A' hfl hv)
  have hCaseV' := hCaseV
  obtain ⟨htw, hp3, h3, h9, hA'R⟩ := hCaseV
  subst htw
  subst hp3
  have hlt5 : ¬ 3 ^ 5 ≤ Nat.card A' := fun h5 =>
    hNTA' (RCKBand.rckSZ_bigElem hp hp2 ExcFramesHalf.bigElemAbelianToralBar_E6_three
      (RCKBand.rckSZ_le_adjoint hA'le) hA'el h5)
  exact rckExcCaseVData_of_caseEightV_core ht hcfg hframe' hCaseV' hlt5

theorem rckExcCaseVReduction_of_floors
    (hFl : RCKExcFloors) : RCKExcCaseVReduction := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht h hNT
  obtain ⟨θ, A', hframe⟩ := rckBridgeFrame_exists ht h
  have hNTA' : ¬ IsToralSubgroup (langTag t) GGL A' := fun hT => hNT ⟨θ, A', hframe, hT⟩
  exact rckExcCaseVData_of_frame ht (rckCompCore_of_rpConfig h) hframe hNTA'
    (hFl X t n f ψ p G₀ A B₁ D J L R Rm K e ht h θ A' hframe)

theorem rckExcCaseV_selfCent_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    GGTorusSelfCent 3 ((A.subgroupOf G₀).map (MulAut.conj : ↥G₀ →* MulAut ↥G₀)) ∧
      Nat.card ((A.subgroupOf G₀).map (MulAut.conj : ↥G₀ →* MulAut ↥G₀)) = 3 ^ 4 := by
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, -, -, hcardA, -, hAG, hZ⟩ := hV
  unfold RCKCompCore at h
  rcases h with
    ⟨-, -, hp, -, -, -, -, -, -, -, -, -, -, hSC, -⟩
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  constructor
  · intro n hnfix hn3
    have hnA : (n : X) ∈ A := by
      by_cases hn1 : (n : X) = 1
      · simpa [hn1] using A.one_mem
      · apply hSC (n : X) ⟨Subgroup.mem_sup_right n.2, ?_⟩ ?_
        · refine Subgroup.mem_centralizer_iff.2 ?_
          intro a ha
          have ha0 : (⟨a, hAG ha⟩ : ↥G₀) ∈ A.subgroupOf G₀ :=
            Subgroup.mem_subgroupOf.mpr ha
          have hfix : a * (n : X) * a⁻¹ = (n : X) := by
            simpa using congrArg Subtype.val
              (hnfix (MulAut.conj (⟨a, hAG ha⟩ : ↥G₀))
                (Subgroup.mem_map.mpr ⟨⟨a, hAG ha⟩, ha0, rfl⟩))
          calc a * (n : X) = (a * (n : X) * a⁻¹) * a := by group
            _ = (n : X) * a := by rw [hfix]
        · refine orderOf_eq_prime ?_ ?_
          · simpa using congrArg Subtype.val hn3
          · intro h1
            exact hn1 h1
    exact Subgroup.mem_map.mpr
      ⟨⟨n, n.2⟩, Subgroup.mem_subgroupOf.mpr hnA, rfl⟩
  · have hinj : Function.Injective (MulAut.conj : ↥G₀ →* MulAut ↥G₀) := by
      rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
    rw [Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv, hcardA]

theorem rckExcCaseV_not_toral_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ¬ RCKToralFrame t f p G₀ A := by
  have hSelf := rckExcCaseV_selfCent_core h hV
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, h3dvd, -, hcardA, -, hAG, hZ⟩ := hV
  have ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hf : 1 ≤ f := by
    have hcfg := h
    unfold RCKCompCore at hcfg
    exact hcfg.1.1.1.2.1
  intro hTor
  obtain ⟨θ, A', hFrame, hToral⟩ := hTor
  have hEq : A' = (A.subgroupOf G₀).map θ :=
    rckBridgeFrame_eq_map_of_presentation ht h.1 hFrame hAG
  have hinjθ : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, hFrame.1, hZ]
  have hinjConj : Function.Injective (MulAut.conj : ↥G₀ →* MulAut ↥G₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  let θE : ↥G₀ →* ModGL Tag.E6 GGL := θ
  let A'E : Subgroup (ModGL Tag.E6 GGL) := A'
  have hEqE : A'E = (A.subgroupOf G₀).map θE := by
    dsimp only [A'E, θE]
    exact hEq
  have hinjθE : Function.Injective θE := hinjθ
  let Rgrp : Subgroup (ModGL Tag.E6 GGL) :=
    _root_.CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp GGL (ggFrobT f)
  have hFixRgrp : ggFixGp .twistedE6 f = Rgrp := rfl
  have hXle : A'E ≤ Rgrp := by
    rw [← hFixRgrp]
    exact hFrame.2.2.1
  have hX3 : ∀ x ∈ A'E, x ^ 3 = 1 := by
    intro x hx
    exact hFrame.2.2.2.1.2 x hx
  have hXcard : Nat.card A'E = 3 ^ 4 := by
    exact hFrame.2.2.2.2.1.trans hcardA
  have hSC' : ∀ u ∈ ⁅Rgrp, Rgrp⁆, u ^ 3 = 1 →
      (∀ x ∈ A'E, x * u = u * x) → u ∈ A'E := by
    intro u huDeriv hu3 hcomm
    have huRange : u ∈ θE.range := by
      change u ∈ θ.range
      rw [hFrame.2.1, hFixRgrp]
      exact huDeriv
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp huRange
    have hn3 : n ^ 3 = 1 := by
      apply hinjθE
      calc
        θE (n ^ 3) = θE n ^ 3 := map_pow θE n 3
        _ = u ^ 3 := by rw [hn]
        _ = 1 := hu3
        _ = θE 1 := (map_one θE).symm
    have hnfix : ∀ b ∈ (A.subgroupOf G₀).map (MulAut.conj : ↥G₀ →* MulAut ↥G₀),
        b n = n := by
      intro b hb
      obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp hb
      apply hinjθE
      have hθa : θE a0 ∈ A'E := by
        rw [hEqE]
        exact Subgroup.mem_map_of_mem θE ha0
      have hc := hcomm (θE a0) hθa
      calc
        θE ((MulAut.conj a0) n) = θE (a0 * n * a0⁻¹) := by rw [MulAut.conj_apply]
        _ = θE a0 * θE n * (θE a0)⁻¹ := by simp [map_mul, map_inv]
        _ = θE n := by
          rw [hn, hc]
          group
    have hmem : MulAut.conj n ∈ (A.subgroupOf G₀).map
        (MulAut.conj : ↥G₀ →* MulAut ↥G₀) := hSelf.1 n hnfix hn3
    obtain ⟨a0, ha0, haeq⟩ := Subgroup.mem_map.mp hmem
    have hna : a0 = n := hinjConj haeq
    have hnSub : n ∈ A.subgroupOf G₀ := hna ▸ ha0
    rw [hEqE, ← hn]
    exact Subgroup.mem_map_of_mem θE hnSub
  have hnt : ¬ _root_.CFSG.StandardType.SCFourCover.E6AdToral A'E :=
    _root_.CFSG.StandardType.SCFourCover.not_e6AdToral_of_selfCent_derived hf (ggFrobT f)
      (ggFrobT_apply f) h3dvd hXle hX3 hXcard hSC'
  apply hnt
  obtain ⟨g, hg, hconj⟩ := hToral
  let gE : ModGL Tag.E6 GGL := g
  have hgE : gE ∈ adjointGroup Tag.E6 GGL := hg
  have hconjE : ∀ x ∈ A'E,
      gE⁻¹ * x * gE ∈ _root_.CFSG.LieType.Chevalley.torusGroup Tag.E6 GGL := by
    intro x hx
    exact hconj x hx
  refine ⟨gE⁻¹, (adjointGroup Tag.E6 GGL).inv_mem hgE, fun x hx => ?_⟩
  simpa only [inv_inv] using hconjE x hx

theorem rckExcCaseV_not_toral
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ¬ RCKToralFrame t f p G₀ A :=
  rckExcCaseV_not_toral_core (rckCompCore_of_rpConfig h) hV

private theorem rckExc_lMarking_subgroupOf {X : Type*} [Group X]
    {L G₀ B : Subgroup X} (hLG : L ≤ G₀)
    (h : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : X) = b⁻¹ * l * b) φ)) :
    LargeEvenMarking ↥(L.subgroupOf G₀) (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥(L.subgroupOf G₀) =>
        ((l' : ↥G₀) : X) = b⁻¹ * ((l : ↥G₀) : X) * b) φ) := by
  let e : ↥(L.subgroupOf G₀) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  refine largeEvenMarking_congr e ?_ h
  intro lab R _ I F θ hθ b hb
  obtain ⟨φ, hφ, hind⟩ := hθ b hb
  refine ⟨φ, hφ, ?_⟩
  refine (largeEvenInduces_congr_equiv e θ
    (fun l l' : ↥(L.subgroupOf G₀) =>
      ((l' : ↥G₀) : X) = b⁻¹ * ((l : ↥G₀) : X) * b)
    (fun l l' : ↥L => (l' : X) = b⁻¹ * l * b) ?_ φ).2 hind
  intro l l'
  exact Iff.rfl

private theorem rckExcCaseV_original_action {X : Type} [Group X]
    {G₀ A L : Subgroup X} {x : X}
    (hAG : A ≤ G₀) (hAL : A ≤ Subgroup.normalizer (L : Set X)) (hLG0 : L ≤ G₀)
    (hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x)
    (hxcomp : IsComponentOf L (G₀ ⊓ Subgroup.centralizer ({x} : Set X)))
    (hxG : x ∈ G₀) (hx1 : x ≠ 1) (hAel : IsElemAbelian 3 A)
    (hcardA : Nat.card A = 3 ^ 4) (hZ : Subgroup.center ↥G₀ = ⊥) :
    (let x₀ : ↥G₀ := ⟨x, hxG⟩
     let a₀ : MulAut ↥G₀ := MulAut.conj x₀
     let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
     let E : Subgroup (MulAut ↥G₀) := A₀.map (MulAut.conj : ↥G₀ →* MulAut ↥G₀)
     let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
     IsComponentOf L₀ (ggFix a₀) ∧
     (∀ a ∈ E, ∀ l ∈ L₀, a l ∈ L₀) ∧
     (∀ a ∈ E, (∀ l ∈ L₀, a l = l) → a ∈ Subgroup.zpowers a₀) ∧
     Function.Injective (MulAut.conj : ↥G₀ →* MulAut ↥G₀) ∧
     IsElemAbelian 3 A₀ ∧ IsElemAbelian 3 E ∧
     x₀ ∈ A₀ ∧ a₀ ∈ E ∧ x₀ ≠ 1 ∧ a₀ ≠ 1 ∧ Nat.card A₀ = 3 ^ 4) := by
  let x₀ : ↥G₀ := ⟨x, hxG⟩
  let a₀ : MulAut ↥G₀ := MulAut.conj x₀
  let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
  let E : Subgroup (MulAut ↥G₀) := A₀.map (MulAut.conj : ↥G₀ →* MulAut ↥G₀)
  let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  have hA0el : IsElemAbelian 3 A₀ := hAel.subgroupOf G₀
  have hEel : IsElemAbelian 3 E := hA0el.map (MulAut.conj : ↥G₀ →* MulAut ↥G₀)
  have hx0A0 : x₀ ∈ A₀ := Subgroup.mem_subgroupOf.mpr (by
    have hxW : x ∈ A ⊓ Subgroup.centralizer (L : Set X) := by
      rw [hWeq]
      exact Subgroup.mem_zpowers x
    exact hxW.1)
  have ha0E : a₀ ∈ E := Subgroup.mem_map.mpr ⟨x₀, hx0A0, rfl⟩
  have hinjConj : Function.Injective (MulAut.conj : ↥G₀ →* MulAut ↥G₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZ]
  have hx0ne : x₀ ≠ 1 := by
    intro h1
    exact hx1 (congrArg Subtype.val h1)
  have ha0ne : a₀ ≠ 1 := by
    intro h1
    apply hx0ne
    exact hinjConj (by simpa using h1)
  have hfixEq : (G₀ ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf G₀ = ggFix a₀ := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      mem_ggFix, MulAut.conj_apply]
    constructor
    · rintro ⟨-, hcomm⟩
      apply Subtype.ext
      change (x : X) * (g : X) * x⁻¹ = (g : X)
      rw [hcomm.symm]
      group
    · intro hfix
      refine ⟨g.2, ?_⟩
      have hfixX : (x : X) * (g : X) * x⁻¹ = (g : X) := by
        have := congrArg Subtype.val hfix
        simpa [MulAut.conj_apply] using this
      have hxgx : (x : X) * (g : X) = (g : X) * (x : X) := by
        calc (x : X) * (g : X) = ((x : X) * (g : X) * x⁻¹) * x := by group
          _ = (g : X) * x := by rw [hfixX]
      exact hxgx.symm
  have hL0comp : IsComponentOf L₀ (ggFix a₀) := by
    rw [← hfixEq]
    exact ggIsComponentOf_subgroupOf hxcomp inf_le_left
  have hEnormL0 : ∀ a ∈ E, ∀ l ∈ L₀, a l ∈ L₀ := by
    intro a ha l hl
    obtain ⟨b, hbA0, rfl⟩ := Subgroup.mem_map.mp ha
    have hbA : (b : X) ∈ A := hbA0
    have hconjL : (b : X) * (l : X) * (b : X)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL hbA) (l : X)).mp (Subgroup.mem_subgroupOf.mp hl)
    exact Subgroup.mem_subgroupOf.mpr (by simpa [MulAut.conj_apply] using hconjL)
  have hCentL0 : ∀ a ∈ E, (∀ l ∈ L₀, a l = l) → a ∈ Subgroup.zpowers a₀ := by
    intro a ha hfix
    obtain ⟨b, hbA0, rfl⟩ := Subgroup.mem_map.mp ha
    have hbA : (b : X) ∈ A := hbA0
    have hbCL : (b : X) ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl0 : (⟨l, hLG0 hl⟩ : ↥G₀) ∈ L₀ := Subgroup.mem_subgroupOf.mpr hl
      have hfix' := hfix ⟨l, hLG0 hl⟩ hl0
      have hconj : (b : X) * l * (b : X)⁻¹ = l := by
        have := congrArg Subtype.val hfix'
        simpa [MulAut.conj_apply] using this
      calc l * (b : X) = ((b : X) * l * (b : X)⁻¹) * (b : X) := by rw [hconj]
        _ = (b : X) * l := by group
    have hbW : (b : X) ∈ A ⊓ Subgroup.centralizer (L : Set X) := ⟨hbA, hbCL⟩
    have hbZp : (b : X) ∈ Subgroup.zpowers x := by
      rw [← hWeq]
      exact hbW
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbZp
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc
      a₀ ^ k = (MulAut.conj : ↥G₀ →* MulAut ↥G₀) (x₀ ^ k) := (map_zpow _ _ _).symm
      _ = MulAut.conj b := by
        congr 1
        apply Subtype.ext
        simpa using hk
  exact ⟨hL0comp, hEnormL0, hCentL0, hinjConj, hA0el, hEel, hx0A0, ha0E, hx0ne, ha0ne,
    by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv, hcardA]⟩

theorem rckExcCaseV_marking_L_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    CFSG.StandardType.LargeEvenMarking ↥L
      (fun lab _ _ _ _ _ => lab = ⟨.twA, 5, f⟩) := by
  have hSelf := rckExcCaseV_selfCent_core h hV
  obtain ⟨hEself, hEcard⟩ := hSelf
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, h3dvd, -, hcardA, hBA, hAG, hZ⟩ := hV
  have hxdata := rck_centralizer_L_eq_zpowers_core h hBA
  obtain ⟨x, hxD, hx1, hxcomp, hWeq, -⟩ := hxdata
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  have hDA : D ≤ A := hBA ▸ hDB1
  have hxG : x ∈ G₀ := hAG (hDA hxD)
  let x₀ : ↥G₀ := ⟨x, hxG⟩
  let a₀ : MulAut ↥G₀ := MulAut.conj x₀
  let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
  let E : Subgroup (MulAut ↥G₀) := A₀.map (MulAut.conj : ↥G₀ →* MulAut ↥G₀)
  let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  have hperfG0 : commutator ↥G₀ = ⊤ := hGG.2.2.1
  have hLieG0 : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .twistedE6 n 2 f := hGG.2.2.2
  have hAL : A ≤ Subgroup.normalizer (L : Set X) := hBA ▸ hB1L
  have hsetup := rckExcCaseV_original_action hAG hAL hLG0 hWeq hxcomp hxG hx1 hAel hcardA hZ
  dsimp only at hsetup
  obtain ⟨hL0comp, hEnormL0, hCentL0, -, hA0el, hEel, hx0A0, ha0E, hx0ne, ha0ne, -⟩ :=
    hsetup
  have hG0mark : LargeEvenMarking ↥G₀ (fun lab _ _ _ _ _ =>
      markTag lab = .twistedE6 ∧ markRank lab = n ∧ markChar lab = 2 ∧ markDeg lab = f) :=
    CFSG.StandardType.largeEvenMarking_of_lieModel_centerQuot hperfG0 hLieG0
  obtain ⟨_, lab, hlab, hraw⟩ := hG0mark
  obtain ⟨_, _, _, _, _, _, _, hpres₀⟩ := largeEvenRawDatum_exists hraw
  have hlabtw : lab.tag = .twE6 := by
    obtain ⟨tg, r, nlab⟩ := lab
    clear * - hpres₀
    revert hpres₀
    cases tg <;> simp [markTag] <;> split_ifs <;> simp_all
  have hlabn : lab.n = f := by
    obtain ⟨tg, r, nlab⟩ := lab
    have hdeg : markDeg ⟨tg, r, nlab⟩ = f := hpres₀.2.2.2
    have htag : markTag ⟨tg, r, nlab⟩ = .twistedE6 := hpres₀.1
    have htg : tg = .twE6 := by
      clear * - htag
      revert htag
      cases tg <;> simp [markTag] <;> split_ifs <;> simp_all
    subst htg
    simpa [markDeg] using hdeg
  have hlab3 : 3 ∣ 2 ^ lab.n + 1 := by
    rw [hlabn]
    exact h3dvd
  have hK1 : LargeEvenLabelAll lab (fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L'),
            GGTwE6SCFourSetting I ψ A a₀ J₁ →
            LargeEvenMarking ↥J₁ fun lab' _ _ _ _ _ =>
              (lab' = ⟨.D, 4, lab.n⟩ ∨ lab' = ⟨.triD4, 0, lab.n⟩ ∨
                lab' = ⟨.A, 2, 3 * lab.n⟩ ∨ lab' = ⟨.twA, 2, 3 * lab.n⟩) ∨
              lab' = ⟨.twA, 5, lab.n⟩) :=
    CFSG.StandardType.SCFourCover.ggTwE6SCFourLabelsKnown_holds lab hlab hlabtw hlab3
  have hOUT : LargeEvenLabelAll lab (fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L'),
            GGTwE6SCFourSetting I ψ A a₀ J₁ →
            LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
              lab' = ⟨.D, 4, lab.n⟩ ∨ lab' = ⟨.triD4, 0, lab.n⟩ ∨
                lab' = ⟨.A, 2, 3 * lab.n⟩ ∨ lab' = ⟨.twA, 2, 3 * lab.n⟩) →
            ∃ a ∈ A, GGOutsideInndiag J₁ a) :=
    CFSG.StandardType.SCFourCover.ggTwE6SCFourOutKnown_holds lab hlab hlabtw hlab3
  have hrawInn := largeEvenRawDatum_inn_all hraw
  have hrawBoth := (largeEvenLabelAll_and hK1 hOUT) _ hrawInn
  obtain ⟨R, _, I, F, hcont⟩ := largeEvenRawDatum_exists hrawBoth
  rcases hcont with ⟨⟨hQ0, hInn⟩, ⟨hK1R, hOutR⟩⟩
  obtain ⟨hs, hna, θ, _⟩ := hQ0
  have hInner : ∀ a ∈ E, ∃ φ ∈ I, ∀ l : ↥G₀,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    intro a ha
    obtain ⟨b, hbA0, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨MulAut.conj (ggQuotHom θ b), hInn ⟨ggQuotHom θ b, rfl⟩, ?_⟩
    intro l
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have hSetting : GGTwE6SCFourSetting I (ggQuotHom θ) E a₀ L₀ := by
    unfold GGTwE6SCFourSetting
    exact ⟨hEel, hInner, hEcard, hEself, ha0E, ha0ne, hL0comp, hEnormL0, hCentL0⟩
  have hK1mark : LargeEvenMarking ↥L₀ (fun lab' _ _ _ _ _ =>
      (lab' = ⟨.D, 4, lab.n⟩ ∨ lab' = ⟨.triD4, 0, lab.n⟩ ∨
        lab' = ⟨.A, 2, 3 * lab.n⟩ ∨ lab' = ⟨.twA, 2, 3 * lab.n⟩) ∨
      lab' = ⟨.twA, 5, lab.n⟩) :=
    hK1R hs hna ↥G₀ (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hperfG0 E a₀ L₀ hSetting
  rcases largeEvenMarking_label_or hK1mark with hFirst | hTwA5
  · obtain ⟨α, hαE, hOutα⟩ :=
      hOutR hs hna ↥G₀ (ggQuotHom θ) (ggQuotHom_surjective θ)
        (by rw [ker_ggQuotHom]) hperfG0 E a₀ L₀ hSetting hFirst
    obtain ⟨b, hbA0, rfl⟩ := Subgroup.mem_map.mp hαE
    have hbA : (b : X) ∈ A := hbA0
    have hbB1 : (b : X) ∈ B₁ := hBA.symm ▸ hbA
    have hMarkL0 := rckExc_lMarking_subgroupOf hLG0 hMarkL
    have hJoint := ggMarkingAll_apply hOutα.2 hMarkL0
    obtain ⟨_, _, _, hraw0⟩ := hJoint
    obtain ⟨_, _, I0, _, _, _, θ0, hboth0⟩ := largeEvenRawDatum_exists hraw0
    rcases hboth0 with ⟨hact, hnot⟩
    obtain ⟨φ, hφ, hind⟩ := hact ((b : X)⁻¹) (B₁.inv_mem hbB1)
    exfalso
    refine hnot ⟨φ, Subgroup.subset_closure hφ, ?_⟩
    intro l l' hl
    apply hind l l'
    have hlX : ((l' : ↥G₀) : X) = (((MulAut.conj b) l : ↥G₀) : X) := congrArg Subtype.val hl
    simpa [MulAut.conj_apply, inv_inv] using hlX
  · have hTwAL : LargeEvenMarking ↥L (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, lab.n⟩) :=
      largeEvenMarking_congr (Subgroup.subgroupOfEquivOfLe hLG0).symm
        (fun _ _ _ _ _ _ h => h) hTwA5
    simpa [hlabn] using hTwAL

section RckExcCaseVInnerOnL

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem map_baseChangeGL_su6Levi
    {F L : Type} [Field F] [Field L] {σ : F ≃+* F} {δ : L ≃+* L}
    (ε : F →+* L) (hε : ∀ x, δ (ε x) = ε (σ x)) (hεsurj : Function.Surjective ε)
    {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hL : Nat.card L = (2 ^ f) ^ 2)
    (hσ : ∀ x, σ x = x ^ 2 ^ f) (hδ : ∀ x, δ x = x ^ 2 ^ f) :
    (CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom).map (baseChangeGL ε) =
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi δ.toRingHom := by
  rw [CFSG.SeitzReduction.TwistedE6Pilot.su6Levi,
    CFSG.SeitzReduction.TwistedE6Pilot.su6Levi]
  have hmap := Subgroup.map_inf_eq
    (subsystemGroup TwistTag.E6.tag F E6GraphLevi.setA)
    (graphFixedRootGroup TwistTag.E6 F σ.toRingHom) (baseChangeGL ε)
    (baseChangeGL_injective (τ := Tag.E6) (f := ε))
  rw [hmap]
  congr 1
  · rw [CFSG.RankThree.Chevalley.EvenF4QPlus.map_baseChangeGL_subsystemGroup ε E6GraphLevi.setA,
      Set.range_eq_univ.mpr hεsurj, subsystemGroup]
    simp
  · exact map_baseChangeGL_graphFixedRootGroup_eq (t := TwistTag.E6) (p := 2)
      Nat.prime_two hf F hF σ.toRingHom hσ ε hδ δ.surjective

theorem baseChangeGL_mem_twistedE6InndiagGL
    {F L : Type} [Field F] [Field L] {σ : F ≃+* F} {δ : L ≃+* L}
    (ε : F →+* L) (hε : ∀ x, δ (ε x) = ε (σ x)) (hεsurj : Function.Surjective ε)
    {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hL : Nat.card L = (2 ^ f) ^ 2)
    (hσ : ∀ x, σ x = x ^ 2 ^ f) (hδ : ∀ x, δ x = x ^ 2 ^ f)
    {g : ModGL TwistTag.E6.tag F} (hg : g ∈ twistedE6InndiagGL F σ) :
    baseChangeGL ε g ∈ twistedE6InndiagGL L δ := by
  have hroot : (twistedE6RootGroup F σ).map (baseChangeGL ε) =
      twistedE6RootGroup L δ :=
    map_baseChangeGL_graphFixedRootGroup_eq (t := TwistTag.E6) (p := 2)
      Nat.prime_two hf F hF σ.toRingHom hσ ε hδ δ.surjective
  have hdiag : (twistedE6DiagGL F σ).map (baseChangeGL ε) ≤ twistedE6DiagGL L δ := by
    rintro - ⟨x, hx, rfl⟩
    rw [twistedE6DiagGL] at hx
    obtain ⟨u, rfl⟩ := hx
    change baseChangeGL ε
      (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∈
      twistedE6DiagGL L δ
    rw [baseChangeGL_rootDiagUnit]
    let b : Fin Tag.E6.rank → Lˣ := fun i =>
      Units.map ε.toMonoidHom (compatDiag TwistTag.E6 σ.toRingHom u i)
    have hb : ∀ i, b (TwistTag.E6.perm i) = Units.map δ.toMonoidHom (b i) := by
      intro i
      apply Units.ext
      change ε (((compatDiag TwistTag.E6 σ.toRingHom u) (TwistTag.E6.perm i) : Fˣ) : F) =
        δ (ε (((compatDiag TwistTag.E6 σ.toRingHom u) i : Fˣ) : F))
      rw [compatDiag_perm]
      exact (hε _).symm
    obtain ⟨u', hu'⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := δ.toRingHom) hb
    rw [twistedE6DiagGL]
    exact ⟨u', by
      change rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 δ.toRingHom u') =
        rootDiagUnit TwistTag.E6.tag b
      rw [hu']⟩
  rw [twistedE6InndiagGL] at hg ⊢
  have hle : (twistedE6RootGroup F σ ⊔ twistedE6DiagGL F σ).map (baseChangeGL ε) ≤
      twistedE6RootGroup L δ ⊔ twistedE6DiagGL L δ := by
    rw [Subgroup.map_sup]
    exact sup_le ((le_of_eq hroot).trans le_sup_left) (hdiag.trans le_sup_right)
  exact hle (Subgroup.mem_map_of_mem (baseChangeGL ε) hg)

theorem mem_algebraMap_fieldRange_iff_pow {F Ω : Type} [Field F] [Finite F] [Field Ω]
    [Algebra F Ω] (a : Ω) :
    a ∈ (algebraMap F Ω).fieldRange ↔ a ^ Nat.card F = a := by
  rw [RingHom.mem_fieldRange]
  exact (TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap
    (K := F) (L := Ω) a).symm

theorem sigmaBar_eq_pow {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {f : ℕ}
    (hσ : ∀ x, σ x = x ^ 2 ^ f)
    (y : (algebraMap F (AlgebraicClosure F)).fieldRange) :
    ((algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv.symm.trans
        (σ.trans (algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv)) y =
      y ^ 2 ^ f := by
  obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp y.2
  have hy : y = (algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv x :=
    Subtype.ext hx.symm
  subst hy
  calc
    ((algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv.symm.trans
        (σ.trans (algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv))
        ((algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv x) =
        (algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv (σ x) := by
      rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
    _ = (algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv (x ^ 2 ^ f) := by
      rw [hσ x]
    _ = ((algebraMap F (AlgebraicClosure F)).rangeRestrictFieldEquiv x) ^ 2 ^ f := by
      rw [map_pow]

noncomputable def conjQuotientEquivRange (L : Type*) [Group L] :
    L ⧸ Subgroup.center L ≃* (MulAut.conj : L →* MulAut L).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.GroupTheory.ker_conj_eq_center (G := L)).symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : L →* MulAut L))

theorem conjQuotientEquivRange_mk {L : Type*} [Group L] (l : L) :
    conjQuotientEquivRange L (QuotientGroup.mk l) =
      ⟨MulAut.conj l, ⟨l, rfl⟩⟩ :=
  Subtype.ext rfl

theorem ker_normalizerAction_eq_centralizer
    {X : Type*} [Group X] {A L : Subgroup X}
    (hAL : A ≤ Subgroup.normalizer (L : Set X)) :
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)).ker =
      (Subgroup.centralizer (L : Set X)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hmem : Subgroup.inclusion hAL a ∈ L.normalizerMonoidHom.ker := h
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro h
    have hmem : Subgroup.inclusion hAL a ∈ L.normalizerMonoidHom.ker := by
      rw [Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr h
    exact hmem

theorem ker_conjAction_quotient_equiv
    {X P : Type*} [Group X] [Group P] {A L : Subgroup X} {x : X}
    (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hα : ∀ a : A, (L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)) a ∈
      (MulAut.conj : ↥L →* MulAut ↥L).range)
    (hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x)
    (η : ↥L ⧸ Subgroup.center ↥L ≃* P) :
    (η.toMonoidHom.comp ((conjQuotientEquivRange ↥L).symm.toMonoidHom.comp
      ((L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)).codRestrict _ hα))).ker =
      (Subgroup.zpowers x).subgroupOf A := by
  let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  let αI : A →* (MulAut.conj : ↥L →* MulAut ↥L).range := α.codRestrict _ hα
  let cL := conjQuotientEquivRange ↥L
  have hαker : α.ker = (Subgroup.centralizer (L : Set X)).subgroupOf A :=
    ker_normalizerAction_eq_centralizer hAL
  have hαIker : αI.ker = α.ker := MonoidHom.ker_codRestrict α _ hα
  have hρker : (η.toMonoidHom.comp (cL.symm.toMonoidHom.comp αI)).ker = αI.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : cL.symm (αI a) = 1 := η.injective (by simpa using h)
      exact cL.symm.injective (by simpa using h1)
    · intro h
      simpa [h]
  change (η.toMonoidHom.comp (cL.symm.toMonoidHom.comp αI)).ker =
    (Subgroup.zpowers x).subgroupOf A
  rw [hρker, hαIker, hαker]
  rw [← Subgroup.inf_subgroupOf_left (Subgroup.centralizer (L : Set X)) A, hWeq]

theorem rckExcCaseV_model_data_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁)
    {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (hFcard : Nat.card F = (2 ^ f) ^ 2) (hσ : ∀ z, σ z = z ^ 2 ^ f)
    (eF : ↥G₀ ≃* twistedE6RootGroup F σ) :
    ∃ (x₀ : ↥G₀),
      let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
      let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
      let xF : twistedE6RootGroup F σ := eF x₀
      let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
      let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
      letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
      letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
      let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
        (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
      let bc : ModGL Tag.E6 F →* ModGL Tag.E6 (AlgebraicClosure F) :=
        baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F))
      let Xgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        A₀.map (bc.comp ι₀)
      let Cgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
          (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)))
      Nat.card k = 2 ^ f ∧
      (x₀ : X) ∈ D ∧ x₀ ∈ A₀ ∧ orderOf x₀ = 3 ∧
      A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers (x₀ : X) ∧
      CFSG.Assembly.IsComponentOf L
        (G₀ ⊓ Subgroup.centralizer ({(x₀ : X)} : Set X)) ∧
      CFSG.Open.IsComponentOf LF
        (Subgroup.centralizer ({xF} : Set (twistedE6RootGroup F σ))) ∧
      ∃ (c : twistedE6InndiagGL F σ) (Q : SL2 k) (m : ℕ),
        orderOf Q = Nat.card k + 1 ∧ Q ^ m ≠ 1 ∧
        (c : ModGL TwistTag.E6.tag F) * ι₀ x₀ * (c : ModGL TwistTag.E6.tag F)⁻¹ =
          (thetaSL2 F).comp
            (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m) ∧
        L₀.map ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
          CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom ∧
        ¬ CFSG.StandardType.SCFourCover.E6AdToral Xgeom ∧
        (∀ u ∈ Cgeom, u ^ 3 = 1 →
          (∀ y ∈ Xgeom, y * u = u * y) → u ∈ Xgeom)
 := by
  have hSelf := rckExcCaseV_selfCent_core h hV
  obtain ⟨hEself, _hEcard⟩ := hSelf
  have hcfg := h
  have hVcfg := hV
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, h3dvd, -, hcardA, hBA, hAG, hZ⟩ := hV
  have hxdata := rck_centralizer_L_eq_zpowers_core hcfg hBA
  obtain ⟨x, hxD, hx1, hxcomp, hWeq, -⟩ := hxdata
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hDA : D ≤ A := hBA ▸ hDB1
  have hxG : x ∈ G₀ := hAG (hDA hxD)
  have hx3 : x ^ 3 = 1 := hAel.2 x (hDA hxD)
  have hAL : A ≤ Subgroup.normalizer (L : Set X) := hBA ▸ hB1L
  have hsetup := rckExcCaseV_original_action hAG hAL hLG0 hWeq hxcomp hxG hx1 hAel
    hcardA hZ
  obtain ⟨hL0comp, hEnormL0, hCentL0, hinjConj, hA0el, _hEel, hx0A0, _ha0E, hx0ne, _ha0ne,
    hcardA0⟩ := hsetup
  let x₀ : ↥G₀ := ⟨x, hxG⟩
  let a₀ : MulAut ↥G₀ := MulAut.conj x₀
  let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
  let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  let AF : Subgroup (twistedE6RootGroup F σ) := A₀.map eF.toMonoidHom
  let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
  let xF : twistedE6RootGroup F σ := eF x₀
  let xFT : ModGL Tag.E6 F := xF.val
  let tx : twistedE6InndiagGL F σ :=
    ⟨xF.val, Subgroup.mem_sup_left xF.2⟩
  let E : Subgroup (MulAut (twistedE6RootGroup F σ)) := AF.map (MulAut.conj : (twistedE6RootGroup F σ) →* MulAut (twistedE6RootGroup F σ))
  have hZC : Subgroup.center (twistedE6RootGroup F σ) = ⊥ := by
    have hmap := Subgroup.map_center_eq eF
    rw [hZ, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hinjConjC : Function.Injective (MulAut.conj : (twistedE6RootGroup F σ) →* MulAut (twistedE6RootGroup F σ)) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hZC]
  have hx03 : x₀ ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx3F : xF ^ 3 = 1 := by
    have h : eF (x₀ ^ 3) = 1 := by rw [hx03, map_one]
    simpa using h
  have hxFne : xF ≠ 1 := by
    intro h1
    have h2 : x₀ = 1 := eF.injective (by simpa [xF] using h1)
    exact hx1 (congrArg Subtype.val h2)
  have hxordF : orderOf xF = 3 := orderOf_eq_prime hx3F hxFne
  have hx3Fmod : (xF.val) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hx3F
  have hxordFmod : orderOf (xF.val) = 3 :=
    orderOf_eq_prime hx3Fmod (fun h1 => hxFne (Subtype.ext h1))
  have htx3 : tx ^ 3 = 1 := by
    apply Subtype.ext
    change (xF.val) ^ 3 = 1
    exact hx3Fmod
  have htxne : tx ≠ 1 := by
    intro h1
    apply hxFne
    have h2 : xF.val = (1 : ModGL Tag.E6 F) := by
      have h3 : tx.val = (1 : ModGL Tag.E6 F) := congrArg Subtype.val h1
      simpa [tx] using h3
    exact Subtype.ext h2
  have hconjtx : twistedE6InndiagConj F σ tx = MulAut.conj xF := by
    refine MulEquiv.ext fun z => ?_
    apply Subtype.ext
    simpa [twistedE6InndiagConj_apply, MulAut.conj_apply, tx]
  have hAFel : IsElemAbelian 3 AF := hA0el.map eF.toMonoidHom
  have hEelModel : IsElemAbelian 3 E := hAFel.map (MulAut.conj : (twistedE6RootGroup F σ) →* MulAut (twistedE6RootGroup F σ))
  have hcardAF : Nat.card AF = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective eF.injective, hcardA0]
  have hcardE : Nat.card E = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hinjConjC, hcardAF]
  have hfE : twistedE6InndiagConj F σ tx ∈ E := by
    rw [hconjtx]
    exact Subgroup.mem_map_of_mem (MulAut.conj : (twistedE6RootGroup F σ) →* MulAut (twistedE6RootGroup F σ))
      (Subgroup.mem_map_of_mem eF.toMonoidHom (Subgroup.mem_subgroupOf.mpr hx0A0))
  have hEI : E ≤ (twistedE6InndiagConj F σ).range := by
    rintro - ⟨aF, haF, rfl⟩
    refine ⟨⟨aF.val, Subgroup.mem_sup_left aF.2⟩, ?_⟩
    refine MulEquiv.ext fun z => ?_
    apply Subtype.ext
    simpa [twistedE6InndiagConj_apply, MulAut.conj_apply]
  have hfixcent : ggFix (MulAut.conj xF : MulAut (twistedE6RootGroup F σ)) =
      Subgroup.centralizer ({xF} : Set (twistedE6RootGroup F σ)) :=
    CFSG.StandardType.E6ThreeEnd.ggFix_conj xF
  have hconjEF : MulAut.congr eF a₀ = MulAut.conj xF := by
    refine MulEquiv.ext fun z => ?_
    apply Subtype.ext
    simp [MulAut.congr_apply, MulAut.conj_apply, a₀, x₀, xF]
  have hfixmap0 : (ggFix a₀).map eF.toMonoidHom = ggFix (MulAut.congr eF a₀) :=
    (CFSG.StandardType.E6ThreeEnd.ggFix_congr eF a₀).symm
  have hLf : CFSG.Open.IsComponentOf LF (Subgroup.centralizer ({xF} : Set (twistedE6RootGroup F σ))) := by
    have hL0open : CFSG.Open.IsComponentOf L₀ (ggFix a₀) :=
      CFSG.Assembly.isComponentOf_iff_open.mp hL0comp
    have hmapcomp := CFSG.isComponentOf_map_mulEquiv eF hL0open
    rw [hfixmap0, hconjEF, hfixcent] at hmapcomp
    exact hmapcomp
  have hggFix_zp : ggFix (MulAut.conj xF : MulAut (twistedE6RootGroup F σ)) =
      CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (MulAut.conj xF)) := by
    ext c
    rw [mem_ggFix, CFSG.LieType.Seitz.mem_fixedPoints]
    exact ⟨fun hc φ hφ => by
      have hle : Subgroup.zpowers (MulAut.conj xF) ≤ MulAction.stabilizer (MulAut (twistedE6RootGroup F σ)) c :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hc)
      exact MulAction.mem_stabilizer_iff.1 (hle hφ),
      fun hc => hc _ (Subgroup.mem_zpowers _)⟩
  have hzp : Subgroup.zpowers (twistedE6InndiagConj F σ tx) =
      Subgroup.zpowers (MulAut.conj xF : MulAut (twistedE6RootGroup F σ)) := by rw [hconjtx]
  have hLfFix : CFSG.Open.IsComponentOf LF
      (CFSG.LieType.Seitz.fixedPoints
        (Subgroup.zpowers (twistedE6InndiagConj F σ tx))) := by
    rw [hzp, ← hggFix_zp, hfixcent]
    exact hLf
  have hEJ : ∀ e ∈ E, LF.map e.toMonoidHom = LF := by
    rintro - ⟨aF, haF, rfl⟩
    obtain ⟨a₀', ha₀', rfl⟩ := Subgroup.mem_map.mp haF
    change (Subgroup.map eF.toMonoidHom L₀).map
      (MulAut.conj (eF a₀')).toMonoidHom = Subgroup.map eF.toMonoidHom L₀
    apply le_antisymm
    · rintro - ⟨l, hl, rfl⟩
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      have hmem : MulAut.conj a₀' l₀ ∈ L₀ :=
        hEnormL0 (MulAut.conj a₀')
          (Subgroup.mem_map_of_mem (MulAut.conj : ↥G₀ →* MulAut ↥G₀) ha₀') l₀ hl₀
      change eF.toMonoidHom a₀' * eF.toMonoidHom l₀ * (eF.toMonoidHom a₀')⁻¹ ∈
        Subgroup.map eF.toMonoidHom L₀
      simpa only [MulAut.conj_apply, map_mul, map_inv] using
        (Subgroup.mem_map_of_mem eF.toMonoidHom hmem)
    · rintro - ⟨l₀, hl₀, rfl⟩
      refine Subgroup.mem_map.mpr
        ⟨MulAut.conj ((eF a₀')⁻¹) (eF l₀), ?_, ?_⟩
      · have hmem : MulAut.conj (a₀'⁻¹) l₀ ∈ L₀ :=
          hEnormL0 (MulAut.conj (a₀'⁻¹))
            (Subgroup.mem_map_of_mem (MulAut.conj : ↥G₀ →* MulAut ↥G₀)
              (A₀.inv_mem ha₀')) l₀ hl₀
        change a₀'⁻¹ * l₀ * (a₀'⁻¹)⁻¹ ∈ L₀ at hmem
        change (eF.toMonoidHom a₀')⁻¹ * eF.toMonoidHom l₀ *
          ((eF.toMonoidHom a₀')⁻¹)⁻¹ ∈ Subgroup.map eF.toMonoidHom L₀
        simpa only [map_mul, map_inv, inv_inv] using
          (Subgroup.mem_map_of_mem eF.toMonoidHom hmem)
      · change (eF a₀') * ((eF a₀')⁻¹ * eF l₀ * (eF a₀')⁻¹⁻¹) * (eF a₀')⁻¹ = eF l₀
        rw [inv_inv]
        calc (eF a₀') * ((eF a₀')⁻¹ * eF l₀ * eF a₀') * (eF a₀')⁻¹
            = ((eF a₀') * (eF a₀')⁻¹) * (eF l₀ * eF a₀') * (eF a₀')⁻¹ := by
              simp only [mul_assoc]
          _ = eF l₀ := by
              rw [mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hCJ : ∀ e ∈ E, (∀ c ∈ LF, e c = c) →
      e ∈ Subgroup.zpowers (twistedE6InndiagConj F σ tx) := by
    rintro - ⟨aF, haF, rfl⟩ hfix
    obtain ⟨a₀', ha₀', rfl⟩ := Subgroup.mem_map.mp haF
    change ∀ c ∈ Subgroup.map eF.toMonoidHom L₀, (MulAut.conj (eF a₀')) c = c at hfix
    have hfix0 : ∀ l ∈ L₀, MulAut.conj a₀' l = l := by
      intro l hl
      apply eF.injective
      have h := hfix (eF l) (Subgroup.mem_map_of_mem eF.toMonoidHom hl)
      simpa [MulAut.conj_apply, map_mul, map_inv] using h
    have hmem := hCentL0 (MulAut.conj a₀')
      (Subgroup.mem_map_of_mem (MulAut.conj : ↥G₀ →* MulAut ↥G₀) ha₀') hfix0
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc
      (MulAut.conj xF) ^ k = (MulAut.congr eF a₀) ^ k := by rw [hconjEF]
      _ = MulAut.congr eF (a₀ ^ k) :=
        (map_zpow (MulAut.congr eF).toMonoidHom a₀ k).symm
      _ = MulAut.congr eF (MulAut.conj a₀') := by rw [hk]
      _ = MulAut.conj (eF a₀') := by
        ext z
        simp [MulAut.congr_apply, MulAut.conj_apply]
  have hmarkL0 : LargeEvenMarking ↥L₀ (fun lab _ _ _ _ _ => lab = ⟨.twA, 5, f⟩) :=
    largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG0)
      (rckExcCaseV_marking_L_core hcfg hVcfg)
  have hmarkLF : LargeEvenMarking ↥LF (fun lab _ _ _ _ _ => lab = ⟨.twA, 5, f⟩) :=
    largeEvenMarking_of_mulEquiv
      (L₀.equivMapOfInjective eF.toMonoidHom eF.injective).symm hmarkL0
  haveI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hFcard
  haveI : IsAlgClosed (AlgebraicClosure F) := inferInstance
  haveI : CharP (AlgebraicClosure F) 2 := charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  let Fr : (AlgebraicClosure F) →+* (AlgebraicClosure F) := iterateFrobenius (AlgebraicClosure F) 2 f
  have hFr : ∀ c, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have hrat := CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
    (ℓ := 2) (f := f) Nat.prime_two hf F hFcard σ.toRingHom hσ (AlgebraicClosure F) Fr hFr
  obtain ⟨-, -, hder, -, -, -, -⟩ := hrat
  have hnorm := CFSG.LieType.Chevalley.exceptional_ambient_twisted_Frobenius_fixed_normalizer
    (t := TwistTag.E6) Nat.prime_two hf F hFcard σ.toRingHom hσ (AlgebraicClosure F) Fr hFr
  obtain ⟨-, hleCR, -, -, -⟩ := hnorm
  let lam : ↥G₀ →* ModGL Tag.E6 (AlgebraicClosure F) :=
    (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F))).comp ((twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom)
  let Xgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) := A₀.map lam
  have hlam_inj : Function.Injective lam := by
    intro a b hab
    apply eF.injective
    apply Subtype.ext
    exact (baseChangeGL_injective (τ := Tag.E6) (f := algebraMap F (AlgebraicClosure F))) hab
  have hX3 : ∀ y ∈ Xgeom, y ^ 3 = 1 := by
    rintro - ⟨a, ha, rfl⟩
    rw [← map_pow, hA0el.2 a ha, map_one]
  have hXcard : Nat.card Xgeom = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hlam_inj, hcardA0]
  have hXleC : Xgeom ≤ (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
      (baseChangeGL (algebraMap F (AlgebraicClosure F))) := by
    rintro - ⟨a, ha, rfl⟩
    exact Subgroup.mem_map_of_mem (baseChangeGL (algebraMap F (AlgebraicClosure F))) (eF a).2
  have hXleR : Xgeom ≤ CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp (AlgebraicClosure F) Fr :=
    hXleC.trans hleCR
  have hSC' : ∀ u ∈ ⁅CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp (AlgebraicClosure F) Fr,
      CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp (AlgebraicClosure F) Fr⁆,
      u ^ 3 = 1 → (∀ y ∈ Xgeom, y * u = u * y) → u ∈ Xgeom := by
    intro u huDeriv hu3 hcomm
    have huC : u ∈ (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
        (baseChangeGL (algebraMap F (AlgebraicClosure F))) := by
      rw [← hder]
      exact huDeriv
    obtain ⟨z, hzC, hzu⟩ := Subgroup.mem_map.mp huC
    have hz3 : z ^ 3 = 1 := by
      apply baseChangeGL_injective (f := algebraMap F (AlgebraicClosure F))
      calc baseChangeGL (algebraMap F (AlgebraicClosure F)) (z ^ 3)
          = (baseChangeGL (algebraMap F (AlgebraicClosure F)) z) ^ 3 := map_pow _ _ _
        _ = u ^ 3 := congrArg (fun w => w ^ 3) hzu
        _ = 1 := hu3
        _ = baseChangeGL (algebraMap F (AlgebraicClosure F)) 1 := (map_one _).symm
    let zC : (twistedE6RootGroup F σ) := ⟨z, hzC⟩
    have hzC3 : zC ^ 3 = 1 := Subtype.ext (by simpa [zC] using hz3)
    obtain ⟨g, hg⟩ := eF.surjective zC
    have hgz : (eF g).val = z := congrArg Subtype.val hg
    have hg3 : g ^ 3 = 1 := by
      apply eF.injective
      rw [map_pow, hg, hzC3, map_one]
    have hzu' : u = lam g := by
      rw [← hzu, ← hgz]
      rfl
    have hgcent : ∀ a ∈ A₀, a * g = g * a := by
      intro a ha
      apply hlam_inj
      have h := hcomm (lam a) (Subgroup.mem_map_of_mem lam ha)
      simpa [map_mul, hzu'] using h
    have hgconjE : MulAut.conj g ∈ A₀.map (MulAut.conj : ↥G₀ →* MulAut ↥G₀) := by
      refine hEself g ?_ hg3
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      rw [MulAut.conj_apply]
      calc (b : ↥G₀) * g * b⁻¹ = (g * b) * b⁻¹ := by rw [hgcent b hb]
        _ = g := by rw [mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨a₀', ha₀', haeq⟩ := Subgroup.mem_map.mp hgconjE
    have hga : a₀' = g := hinjConj haeq
    have hgA0 : g ∈ A₀ := hga ▸ ha₀'
    rw [hzu']
    exact Subgroup.mem_map_of_mem lam hgA0
  have hntX : ¬ CFSG.StandardType.SCFourCover.E6AdToral Xgeom :=
    CFSG.StandardType.SCFourCover.not_e6AdToral_of_selfCent_derived hf Fr hFr h3dvd
      hXleR hX3 hXcard hSC'
  let Y : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
    (((E.comap (twistedE6InndiagConj F σ)).map
      (twistedE6InndiagGL F σ).subtype).map (baseChangeGL (algebraMap F (AlgebraicClosure F))))
  have hXY : Xgeom ≤ Y := by
    rintro - ⟨a, ha, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(eF a).val, ?_, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨⟨(eF a).val, Subgroup.mem_sup_left (eF a).2⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hc : twistedE6InndiagConj F σ
        ⟨(eF a).val, Subgroup.mem_sup_left (eF a).2⟩ = MulAut.conj (eF a) := by
      refine MulEquiv.ext fun z => ?_
      apply Subtype.ext
      simpa [twistedE6InndiagConj_apply, MulAut.conj_apply]
    rw [hc]
    exact Subgroup.mem_map_of_mem (MulAut.conj : (twistedE6RootGroup F σ) →* MulAut (twistedE6RootGroup F σ))
      (Subgroup.mem_map_of_mem eF.toMonoidHom ha)
  have hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral Y := fun htorY =>
    hntX (CFSG.StandardType.SCFourCover.e6AdToral_mono hXY htorY)
  have hS : CFSG.StandardType.SCFourCover.E6LeviThreeToralBar :=
    CFSG.StandardType.SCFourCover.e6LeviThreeToralBar
  have h36 : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6MatFixDim F σ tx = 36 :=
    CFSG.StandardType.SCFourCover.twE6MatFixDim_eq_36_of_twA5 hS hf h3dvd hFcard hσ
      (h := tx) htxne htx3 (E := E) hEelModel hcardE hfE hEI hnt
      (J := LF) hLfFix hEJ hCJ hmarkLF
  have hdim : Module.finrank F (LinearMap.ker
      ((Units.val tx.val : Module.End F (RootModule Tag.E6 F)) - 1)) = 36 := by
    change CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twE6MatFixDim F σ tx = 36
    exact h36
  have hcharF : ringChar F = 2 := ringChar.eq F 2
  have hKchars : ringChar F ≠ 3 := by rw [hcharF]; decide
  have hxL : baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)) xFT ∈
      adjointGroup Tag.E6 (AlgebraicClosure F) := by
    refine CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (f := algebraMap F (AlgebraicClosure F)) ?_
    exact CFSG.LieType.Chevalley.twistedFixedGroup_le_adjointGroup (t := TwistTag.E6)
      (K := F) (σ := σ.toRingHom)
      (CFSG.LieType.Chevalley.graphFixedRootGroup_le (t := TwistTag.E6) (K := F)
        (σ := σ.toRingHom) xF.2)
  obtain ⟨g, hg, ρ, hρ, ζ, hζ3, hζ1, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.exists_coroot_conj_of_cube_one_of_finrank_eq_thirtysix
      (K := F) hKchars hxL hx3Fmod hdim
  let gT : ModGL TwistTag.E6.tag (AlgebraicClosure F) := g
  have hgT : gT ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure F) := hg
  have hρT : IsRoot TwistTag.E6.tag ρ := hρ
  have htuple : (fun j => ζ ^ (CFSG.LieType.Steinberg.Adjoint.iform ρ
        (Pi.single j 1) : ℤ)) =
      CFSG.StandardType.TwE6RootAs.corootTuple ρ ζ := by
    funext i
    simp only [TwistTag.tag, CFSG.StandardType.TwE6RootAs.corootTuple,
      CFSG.RankThree.Lattice.iform_single_right_E6]
    rfl
  have hcor_geo : gT⁻¹ * baseChangeGL (algebraMap F (AlgebraicClosure F)) xF.val * gT =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag
        (CFSG.StandardType.TwE6RootAs.corootTuple ρ ζ) := by
    show g⁻¹ * baseChangeGL (algebraMap F (AlgebraicClosure F)) xFT * g =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6
        (CFSG.StandardType.TwE6RootAs.corootTuple ρ ζ)
    rw [← htuple]
    exact hconj
  let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
  letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
  letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
  have hk : Nat.card k = 2 ^ f := by
    change Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ f
    exact CFSG.LieType.SeitzGeneration.card_fixSubfield_sq Nat.prime_two hf hFcard σ hσ
  obtain ⟨c, hc, B, hB, m, hBm1, hcx⟩ :=
    CFSG.StandardType.TwE6CorootCore.exists_conj_eq_thetaSL2_pow_of_coroot_conj
      (K := F) σ hf hFcard hσ (k := k) hk gT hgT xF.val
      (Subgroup.mem_sup_left xF.2) ρ hρT 3 Nat.prime_three h3dvd ζ hζ3 hζ1 hcor_geo
  let c' : twistedE6InndiagGL F σ := ⟨c, hc⟩
  have hcx' : c'.val * xF.val *
      c'.val⁻¹ =
        (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F)) (B ^ m) := by
    simpa [c'] using hcx

  let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
    (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
  let bc : ModGL Tag.E6 F →* ModGL Tag.E6 (AlgebraicClosure F) :=
    baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F))
  let Cgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
    (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
      (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)))
  have hxord0 : orderOf x₀ = 3 := orderOf_eq_prime hx03 hx0ne
  let ρ₀ : SL2 k →* ModGL Tag.E6 F :=
    (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F))
  have hρ₀ : Function.Injective ρ₀ :=
    injective_thetaSL2_comp_map (two_eq_zero_of_card_sq hf hFcard) (algebraMap k F)
  have hQm3 : orderOf (B ^ m) = 3 := by
    calc
      orderOf (B ^ m) = orderOf (ρ₀ (B ^ m)) :=
        (orderOf_injective ρ₀ hρ₀ (B ^ m)).symm
      _ = orderOf (c'.val * xF.val * c'.val⁻¹) :=
        congrArg orderOf hcx'.symm
      _ = orderOf xF.val := by
        simpa only [MulAut.conj_apply] using
          (MulAut.conj c'.val).orderOf_eq xF.val
      _ = 3 := hxordFmod
  have hm3 : 3 ≤ orderOf (B ^ m) := by rw [hQm3]
  have hmapLF :=
    CFSG.StandardType.TwE6CorootCore.map_component_eq_su6Levi_of_conj_thetaSL2_pow
      σ hf hk hFcard hσ c' hLf (B := B) hB (m := m) hm3 hcx'
  have hLimage : L₀.map
      ((MulAut.conj (c' : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom := by
    simpa only [LF, ι₀, Subgroup.map_map, MonoidHom.comp_assoc] using hmapLF
  have hSCgeom : ∀ u ∈ Cgeom, u ^ 3 = 1 →
      (∀ y ∈ Xgeom, y * u = u * y) → u ∈ Xgeom := by
    intro u hu hu3 hcomm
    have hderTag : ⁅CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp
        (AlgebraicClosure F) Fr,
        CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.Rgrp
          (AlgebraicClosure F) Fr⁆ = Cgeom := by
      change ⁅twistedFixedGroup TwistTag.E6 (AlgebraicClosure F) Fr,
        twistedFixedGroup TwistTag.E6 (AlgebraicClosure F) Fr⁆ =
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
          (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)))
      exact hder
    apply hSC' u ?_ hu3 hcomm
    rw [hderTag]
    exact hu
  refine ⟨x₀, ?_⟩
  dsimp only
  exact ⟨hk, hxD, hx0A0, hxord0, hWeq, hxcomp, hLf,
    c', B, m, hB, hBm1, hcx', hLimage, hntX, hSCgeom⟩

theorem rckExcCaseV_exists_finite_model_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F)
      (eF : ↥G₀ ≃* twistedE6RootGroup F σ) (x₀ : ↥G₀),
      let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
      let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
      let xF : twistedE6RootGroup F σ := eF x₀
      let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
      let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
      letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
      letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
      let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
        (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
      let bc : ModGL Tag.E6 F →* ModGL Tag.E6 (AlgebraicClosure F) :=
        baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F))
      let Xgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        A₀.map (bc.comp ι₀)
      let Cgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
          (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)))
      Nat.card F = (2 ^ f) ^ 2 ∧
      (∀ z, σ z = z ^ 2 ^ f) ∧
      Nat.card k = 2 ^ f ∧
      (x₀ : X) ∈ D ∧ x₀ ∈ A₀ ∧ orderOf x₀ = 3 ∧
      A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers (x₀ : X) ∧
      CFSG.Assembly.IsComponentOf L
        (G₀ ⊓ Subgroup.centralizer ({(x₀ : X)} : Set X)) ∧
      CFSG.Open.IsComponentOf LF
        (Subgroup.centralizer ({xF} : Set (twistedE6RootGroup F σ))) ∧
      ∃ (c : twistedE6InndiagGL F σ) (Q : SL2 k) (m : ℕ),
        orderOf Q = Nat.card k + 1 ∧ Q ^ m ≠ 1 ∧
        (c : ModGL TwistTag.E6.tag F) * ι₀ x₀ * (c : ModGL TwistTag.E6.tag F)⁻¹ =
          (thetaSL2 F).comp
            (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m) ∧
        L₀.map ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
          CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom ∧
        ¬ CFSG.StandardType.SCFourCover.E6AdToral Xgeom ∧
        (∀ u ∈ Cgeom, u ^ 3 = 1 →
          (∀ y ∈ Xgeom, y * u = u * y) → u ∈ Xgeom)
 := by
  have hcfg := h
  have hVcfg := hV
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, -, -, -, -, -, hZ⟩ := hV
  unfold RCKCompCore at h
  obtain ⟨hGG, -⟩ := h
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hLieG0 : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .twistedE6 n 2 f := hGG.2.2.2
  obtain ⟨-, -, hTCM⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedChevalleyModel_of_lieModel hLieG0
  obtain ⟨F, hField, hFinite, σ, hFcard, hσ, ⟨ε⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.exists_twistedE6RootGroup_equiv
      Nat.prime_two hf hTCM
  letI : Field F := hField
  letI : Finite F := hFinite
  let eQ : ↥G₀ ≃* (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eF : ↥G₀ ≃* twistedE6RootGroup F σ := eQ.trans ε.symm
  obtain ⟨x₀, hx₀⟩ := rckExcCaseV_model_data_core hcfg hVcfg hFcard hσ eF
  refine ⟨F, hField, hFinite, σ, eF, x₀, ?_⟩
  dsimp only at hx₀ ⊢
  exact ⟨hFcard, hσ, hx₀⟩

theorem rckExcCaseV_inner_on_L_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹ := by

  obtain ⟨F, hField, hFinite, σ, eF, x₀, hdata⟩ :=
    rckExcCaseV_exists_finite_model_core h hV
  dsimp only at hdata
  obtain ⟨hFcard, hσ, hk, hxD, hx0A0, hxord0, hWeq, hxcomp, hLf,
    c, Q, m, hB, hBm1, hcx, hLimage, hntX, hSCgeom⟩ := hdata
  let x : X := (x₀ : X)
  letI : Field F := hField
  letI : Finite F := hFinite
  let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
  letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
  letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
  let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
  let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  let xF : twistedE6RootGroup F σ := eF x₀
  let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
  let c' : twistedE6InndiagGL F σ := c
  let B : SL2 k := Q
  have hxordF : orderOf xF = 3 := by
    change orderOf (eF.toMonoidHom x₀) = 3
    rw [orderOf_injective eF.toMonoidHom eF.injective x₀]
    exact hxord0
  have hcxF : (c : ModGL TwistTag.E6.tag F) *
      (((twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom) x₀) *
      (c : ModGL TwistTag.E6.tag F)⁻¹ =
      (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m) := by
    simpa only [k] using hcx
  have hcx' : c'.val * xF.val * c'.val⁻¹ =
      (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F)) (B ^ m) := by
    change c'.val *
      (((twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom) x₀) *
      c'.val⁻¹ =
      (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F)) (B ^ m)
    simpa only [c', B] using hcxF
  have hcfg := h
  have hVcfg := hV
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, h3dvd, -, -, hBA, hAG, -⟩ := hV
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hDA : D ≤ A := hBA ▸ hDB1

  intro a ha
  let a₀' : ↥G₀ := ⟨a, hAG ha⟩
  let aF : (twistedE6RootGroup F σ) := eF a₀'
  have haxF : aF * xF = xF * aF := by
    have hcommX : a * x = x * a := by
      have := hAel.1.is_comm.comm ⟨a, ha⟩ ⟨x, hDA hxD⟩
      exact congrArg Subtype.val this
    have hcommG0 : a₀' * x₀ = x₀ * a₀' := Subtype.ext hcommX
    calc
      aF * xF = eF (a₀' * x₀) := by rw [map_mul]
      _ = eF (x₀ * a₀') := by rw [hcommG0]
      _ = xF * aF := by rw [map_mul]
  obtain ⟨lF, hlF, hact⟩ :=
    CFSG.StandardType.TwE6CorootCore.exists_inner_on_component_of_conj_thetaSL2_pow
      (K := F) (k := k) σ hf hk hFcard hσ h3dvd c' hxordF hLf hB hcx' aF haxF
  obtain ⟨l₀, hl₀, hlmap⟩ := Subgroup.mem_map.mp hlF
  refine ⟨(l₀ : X), Subgroup.mem_subgroupOf.mp hl₀, fun y hy => ?_⟩
  let y₀ : ↥G₀ := ⟨y, hLG0 hy⟩
  have hyF : eF y₀ ∈ LF :=
    Subgroup.mem_map_of_mem eF.toMonoidHom (Subgroup.mem_subgroupOf.mpr hy)
  have hacty := hact (eF y₀) hyF
  have hacty' : aF * eF y₀ * aF⁻¹ = eF l₀ * eF y₀ * (eF l₀)⁻¹ := by
    simpa [← hlmap] using hacty
  have hG0 : a₀' * y₀ * a₀'⁻¹ = l₀ * y₀ * l₀⁻¹ := by
    apply eF.injective
    simp only [map_mul, map_inv]
    change eF a₀' * eF y₀ * (eF a₀')⁻¹ = eF l₀ * eF y₀ * (eF l₀)⁻¹
    simpa only [aF, ← hlmap] using hacty'
  simpa using congrArg Subtype.val hG0

theorem rckExcCaseV_inner_on_L
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹ :=
  rckExcCaseV_inner_on_L_core (rckCompCore_of_rpConfig h) hV

theorem exists_canonical_fieldRange_frame
    {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {f : ℕ}
    (hf : 1 ≤ f) (hFcard : Nat.card F = (2 ^ f) ^ 2)
    (hσ : ∀ z, σ z = z ^ 2 ^ f)
    {H : Type} [Group H] {A L : Subgroup H} {x : H}
    (hxA : x ∈ A) (hx3 : orderOf x = 3) (hAe : CFSG.Open.IsElemAbelian 3 A)
    {k : Type} [Field k] [Algebra k F] (hk : Nat.card k = 2 ^ f)
    {ι₀ : H →* ModGL TwistTag.E6.tag F} (hι₀ : Function.Injective ι₀)
    (hrange : ι₀.range = twistedE6RootGroup F σ)
    {c : twistedE6InndiagGL F σ} {Q : SL2 k} {m : ℕ}
    (hQ : orderOf Q = Nat.card k + 1) (hQm : Q ^ m ≠ 1)
    (hcx : (c : ModGL TwistTag.E6.tag F) * ι₀ x * (c : ModGL TwistTag.E6.tag F)⁻¹ =
      (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m))
    (hL : L.map ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom) :
    let Ω := AlgebraicClosure F
    let j : F →+* Ω := algebraMap F Ω
    let Fbar : Subfield Ω := j.fieldRange
    let ε : F ≃+* Fbar := j.rangeRestrictFieldEquiv
    let σbar : Fbar ≃+* Fbar := ε.symm.trans (σ.trans ε)
    letI : Algebra k Fbar := (ε.toRingHom.comp (algebraMap k F)).toAlgebra
    letI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hFcard
    letI : CharP Ω 2 := charP_of_injective_algebraMap
      (algebraMap F (AlgebraicClosure F)).injective 2
    let bε : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag Fbar := baseChangeGL (τ := Tag.E6) ε.toRingHom
    let ιbar : H →* ModGL TwistTag.E6.tag Fbar := bε.comp ι₀
    ∃ (cbar : twistedE6InndiagGL Fbar σbar),
      (cbar : ModGL TwistTag.E6.tag Fbar) = bε c.val ∧
      (cbar : ModGL TwistTag.E6.tag Fbar) * ιbar x * (cbar : ModGL TwistTag.E6.tag Fbar)⁻¹ =
        (thetaSL2 Fbar).comp (Matrix.SpecialLinearGroup.map (algebraMap k Fbar)) (Q ^ m) ∧
      L.map ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar) =
        CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom ∧
      ∃ n : ModGL TwistTag.E6.tag Ω, n ∈ (thetaSL2 Ω).range ∧
        (∃ a : Fbarˣ, n⁻¹ * twistHom TwistTag.E6 Ω
            (iterateFrobeniusEquiv Ω 2 f).toRingHom n =
          thetaSL2 Ω (Matrix.SpecialLinearGroup.map Fbar.subtype (nSL a))) ∧
        ∃ S : Matrix.SpecialLinearGroup (Fin 6) Ω,
          let ι : H →* ModGL TwistTag.E6.tag Ω :=
            (MulAut.conj n⁻¹).toMonoidHom.comp
              ((baseChangeGL (τ := Tag.E6) Fbar.subtype).comp
                ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar))
          let X : Subgroup (ModGL TwistTag.E6.tag Ω) := A.map ι
          let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL TwistTag.E6.tag Ω := E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
          X ≤ torusGroup Tag.E6 Ω ⊔ ψ.range ∧
            L.map ι = (CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom).map
              (baseChangeGL (τ := Tag.E6) Fbar.subtype) ∧
            (∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω, ψ S * ψ Y * (ψ S)⁻¹ =
              ψ (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL S) Y)) ∧
            (∀ g, g ∈ L.map ι ↔
              ∃ Y ∈ CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 6) (iterateFrobeniusEquiv Ω 2 f)),
                g = ψ S * ψ Y * (ψ S)⁻¹) ∧
            (∃ ζ : Fbarˣ, orderOf ζ = 3 ∧
              ι x = rootDiagUnit Tag.E6 (CFSG.SeitzReduction.EPilot.highDiag .E6
                (Units.map Fbar.subtype.toMonoidHom ζ))) ∧
            (∃ J6 : Matrix.SpecialLinearGroup (Fin 6) Ω,
              (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω ∧
                (ψ S)⁻¹ * twistHom TwistTag.E6 Ω
                  (iterateFrobeniusEquiv Ω 2 f).toRingHom (ψ S) = ψ J6) ∧
            ∃ (Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L)
              (θ : ↥L ⧸ Subgroup.center ↥L ≃*
                LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))),
              (∀ s, ι (Φ s : H) =
                ψ S * ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f) s) * (ψ S)⁻¹) ∧
                ∀ s, θ (QuotientGroup.mk (Φ s)) =
                  LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) s := by
  classical
  let Ω := AlgebraicClosure F
  let j : F →+* Ω := algebraMap F Ω
  let Fbar : Subfield Ω := j.fieldRange
  let ε : F ≃+* Fbar := j.rangeRestrictFieldEquiv
  let σbar : Fbar ≃+* Fbar := ε.symm.trans (σ.trans ε)
  letI : Algebra k Fbar := (ε.toRingHom.comp (algebraMap k F)).toAlgebra
  haveI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hFcard
  haveI : CharP Ω 2 := charP_of_injective_algebraMap
    (algebraMap F (AlgebraicClosure F)).injective 2
  let bε : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag Fbar := baseChangeGL (τ := Tag.E6) ε.toRingHom
  let ιbar : H →* ModGL TwistTag.E6.tag Fbar := bε.comp ι₀
  have hFbarcard : Nat.card Fbar = (2 ^ f) ^ 2 := by
    rw [← Nat.card_congr ε.toEquiv]
    exact hFcard
  have hFmem : ∀ a : Ω, a ∈ Fbar ↔ a ^ ((2 ^ f) ^ 2) = a := by
    intro a
    change a ∈ (algebraMap F Ω).fieldRange ↔ a ^ ((2 ^ f) ^ 2) = a
    rw [mem_algebraMap_fieldRange_iff_pow (F := F) a, hFcard]
  have hσbar : ∀ z : Fbar, σbar z = z ^ 2 ^ f := sigmaBar_eq_pow hσ
  have hιbar_inj : Function.Injective ιbar :=
    (baseChangeGL_injective (τ := Tag.E6) (f := ε.toRingHom)).comp hι₀
  have hrangebar : ιbar.range = twistedE6RootGroup Fbar σbar := by
    change (bε.comp ι₀).range = twistedE6RootGroup Fbar σbar
    rw [MonoidHom.range_comp, hrange, twistedE6RootGroup, twistedE6RootGroup]
    change Subgroup.map (baseChangeGL (τ := Tag.E6) ε.toRingHom)
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom) =
      graphFixedRootGroup TwistTag.E6 Fbar σbar.toRingHom
    exact map_baseChangeGL_graphFixedRootGroup_eq (t := TwistTag.E6) (p := 2)
      Nat.prime_two hf F hFcard σ.toRingHom hσ ε.toRingHom hσbar σbar.surjective
  have hεbar : ∀ z, σbar (ε.toRingHom z) = ε.toRingHom (σ z) := by
    intro z
    simp [σbar]
  have hcbar : bε c.val ∈ twistedE6InndiagGL Fbar σbar :=
    baseChangeGL_mem_twistedE6InndiagGL ε.toRingHom hεbar ε.surjective hf
      hFcard hFbarcard hσ hσbar c.2
  let cb : ModGL TwistTag.E6.tag Fbar := bε c.val
  let cbar : twistedE6InndiagGL Fbar σbar := ⟨cb, hcbar⟩
  have hcxbar : cb * ιbar x * cb⁻¹ =
      (thetaSL2 Fbar).comp (Matrix.SpecialLinearGroup.map (algebraMap k Fbar)) (Q ^ m) := by
    have h := congrArg bε hcx
    change bε ((c : ModGL TwistTag.E6.tag F) * ι₀ x * (c : ModGL TwistTag.E6.tag F)⁻¹) =
      bε ((thetaSL2 F).comp
        (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m)) at h
    have hmapθ : bε ((thetaSL2 F).comp
        (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m)) =
        (thetaSL2 Fbar).comp
          (Matrix.SpecialLinearGroup.map (algebraMap k Fbar)) (Q ^ m) := by
      change baseChangeGL (τ := TwistTag.E6.tag) ε.toRingHom
        (rootSL2 TwistTag.E6.tag F e6HighestRoot
          (Matrix.SpecialLinearGroup.map (algebraMap k F) (Q ^ m))) = _
      rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field
        (τ := TwistTag.E6.tag) (K := F) (L := Fbar) (f := ε.toRingHom) (β := e6HighestRoot)]
      change rootSL2 TwistTag.E6.tag Fbar e6HighestRoot
        (Matrix.SpecialLinearGroup.map ε.toRingHom
          (Matrix.SpecialLinearGroup.map (algebraMap k F) (Q ^ m))) =
        rootSL2 TwistTag.E6.tag Fbar e6HighestRoot
          (Matrix.SpecialLinearGroup.map (algebraMap k Fbar) (Q ^ m))
      congr 1
    rw [hmapθ] at h
    change bε (c.val) * bε (ι₀ x) * (bε c.val)⁻¹ = _
    simpa only [map_mul, map_inv] using h
  have hLbar : L.map ((MulAut.conj cb).toMonoidHom.comp ιbar) =
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom := by
    have h := congrArg (Subgroup.map bε) hL
    rw [Subgroup.map_map] at h
    have hcomp : bε.comp
        ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
        (MulAut.conj cb).toMonoidHom.comp ιbar := by
      refine MonoidHom.ext fun l => ?_
      change bε ((c : ModGL TwistTag.E6.tag F) * ι₀ l *
          (c : ModGL TwistTag.E6.tag F)⁻¹) =
        bε (c : ModGL TwistTag.E6.tag F) * bε (ι₀ l) *
          (bε (c : ModGL TwistTag.E6.tag F))⁻¹
      rw [map_mul, map_mul, map_inv]
    rw [hcomp] at h
    exact h.trans (map_baseChangeGL_su6Levi ε.toRingHom hεbar ε.surjective hf
      hFcard hFbarcard hσ hσbar)
  obtain ⟨n, hn, ⟨a, ha⟩, S, hX, hLmap, hS, hFix, hζ, hJ6, Φ, θ, hΦ, hθ⟩ :=
    CFSG.StandardType.SCFourCover.exists_standardSU6Frame_of_original_data
      (Ω := Ω) (f := f) hf (F := Fbar)
      hFbarcard hFmem (σQ := iterateFrobeniusEquiv Ω 2 f)
      (fun c => iterateFrobeniusEquiv_def (R := Ω) (p := 2) (n := f) c)
      (σ := σbar) hσbar (k := k) hk
      (H := H) (ι₀ := ιbar) hιbar_inj hrangebar (A := A) (L := L) (x := x)
      hxA hx3 hAe (c := cbar) (Q := Q) (m := m) hQ hQm hcxbar hLbar
  exact ⟨cbar, rfl, hcxbar, hLbar, n, hn, ⟨a, ha⟩, S, hX, hLmap, hS, hFix, hζ, hJ6,
    Φ, θ, hΦ, hθ⟩

theorem rckExcCaseV_exists_original_canonical_frame_core
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L : Subgroup X}
    (h : RCKCompCore t n f ψ p G₀ A B₁ D J L)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F)
      (eF : ↥G₀ ≃* twistedE6RootGroup F σ) (x₀ : ↥G₀)
      (hf : 1 ≤ f) (hFcard : Nat.card F = (2 ^ f) ^ 2),
      let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
      let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
      let xF : twistedE6RootGroup F σ := eF x₀
      let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
      let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
      letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
      letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
      letI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hFcard
      let Ω := AlgebraicClosure F
      let j : F →+* Ω := algebraMap F Ω
      let Fbar : Subfield Ω := j.fieldRange
      let ε : F ≃+* Fbar := j.rangeRestrictFieldEquiv
      let σbar : Fbar ≃+* Fbar := ε.symm.trans (σ.trans ε)
      letI : Algebra k Fbar := (ε.toRingHom.comp (algebraMap k F)).toAlgebra
      letI : CharP Ω 2 := charP_of_injective_algebraMap
        (algebraMap F (AlgebraicClosure F)).injective 2
      let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
        (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
      let bc : ModGL Tag.E6 F →* ModGL Tag.E6 (AlgebraicClosure F) :=
        baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F))
      let Xgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        A₀.map (bc.comp ι₀)
      let Cgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
          (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)))
      let bε : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag Fbar :=
        baseChangeGL (τ := Tag.E6) ε.toRingHom
      let ιbar : ↥G₀ →* ModGL TwistTag.E6.tag Fbar := bε.comp ι₀
      Nat.card F = (2 ^ f) ^ 2 ∧
      (∀ z, σ z = z ^ 2 ^ f) ∧
      Nat.card k = 2 ^ f ∧
      (x₀ : X) ∈ D ∧ x₀ ∈ A₀ ∧ orderOf x₀ = 3 ∧
      A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers (x₀ : X) ∧
      CFSG.Assembly.IsComponentOf L
        (G₀ ⊓ Subgroup.centralizer ({(x₀ : X)} : Set X)) ∧
      CFSG.Open.IsComponentOf LF
        (Subgroup.centralizer ({xF} : Set (twistedE6RootGroup F σ))) ∧
      ¬ CFSG.StandardType.SCFourCover.E6AdToral Xgeom ∧
      (∀ u ∈ Cgeom, u ^ 3 = 1 →
        (∀ y ∈ Xgeom, y * u = u * y) → u ∈ Xgeom) ∧
      ∃ (c : twistedE6InndiagGL F σ) (Q : SL2 k) (m : ℕ),
        orderOf Q = Nat.card k + 1 ∧ Q ^ m ≠ 1 ∧
        (c : ModGL TwistTag.E6.tag F) * ι₀ x₀ * (c : ModGL TwistTag.E6.tag F)⁻¹ =
          (thetaSL2 F).comp
            (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m) ∧
        L₀.map ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
          CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom ∧
        ∃ (cbar : twistedE6InndiagGL Fbar σbar),
          (cbar : ModGL TwistTag.E6.tag Fbar) = bε c.val ∧
          (cbar : ModGL TwistTag.E6.tag Fbar) * ιbar x₀ *
              (cbar : ModGL TwistTag.E6.tag Fbar)⁻¹ =
            (thetaSL2 Fbar).comp (Matrix.SpecialLinearGroup.map (algebraMap k Fbar)) (Q ^ m) ∧
          L₀.map ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar) =
            CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom ∧
          ∃ nθ : ModGL TwistTag.E6.tag Ω, nθ ∈ (thetaSL2 Ω).range ∧
            (∃ a : Fbarˣ, nθ⁻¹ * twistHom TwistTag.E6 Ω
                (iterateFrobeniusEquiv Ω 2 f).toRingHom nθ =
              thetaSL2 Ω (Matrix.SpecialLinearGroup.map Fbar.subtype (nSL a))) ∧
            ∃ S : Matrix.SpecialLinearGroup (Fin 6) Ω,
              let ι : ↥G₀ →* ModGL TwistTag.E6.tag Ω :=
                (MulAut.conj nθ⁻¹).toMonoidHom.comp
                  ((baseChangeGL (τ := Tag.E6) Fbar.subtype).comp
                    ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar))
              let X : Subgroup (ModGL TwistTag.E6.tag Ω) := A₀.map ι
              let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL TwistTag.E6.tag Ω :=
                E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
              X ≤ torusGroup Tag.E6 Ω ⊔ ψ.range ∧
                L₀.map ι = (CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom).map
                  (baseChangeGL (τ := Tag.E6) Fbar.subtype) ∧
                (∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω, ψ S * ψ Y * (ψ S)⁻¹ =
                  ψ (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL S) Y)) ∧
                (∀ g, g ∈ L₀.map ι ↔
                  ∃ Y ∈ CFSG.RankThree.Classical2.fixSubgroup
                    (stdUnitaryEquiv (ν := 6) (iterateFrobeniusEquiv Ω 2 f)),
                    g = ψ S * ψ Y * (ψ S)⁻¹) ∧
                (∃ ζ : Fbarˣ, orderOf ζ = 3 ∧
                  ι x₀ = rootDiagUnit Tag.E6 (CFSG.SeitzReduction.EPilot.highDiag .E6
                    (Units.map Fbar.subtype.toMonoidHom ζ))) ∧
                (∃ J6 : Matrix.SpecialLinearGroup (Fin 6) Ω,
                  (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω ∧
                    (ψ S)⁻¹ * twistHom TwistTag.E6 Ω
                      (iterateFrobeniusEquiv Ω 2 f).toRingHom (ψ S) = ψ J6) ∧
                ∃ (Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L₀)
                  (θ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃*
                    LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))),
                  (∀ s, ι (Φ s : ↥G₀) =
                    ψ S * ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f) s) *
                      (ψ S)⁻¹) ∧
                    ∀ s, θ (QuotientGroup.mk (Φ s)) =
                      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) s := by
  classical
  obtain ⟨F, hField, hFinite, σ, eF, x₀, hdata⟩ :=
    rckExcCaseV_exists_finite_model_core h hV
  dsimp only at hdata
  obtain ⟨hFcard, hσ, hk, hxD, hx0A0, hxord0, hWeq, hxcomp, hLf,
    c, Q, m, hQ, hQm, hcx, hL, hntX, hSCgeom⟩ := hdata
  letI : Field F := hField
  letI : Finite F := hFinite
  let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
  letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
  letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
  let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
  let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  let xF : twistedE6RootGroup F σ := eF x₀
  let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
  let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
    (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
  have hcfg := h
  have hVcfg := hV
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, h3dvd, -, hcardA, hBA, hAG, hZ⟩ := hV
  unfold RCKCompCore at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6⟩
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hAe : CFSG.Open.IsElemAbelian 3 A₀ := hAel.subgroupOf G₀
  have hι₀_inj : Function.Injective ι₀ := by
    intro a b hab
    exact eF.injective (Subtype.ext hab)
  have hrange : ι₀.range = twistedE6RootGroup F σ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (eF x).2
    · intro hy
      exact ⟨eF.symm ⟨y, hy⟩, by simp [ι₀]⟩
  have hcx' : (c : ModGL TwistTag.E6.tag F) * ι₀ x₀ *
        (c : ModGL TwistTag.E6.tag F)⁻¹ =
      (thetaSL2 F).comp
        (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m) := by
    simpa only [ι₀] using hcx
  have hL' : L₀.map ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom := by
    simpa only [ι₀, L₀] using hL
  obtain ⟨cbar, hcbar_eq, hcxbar, hLbar, nθ, hnθ, ⟨a, ha⟩, S, hX, hLmap, hS, hFix,
    ⟨ζ, hζ3, hζeq⟩, ⟨J6, hJ6mat, hJ6eq⟩, Φ, θ, hΦ, hθ⟩ :=
    exists_canonical_fieldRange_frame (F := F) (σ := σ) (f := f) hf hFcard hσ
      (H := ↥G₀) (A := A₀) (L := L₀) (x := x₀) hx0A0 hxord0 hAe hk
      (ι₀ := ι₀) hι₀_inj hrange hQ hQm hcx' hL'
  exact ⟨F, hField, hFinite, σ, eF, x₀, hf, hFcard,
    hFcard, hσ, hk, hxD, hx0A0, hxord0, hWeq, hxcomp, hLf, hntX, hSCgeom,
    c, Q, m, hQ, hQm, hcx', hL', cbar, hcbar_eq, hcxbar, hLbar,
    nθ, hnθ, ⟨a, ha⟩, S, hX, hLmap, hS, hFix,
    ⟨ζ, hζ3, hζeq⟩, ⟨J6, hJ6mat, hJ6eq⟩, Φ, θ, hΦ, hθ⟩

theorem rckExcCaseV_exists_original_canonical_frame
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F)
      (eF : ↥G₀ ≃* twistedE6RootGroup F σ) (x₀ : ↥G₀)
      (hf : 1 ≤ f) (hFcard : Nat.card F = (2 ^ f) ^ 2),
      let A₀ : Subgroup ↥G₀ := A.subgroupOf G₀
      let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
      let xF : twistedE6RootGroup F σ := eF x₀
      let LF : Subgroup (twistedE6RootGroup F σ) := L₀.map eF.toMonoidHom
      let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
      letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
      letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
      letI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hFcard
      let Ω := AlgebraicClosure F
      let j : F →+* Ω := algebraMap F Ω
      let Fbar : Subfield Ω := j.fieldRange
      let ε : F ≃+* Fbar := j.rangeRestrictFieldEquiv
      let σbar : Fbar ≃+* Fbar := ε.symm.trans (σ.trans ε)
      letI : Algebra k Fbar := (ε.toRingHom.comp (algebraMap k F)).toAlgebra
      letI : CharP Ω 2 := charP_of_injective_algebraMap
        (algebraMap F (AlgebraicClosure F)).injective 2
      let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
        (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
      let bc : ModGL Tag.E6 F →* ModGL Tag.E6 (AlgebraicClosure F) :=
        baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F))
      let Xgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        A₀.map (bc.comp ι₀)
      let Cgeom : Subgroup (ModGL Tag.E6 (AlgebraicClosure F)) :=
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map
          (baseChangeGL (τ := Tag.E6) (algebraMap F (AlgebraicClosure F)))
      let bε : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag Fbar :=
        baseChangeGL (τ := Tag.E6) ε.toRingHom
      let ιbar : ↥G₀ →* ModGL TwistTag.E6.tag Fbar := bε.comp ι₀
      Nat.card F = (2 ^ f) ^ 2 ∧
      (∀ z, σ z = z ^ 2 ^ f) ∧
      Nat.card k = 2 ^ f ∧
      (x₀ : X) ∈ D ∧ x₀ ∈ A₀ ∧ orderOf x₀ = 3 ∧
      A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers (x₀ : X) ∧
      CFSG.Assembly.IsComponentOf L
        (G₀ ⊓ Subgroup.centralizer ({(x₀ : X)} : Set X)) ∧
      CFSG.Open.IsComponentOf LF
        (Subgroup.centralizer ({xF} : Set (twistedE6RootGroup F σ))) ∧
      ¬ CFSG.StandardType.SCFourCover.E6AdToral Xgeom ∧
      (∀ u ∈ Cgeom, u ^ 3 = 1 →
        (∀ y ∈ Xgeom, y * u = u * y) → u ∈ Xgeom) ∧
      ∃ (c : twistedE6InndiagGL F σ) (Q : SL2 k) (m : ℕ),
        orderOf Q = Nat.card k + 1 ∧ Q ^ m ≠ 1 ∧
        (c : ModGL TwistTag.E6.tag F) * ι₀ x₀ * (c : ModGL TwistTag.E6.tag F)⁻¹ =
          (thetaSL2 F).comp
            (Matrix.SpecialLinearGroup.map (algebraMap k F)) (Q ^ m) ∧
        L₀.map ((MulAut.conj (c : ModGL TwistTag.E6.tag F)).toMonoidHom.comp ι₀) =
          CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom ∧
        ∃ (cbar : twistedE6InndiagGL Fbar σbar),
          (cbar : ModGL TwistTag.E6.tag Fbar) = bε c.val ∧
          (cbar : ModGL TwistTag.E6.tag Fbar) * ιbar x₀ *
              (cbar : ModGL TwistTag.E6.tag Fbar)⁻¹ =
            (thetaSL2 Fbar).comp (Matrix.SpecialLinearGroup.map (algebraMap k Fbar)) (Q ^ m) ∧
          L₀.map ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar) =
            CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom ∧
          ∃ nθ : ModGL TwistTag.E6.tag Ω, nθ ∈ (thetaSL2 Ω).range ∧
            (∃ a : Fbarˣ, nθ⁻¹ * twistHom TwistTag.E6 Ω
                (iterateFrobeniusEquiv Ω 2 f).toRingHom nθ =
              thetaSL2 Ω (Matrix.SpecialLinearGroup.map Fbar.subtype (nSL a))) ∧
            ∃ S : Matrix.SpecialLinearGroup (Fin 6) Ω,
              let ι : ↥G₀ →* ModGL TwistTag.E6.tag Ω :=
                (MulAut.conj nθ⁻¹).toMonoidHom.comp
                  ((baseChangeGL (τ := Tag.E6) Fbar.subtype).comp
                    ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar))
              let X : Subgroup (ModGL TwistTag.E6.tag Ω) := A₀.map ι
              let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL TwistTag.E6.tag Ω :=
                E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
              X ≤ torusGroup Tag.E6 Ω ⊔ ψ.range ∧
                L₀.map ι = (CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σbar.toRingHom).map
                  (baseChangeGL (τ := Tag.E6) Fbar.subtype) ∧
                (∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω, ψ S * ψ Y * (ψ S)⁻¹ =
                  ψ (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL S) Y)) ∧
                (∀ g, g ∈ L₀.map ι ↔
                  ∃ Y ∈ CFSG.RankThree.Classical2.fixSubgroup
                    (stdUnitaryEquiv (ν := 6) (iterateFrobeniusEquiv Ω 2 f)),
                    g = ψ S * ψ Y * (ψ S)⁻¹) ∧
                (∃ ζ : Fbarˣ, orderOf ζ = 3 ∧
                  ι x₀ = rootDiagUnit Tag.E6 (CFSG.SeitzReduction.EPilot.highDiag .E6
                    (Units.map Fbar.subtype.toMonoidHom ζ))) ∧
                (∃ J6 : Matrix.SpecialLinearGroup (Fin 6) Ω,
                  (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω ∧
                    (ψ S)⁻¹ * twistHom TwistTag.E6 Ω
                      (iterateFrobeniusEquiv Ω 2 f).toRingHom (ψ S) = ψ J6) ∧
                ∃ (Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L₀)
                  (θ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃*
                    LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))),
                  (∀ s, ι (Φ s : ↥G₀) =
                    ψ S * ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f) s) *
                      (ψ S)⁻¹) ∧
                    ∀ s, θ (QuotientGroup.mk (Φ s)) =
                      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) s :=
  rckExcCaseV_exists_original_canonical_frame_core (rckCompCore_of_rpConfig h) hV

theorem exists_projective_action_kernel
    {X : Type} [Group X] [Finite X] {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ} {x : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁)
    {Fbar : Type} [Field Fbar] [Finite Fbar]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f Fbar)
    {L₀ : Subgroup ↥G₀} (eL : L₀ ≃* ↥L)
    {Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L₀}
    {θ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))}
    (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x)
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹) :
    let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
    let θL : ↥L ⧸ Subgroup.center ↥L ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
      (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
        (Subgroup.map_center_eq eL.symm)).trans θ
    let ΦL : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L := eL.toMonoidHom.comp Φ
    let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
    θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
    let π : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    let α : A →* MulAut ↥L :=
      L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
    ∃ (ρ : A →* P),
      ρ.ker = (Subgroup.zpowers x).subgroupOf A ∧
      (∀ (a : A) (l : ↥L), π (α a l) = ρ a * π l * (ρ a)⁻¹) ∧
      (∀ a : A, ρ a = 1 ↔ (a : X) ∈ Subgroup.zpowers x) := by
  classical
  let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
    (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
  let θL : ↥L ⧸ Subgroup.center ↥L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
    (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
      (Subgroup.map_center_eq eL.symm)).trans θ
  let ΦL : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L := eL.toMonoidHom.comp Φ
  let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
    θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
  let π : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hα : ∀ a : A, α a ∈ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    intro a
    obtain ⟨l, hl, hlact⟩ := hinner (a : X) a.2
    refine ⟨⟨l, hl⟩, ?_⟩
    ext y
    simp only [α, MonoidHom.comp_apply]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    change l * (y : X) * l⁻¹ = (a : X) * (y : X) * (a : X)⁻¹
    exact (hlact (y : X) y.2).symm
  let αI : A →* (MulAut.conj : ↥L →* MulAut ↥L).range := α.codRestrict _ hα
  let ρ : A →* P := η.toMonoidHom.comp ((conjQuotientEquivRange ↥L).symm.toMonoidHom.comp αI)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · exact ker_conjAction_quotient_equiv hAL hα hWeq η
  · intro a l
    obtain ⟨l₀, hl₀, hlact⟩ := hinner (a : X) a.2
    let la : ↥L := ⟨l₀, hl₀⟩
    have hαa : α a = MulAut.conj la := by
      ext y
      exact hlact (y : X) y.2
    have hcL : conjQuotientEquivRange ↥L (QuotientGroup.mk la) = αI a := by
      rw [conjQuotientEquivRange_mk]
      exact Subtype.ext hαa.symm
    have hρa : ρ a = η (QuotientGroup.mk la) := by
      change η ((conjQuotientEquivRange ↥L).symm (αI a)) = η (QuotientGroup.mk la)
      rw [← hcL, MulEquiv.symm_apply_apply]
    calc π (α a l) = η (QuotientGroup.mk (α a l)) := rfl
      _ = η (QuotientGroup.mk (la * l * la⁻¹)) := by rw [hαa, MulAut.conj_apply]
      _ = η (QuotientGroup.mk la * QuotientGroup.mk l * (QuotientGroup.mk la)⁻¹) := by
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      _ = η (QuotientGroup.mk la) * η (QuotientGroup.mk l) * (η (QuotientGroup.mk la))⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      _ = ρ a * π l * (ρ a)⁻¹ := by
        rw [hρa]
        rfl
  · intro a
    constructor
    · intro ha
      have hmem : a ∈ ρ.ker := ha
      rw [ker_conjAction_quotient_equiv hAL hα hWeq η] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro ha
      have hmem : a ∈ (Subgroup.zpowers x).subgroupOf A := Subgroup.mem_subgroupOf.mpr ha
      rw [← ker_conjAction_quotient_equiv hAL hα hWeq η] at hmem
      exact hmem

theorem exists_d_e_decomposition
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e x : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁)
    (hxD : x ∈ D) (hx1 : x ≠ 1) (hxord : orderOf x = 3)
    (hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x) :
    ∃ d ∈ D, d ∉ Subgroup.zpowers x ∧
      D = Subgroup.zpowers x ⊔ Subgroup.zpowers d ∧
      ∃ i j : ℤ, e = x ^ i * d ^ j := by
  have hcfg := h
  unfold RCKExcCaseVData at hV
  obtain ⟨rfl, rfl, h3dvd, h9dvd, hcardA, hBA, hAG, hZ⟩ := hV
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0, hx, hDnotc, hJcompL,
      hJnotA6, hRJ, hRmJ, hRootJ, heD, he1, hKcomp, hJK, hOddK⟩
  have hDA : D ≤ A := hBA ▸ hDB1
  have hDex : ∃ d, d ∈ D ∧ d ∉ Subgroup.centralizer (L : Set X) := by
    by_contra h
    apply hDnotc
    intro d hd
    by_contra hdc
    exact h ⟨d, hd, hdc⟩
  obtain ⟨d, hdD, hdC⟩ := hDex
  have hxinf : x ∈ A ⊓ Subgroup.centralizer (L : Set X) := by
    rw [hWeq]
    exact Subgroup.mem_zpowers x
  have hxC : x ∈ Subgroup.centralizer (L : Set X) := (Subgroup.mem_inf.mp hxinf).2
  have hzxC : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.zpowers_le.mpr hxC
  have hdx : d ∉ Subgroup.zpowers x := fun hd => hdC (hzxC hd)
  have hDelem : CFSG.Open.IsElemAbelian 3 D := hAel.mono hDA
  have hDcard3 : Nat.card D = 3 ^ 2 := by simpa using hDcard
  have hsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d :=
    CFSG.StandardType.eq_sup_zpowers_of_card Nat.prime_three hDelem hDcard3
      hxD hx1 hdD hdx
  obtain ⟨i, j, hij⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.exists_zpow_mul_zpow_of_card_eq_sq
      Nat.prime_three hDelem hDcard3 hxord hxD hdD hdx heD
  exact ⟨d, hdD, hdx, hsup, i, j, hij⟩

theorem exists_cube_one_su_lift
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e x : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁)
    (hDA : D ≤ A)
    (hxD : x ∈ D) (hx1 : x ≠ 1) (hxord : orderOf x = 3)
    {Fbar : Type} [Field Fbar] [Finite Fbar]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f Fbar)
    {L₀ : Subgroup ↥G₀} (eL : L₀ ≃* ↥L)
    {Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L₀}
    {θ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))}
    (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x)
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹) :
    let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
    let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
    let θL : ↥L ⧸ Subgroup.center ↥L ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
      (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
        (Subgroup.map_center_eq eL.symm)).trans θ
    let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
      θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
    let π : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    ∃ (ρ : A →* P),
      (ρ.ker = (Subgroup.zpowers x).subgroupOf A ∧
        (∀ (a : A) (l : ↥L), π (α a l) = ρ a * π l * (ρ a)⁻¹) ∧
        (∀ a : A, ρ a = 1 ↔ (a : X) ∈ Subgroup.zpowers x)) ∧
      ∃ (d : X) (hdD : d ∈ D), d ∉ Subgroup.zpowers x ∧
        D = Subgroup.zpowers x ⊔ Subgroup.zpowers d ∧
        (∃ i j : ℤ, e = x ^ i * d ^ j) ∧
        let dA : A := ⟨d, hDA hdD⟩
        ∃ Bsu : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6),
          (Bsu : P) = ρ dA ∧
          let B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
              (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) := ⟨Bsu, Bsu.2.1⟩
          (B : GL (Fin 6) Fbar) ^ 3 = 1 ∧
          (¬ ∃ c : Fbarˣ, (B : GL (Fin 6) Fbar) =
            Matrix.GeneralLinearGroup.scalar (Fin 6) c) ∧
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
              (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
            MulAut.conj (ρ dA)) ∧
          (∀ l : ↥L, π (α dA l) =
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
              (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B (π l)) := by
  classical
  let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
    (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
  let θL : ↥L ⧸ Subgroup.center ↥L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
    (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
      (Subgroup.map_center_eq eL.symm)).trans θ
  let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
    θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
  let π : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  obtain ⟨ρ, hρker, hρcov, hρ1⟩ :=
    exists_projective_action_kernel h hV hU eL (Φ := Φ) (θ := θ) hAL hWeq hinner
  obtain ⟨d, hdD, hdx, hsup, i, j, hij⟩ :=
    exists_d_e_decomposition h hV hxD hx1 hxord hWeq
  let dA : A := ⟨d, hDA hdD⟩
  let N := CFSG.ClassicalGroups.UnitaryFlag.normOneScalars hU
    (CFSG.ClassicalGroups.UnitaryFlag.gramSU hU (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)) 6
  obtain ⟨Bsu, hBsu⟩ := QuotientGroup.mk'_surjective N (ρ dA)
  have hd3 : dA ^ 3 = 1 := by
    have hcfg := h
    have hVcfg := hV
    unfold RCKExcCaseVData at hV
    obtain ⟨rfl, rfl, -, -, -, -, -, -⟩ := hV
    unfold RCKRPConfig at h
    obtain ⟨-, -, -, -, hAel, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -⟩ := h
    apply Subtype.ext
    simpa using hAel.2 dA dA.2
  have hρd3 : (ρ dA) ^ 3 = 1 := by
    rw [← map_pow, hd3, map_one]
  have hBsu3 : (Bsu : P) ^ 3 = 1 := by
    change (QuotientGroup.mk' N Bsu) ^ 3 = 1
    rw [hBsu]
    exact hρd3
  have h3 : 3 ∣ 2 ^ f + 1 := hV.2.2.1
  have h9 : ¬ 9 ∣ 2 ^ f + 1 := hV.2.2.2.1
  have hBsuGL3 : (Bsu : GL (Fin 6) Fbar) ^ 3 = 1 :=
    CFSG.AGLEmbedding.U62ThreeCent.pow_three_eq_one_of_mem_of_not_nine_dvd
      hU h3 h9 (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) Bsu hBsu3
  let B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) := ⟨Bsu, Bsu.2.1⟩
  have hB3 : (B : GL (Fin 6) Fbar) ^ 3 = 1 := by
    simpa [B] using hBsuGL3
  have hρd_ne : ρ dA ≠ 1 := by
    intro h
    have hmem : dA ∈ (Subgroup.zpowers x).subgroupOf A := (hρ1 dA).mp h
    exact hdx (Subgroup.mem_subgroupOf.mp hmem)
  have hBns : ¬ ∃ c : Fbarˣ, (B : GL (Fin 6) Fbar) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rintro ⟨c, hc⟩
    have hscalarU : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) := by
      rw [← hc]
      simpa [B] using B.2
    have hnorm : hU.norm (c : Fbar) = 1 :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.norm_eq_one_of_scalar_mem_primeFormUnitary
        hU (by norm_num) (1 : GL (Fin 6) Fbar) hscalarU
    have hc6 : c ^ 6 = 1 := by
      have hdet : ((Bsu : GL (Fin 6) Fbar) : Matrix (Fin 6) (Fin 6) Fbar).det = 1 :=
        Bsu.2.2
      have hdB : (((B : GL (Fin 6) Fbar) : Matrix (Fin 6) (Fin 6) Fbar).det) = 1 := by
        simpa [B] using hdet
      rw [hc] at hdB
      apply Units.ext
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdB
    have hmemN : Bsu ∈ N :=
      (CFSG.ClassicalGroups.UnitaryFlag.mem_normOneScalars).mpr
        ⟨c, hnorm, hc6, by simpa [B] using hc⟩
    have hclass : (Bsu : P) = 1 := (QuotientGroup.eq_one_iff _).mpr hmemN
    exact hρd_ne (by rw [← hBsu]; exact hclass)
  have hclass : (Bsu : P) = ρ dA := by
    change QuotientGroup.mk' N Bsu = ρ dA
    exact hBsu
  have hBconj : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B = MulAut.conj (ρ dA) := by
    have hdonor := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom_eq_conj
      (h := hU) (C := CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) Bsu
    change CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) ⟨Bsu, Bsu.2.1⟩ =
      MulAut.conj (ρ dA)
    rw [hdonor, hclass]
  have hcovB : ∀ l : ↥L, π (α dA l) =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B (π l) := by
    intro l
    rw [hBconj, MulAut.conj_apply]
    exact hρcov dA l
  exact ⟨ρ, ⟨hρker, hρcov, hρ1⟩, d, hdD, hdx, hsup, ⟨i, j, hij⟩,
    Bsu, hBsu, hB3, hBns, hBconj, hcovB⟩

theorem exists_JP_component
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e x : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hV : RCKExcCaseVData t f p G₀ A B₁)
    (hDA : D ≤ A)
    {Fbar : Type} [Field Fbar] [Finite Fbar]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f Fbar)
    {L₀ : Subgroup ↥G₀} (eL : L₀ ≃* ↥L)
    {Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥L₀}
    {θ : ↥L₀ ⧸ Subgroup.center ↥L₀ ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))}
    (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hAJ : A ≤ Subgroup.normalizer (J : Set X))
    (hWeq : A ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x)
    {d : X} (hdD : d ∈ D) (hsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d)
    {B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)} :
    let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
    let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
    let θL : ↥L ⧸ Subgroup.center ↥L ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
      (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
        (Subgroup.map_center_eq eL.symm)).trans θ
    let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
      θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
    let π : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
    ∀ (ρ : A →* P),
      (∀ (a : A) (l : ↥L), π (α a l) = ρ a * π l * (ρ a)⁻¹) →
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
        MulAut.conj (ρ ⟨d, hDA hdD⟩)) →
      CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map π)
        (ggFix (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B)) ∧
      (∀ a : A, ∀ y ∈ (J.subgroupOf L).map π,
        MulAut.conj (ρ a) y ∈ (J.subgroupOf L).map π) := by
  classical
  let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
    (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
  let θL : ↥L ⧸ Subgroup.center ↥L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
    (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
      (Subgroup.map_center_eq eL.symm)).trans θ
  let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
    θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
  let π : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  change ∀ (ρ : A →* P),
    (∀ (a : A) (l : ↥L), π (α a l) = ρ a * π l * (ρ a)⁻¹) →
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      MulAut.conj (ρ ⟨d, hDA hdD⟩)) →
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map π)
      (ggFix (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B)) ∧
    (∀ a : A, ∀ y ∈ (J.subgroupOf L).map π,
      MulAut.conj (ρ a) y ∈ (J.subgroupOf L).map π)
  intro ρ hρcov hBconj
  have hcfg := h
  unfold RCKRPConfig at hcfg
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hJcompL, _, _, _, _, _, _, _, _, _⟩ := hcfg
  have hxC : x ∈ Subgroup.centralizer (L : Set X) := by
    have hxinf : x ∈ A ⊓ Subgroup.centralizer (L : Set X) := by
      rw [hWeq]; exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp hxinf).2
  have hcenD : Subgroup.centralizer (D : Set X) =
      Subgroup.centralizer ({x, d} : Set X) := by
    have hDgen : D = Subgroup.closure ({x, d} : Set X) := by
      rw [hsup, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_union]
      congr 1
    rw [hDgen, Subgroup.centralizer_closure]
  have hfixD : L ⊓ Subgroup.centralizer (D : Set X) =
      L ⊓ Subgroup.centralizer ({d} : Set X) := by
    rw [hcenD]
    ext l
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hl, -, hd⟩
      exact ⟨hl, hd⟩
    · rintro ⟨hl, hd⟩
      exact ⟨hl, (hxC l hl).symm, hd⟩
  have hJL : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer ({d} : Set X)) := hfixD ▸ hJcompL
  have hg : d ∈ Subgroup.normalizer (L : Set X) := hAL (hDA hdD)
  have hJfixSub : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
      (CFSG.StandardType.ggFixSub (L.normalizerMonoidHom ⟨d, hg⟩)) :=
    CFSG.StandardType.ggIsComponentOf_ggFixSub_normalizerMonoidHom hg hJL
  have hαeq : L.normalizerMonoidHom ⟨d, hg⟩ = α ⟨d, hDA hdD⟩ := rfl
  have hgg : CFSG.StandardType.ggFixSub (α ⟨d, hDA hdD⟩) =
      ggFix (α ⟨d, hDA hdD⟩) := by
    apply Subgroup.ext
    intro y
    rfl
  have hJfix : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
      (ggFix (α ⟨d, hDA hdD⟩)) := by
    have hsub : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
        (CFSG.StandardType.ggFixSub (α ⟨d, hDA hdD⟩)) := by
      rw [← hαeq]
      exact hJfixSub
    rw [hgg] at hsub
    exact hsub
  have hψ : Function.Surjective π := by
    change Function.Surjective (η.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥L)))
    exact η.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have h1 : ((l : ↥L) : ↥L ⧸ Subgroup.center ↥L) = 1 := by
      apply η.injective
      simpa [π] using hl
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center ↥L) l).mp h1
  have hab : ∀ l : ↥L,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B (π l) =
      π (α ⟨d, hDA hdD⟩ l) := by
    intro l
    rw [hBconj, MulAut.conj_apply]
    exact (hρcov ⟨d, hDA hdD⟩ l).symm
  have hcomp := CFSG.StandardType.E6ThreeModel.isComponentOf_map_ggFix_of_central
    (L' := ↥L) (R := P) (ψ := π) hψ hker (a := α ⟨d, hDA hdD⟩)
    (b := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B) hab hJfix
  refine ⟨hcomp, ?_⟩
  intro a y hy
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
  have hja : (j : X) ∈ J := Subgroup.mem_subgroupOf.mp hj
  have hconjL : (a : X) * (j : X) * (a : X)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hAL a.2) (j : X)).mp j.2
  have hconjJ : (a : X) * (j : X) * (a : X)⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.mp (hAJ a.2) (j : X)).mp hja
  let j' : ↥L := ⟨(a : X) * (j : X) * (a : X)⁻¹, hconjL⟩
  have hj' : j' ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.mpr hconjJ
  refine Subgroup.mem_map.mpr ⟨j', hj', ?_⟩
  have hαj : α a j = j' := Subtype.ext rfl
  rw [MulAut.conj_apply, ← hρcov a j]
  exact congrArg π hαj.symm

theorem comp_conj_baseChangeGL_eq
    {F Fbar Ω H : Type} [Field F] [Field Fbar] [Field Ω] [Algebra F Ω] [Group H]
    (ε : F →+* Fbar) (sub : Fbar →+* Ω)
    (hsub : sub.comp ε = algebraMap F Ω)
    (ι₀ : H →* ModGL Tag.E6 F)
    (cbar : ModGL Tag.E6 Fbar) (n : ModGL Tag.E6 Ω) :
    (MulAut.conj n⁻¹).toMonoidHom.comp
      ((baseChangeGL (τ := Tag.E6) sub).comp
        ((MulAut.conj cbar).toMonoidHom.comp
          ((baseChangeGL (τ := Tag.E6) ε).comp ι₀))) =
    (MulAut.conj (n⁻¹ * baseChangeGL (τ := Tag.E6) sub cbar)).toMonoidHom.comp
      ((baseChangeGL (τ := Tag.E6) (algebraMap F Ω)).comp ι₀) := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply]
  change (MulAut.conj n⁻¹) (baseChangeGL sub
      ((MulAut.conj cbar) (baseChangeGL ε (ι₀ x)))) =
    (MulAut.conj (n⁻¹ * baseChangeGL sub cbar)) (baseChangeGL (algebraMap F Ω) (ι₀ x))
  have h1 : baseChangeGL sub ((MulAut.conj cbar) (baseChangeGL ε (ι₀ x))) =
      (MulAut.conj (baseChangeGL sub cbar)) (baseChangeGL sub (baseChangeGL ε (ι₀ x))) := by
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have h2 : baseChangeGL sub (baseChangeGL ε (ι₀ x)) =
      baseChangeGL (algebraMap F Ω) (ι₀ x) := by
    rw [baseChangeGL_baseChangeGL, hsub]
  rw [h1, h2]
  simp only [MulAut.conj_apply]
  group

theorem not_e6AdToral_frame_map
    {F Fbar Ω H : Type} [Field F] [Field Fbar] [Field Ω] [Algebra F Ω]
    [IsAlgClosed Ω] [CharP Ω 2] [Group H]
    {σbar : Fbar ≃+* Fbar}
    (ε : F ≃+* Fbar) (sub : Fbar →+* Ω)
    (hsub : sub.comp ε.toRingHom = algebraMap F Ω) (hsub_inj : Function.Injective sub)
    (ι₀ : H →* ModGL Tag.E6 F) (A : Subgroup H)
    (cbar : twistedE6InndiagGL Fbar σbar)
    (nθ : ModGL Tag.E6 Ω) (hnθ : nθ ∈ (thetaSL2 Ω).range)
    (hnt : ¬ CFSG.StandardType.SCFourCover.E6AdToral
      (A.map ((baseChangeGL (τ := Tag.E6) (algebraMap F Ω)).comp ι₀))) :
    ¬ CFSG.StandardType.SCFourCover.E6AdToral
      (A.map ((MulAut.conj nθ⁻¹).toMonoidHom.comp
        ((baseChangeGL (τ := Tag.E6) sub).comp
          (((MulAut.conj : ModGL Tag.E6 Fbar →* MulAut (ModGL Tag.E6 Fbar)) cbar.val).toMonoidHom.comp
            ((baseChangeGL (τ := Tag.E6) ε.toRingHom).comp ι₀))))) := by
  let g : ModGL Tag.E6 Ω := nθ⁻¹ * baseChangeGL (τ := Tag.E6) sub cbar.val
  have hcomp := comp_conj_baseChangeGL_eq (H := H) ε.toRingHom sub hsub ι₀
    (cbar.val : ModGL Tag.E6 Fbar) nθ
  have hmap : A.map ((MulAut.conj nθ⁻¹).toMonoidHom.comp
        ((baseChangeGL (τ := Tag.E6) sub).comp
          (((MulAut.conj : ModGL Tag.E6 Fbar →* MulAut (ModGL Tag.E6 Fbar)) cbar.val).toMonoidHom.comp
            ((baseChangeGL (τ := Tag.E6) ε.toRingHom).comp ι₀)))) =
      (A.map ((baseChangeGL (τ := Tag.E6) (algebraMap F Ω)).comp ι₀)).map
        (MulAut.conj g).toMonoidHom := by
    rw [hcomp, Subgroup.map_map]
  have hn_adj : nθ ∈ adjointGroup Tag.E6 Ω := by
    obtain ⟨P, rfl⟩ := hnθ
    change rootSL2 Tag.E6 Ω e6HighestRoot P ∈ adjointGroup Tag.E6 Ω
    rw [CFSG.SeitzReduction.e6HighestRoot_eq_highRoot]
    exact CFSG.SeitzReduction.E6Pilot.rootSL2_highRoot_mem_adjointGroup (τ := .E6) P
  have hroot : ∀ c : Fbarˣ, ∃ u : Ωˣ, u ^ 3 = Units.map sub.toMonoidHom c := by
    intro c
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (sub (c : Fbar)) (by norm_num : 0 < 3)
    have hv0 : v ≠ 0 := by
      intro h0
      have h0' : sub (c : Fbar) = sub 0 := by simpa [h0] using hv.symm
      exact (hsub_inj.ne (Units.ne_zero c)) h0'
    refine ⟨Units.mk0 v hv0, ?_⟩
    ext
    simpa [Units.val_pow_eq_pow_val, Units.mk0_val] using hv
  have hb_adj : baseChangeGL (τ := Tag.E6) sub (cbar.val : ModGL Tag.E6 Fbar) ∈
      adjointGroup Tag.E6 Ω :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.map_twistedE6InndiagGL_le σbar sub hroot
      (Subgroup.mem_map_of_mem _ cbar.2)
  have hg : g ∈ adjointGroup Tag.E6 Ω := mul_mem (inv_mem hn_adj) hb_adj
  intro htor
  exact hnt ((CFSG.StandardType.SCFourCover.e6AdToral_map_conj hg
    (A.map ((baseChangeGL (τ := Tag.E6) (algebraMap F Ω)).comp ι₀))).mp (hmap ▸ htor))

private theorem rckExcCaseV_exists_frame_matrices
    {X : Type} [Group X] {G₀ A : Subgroup X}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ')
    (ι : ↥G₀ →* ModGL Tag.E6 Ω)
    (hAel : CFSG.Open.IsElemAbelian 3 (A.subgroupOf G₀))
    (hXM : (A.subgroupOf G₀).map ι ≤ torusGroup Tag.E6 Ω ⊔ ψ.range)
    (hNT : ¬ CFSG.StandardType.SCFourCover.E6AdToral ((A.subgroupOf G₀).map ι)) :
    ∃ (M : ModGL Tag.E6 Ω → GL (Fin 6) Ω)
      (a₁ a₂ : ↥(A.subgroupOf G₀)),
      (∀ x ∈ (A.subgroupOf G₀).map ι,
        ∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω,
          x * ψ Y * x⁻¹ = ψ (CFSG.RankThree.Classical2.conjSLn (M x) Y)) ∧
      M (ι a₁) * M (ι a₂) ≠ M (ι a₂) * M (ι a₁) := by
  classical
  have h3 : ((3 : ℕ) : Ω) ≠ 0 := by
    have h2 : ((2 : ℕ) : Ω) = 0 := CharP.cast_eq_zero Ω 2
    have h31 : ((3 : ℕ) : Ω) = 1 := by
      have h3eq : (3 : ℕ) = 2 + 1 := rfl
      rw [h3eq, Nat.cast_add, Nat.cast_one, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  have hact : ∀ g : ModGL Tag.E6 Ω, ∃ M : GL (Fin 6) Ω,
      g ∈ torusGroup Tag.E6 Ω ⊔ ψ.range →
        ∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω,
          g * ψ Y * g⁻¹ = ψ (CFSG.RankThree.Classical2.conjSLn M Y) := by
    intro g
    by_cases hg : g ∈ torusGroup Tag.E6 Ω ⊔ ψ.range
    · obtain ⟨M, hM⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.mem_actsOn.1
          (sup_le
            (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.torusGroup_le_actsOn
              (ν := 6) (σ := σ') hψ (by norm_num))
            (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.range_le_actsOn ψ) hg)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨1, fun hg' => absurd hg' hg⟩
  choose M hM using hact
  have hX : CFSG.Open.IsElemAbelian 3 ((A.subgroupOf G₀).map ι) := hAel.map ι
  obtain ⟨x, hxX, y, hyX, hxy⟩ :=
    CFSG.StandardType.SCFourCover.exists_noncommuting_frame_matrices_of_not_toral
      h3 hψ hX hXM M (fun x hx => hM x (hXM hx)) hNT
  obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.mp hxX
  obtain ⟨a₂, ha₂, rfl⟩ := Subgroup.mem_map.mp hyX
  exact ⟨M, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, fun x hx => hM x (hXM hx), hxy⟩

private theorem rckExcCaseV_exists_original_pair
    {X : Type} [Group X] [Finite X]
    {G₀ A J L : Subgroup X} {f : ℕ}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (Fbar : Subfield Ω) [Finite Fbar]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f Fbar)
    (hFmem : ∀ c : Ω, c ∈ Fbar ↔ c ^ ((2 ^ f) ^ 2) = c)
    (h3dvd : 3 ∣ 2 ^ f + 1)
    (hAel : CFSG.Open.IsElemAbelian 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hAJ : A ≤ Subgroup.normalizer (J : Set X))
    {ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ')
    {S : Matrix.SpecialLinearGroup (Fin 6) Ω}
    (hS : ∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω,
      ψ S * ψ Y * (ψ S)⁻¹ =
        ψ (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL S) Y))
    {ι : ↥G₀ →* ModGL Tag.E6 Ω} (hι : Function.Injective ι)
    (hXM : (A.subgroupOf G₀).map ι ≤ torusGroup Tag.E6 Ω ⊔ ψ.range)
    (hNT : ¬ CFSG.StandardType.SCFourCover.E6AdToral ((A.subgroupOf G₀).map ι))
    (hFix : ∀ g : ModGL Tag.E6 Ω, g ∈ (L.subgroupOf G₀).map ι ↔
      ∃ Y ∈ CFSG.RankThree.Classical2.fixSubgroup
        (stdUnitaryEquiv (ν := 6) (iterateFrobeniusEquiv Ω 2 f)),
        g = ψ S * ψ Y * (ψ S)⁻¹)
    (eL : (L.subgroupOf G₀) ≃* ↥L) (heL : ∀ l₀, (eL l₀ : X) = (l₀ : X))
    {Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥(L.subgroupOf G₀)}
    {θ : ↥(L.subgroupOf G₀) ⧸ Subgroup.center ↥(L.subgroupOf G₀) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))}
    (hΦ : ∀ s, ι (Φ s : ↥G₀) =
      ψ S * ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f) s) * (ψ S)⁻¹)
    (hθ : ∀ s, θ (QuotientGroup.mk (Φ s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) s)
    (α : A →* MulAut ↥L)
    (hα : α = L.normalizerMonoidHom.comp (Subgroup.inclusion hAL))
    (π : ↥L →* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
    (hπ : π = (((QuotientGroup.congr (Subgroup.center ↥L)
        (Subgroup.center ↥(L.subgroupOf G₀)) eL.symm
        (Subgroup.map_center_eq eL.symm)).trans θ).trans
      (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center ↥L)))
    (ρ : A →* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
    (hρcov : ∀ (a : A) (l : ↥L), π (α a l) = ρ a * π l * (ρ a)⁻¹)
    (B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
    (hB3 : (B : GL (Fin 6) Fbar) ^ 3 = 1)
    (hBns : ¬ ∃ c : Fbarˣ,
      (B : GL (Fin 6) Fbar) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (dA : A)
    (hBconj : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B = MulAut.conj (ρ dA))
    (hN : ∀ a : A, ∀ y ∈ (J.subgroupOf L).map π,
      MulAut.conj (ρ a) y ∈ (J.subgroupOf L).map π) :
    ∃ (a₁ a₂ : A)
      (g₁ g₂ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
      (κ : Fbarˣ),
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ = MulAut.conj (ρ a₁) ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ = MulAut.conj (ρ a₂) ∧
      (g₁ : GL (Fin 6) Fbar) * (g₂ : GL (Fin 6) Fbar) ≠
        (g₂ : GL (Fin 6) Fbar) * (g₁ : GL (Fin 6) Fbar) ∧
      κ ^ 3 = 1 ∧ κ ≠ 1 ∧
      (g₁ : GL (Fin 6) Fbar) * (g₂ : GL (Fin 6) Fbar) * (g₁ : GL (Fin 6) Fbar)⁻¹ *
        (g₂ : GL (Fin 6) Fbar)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ ∧
      (∀ y ∈ (J.subgroupOf L).map π,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ y ∈
            (J.subgroupOf L).map π) ∧
      (∀ y ∈ (J.subgroupOf L).map π,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ y ∈
            (J.subgroupOf L).map π) ∧
      Odd f := by
  classical
  let P := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
    (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6)
  let α₀ : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  let θL : ↥L ⧸ Subgroup.center ↥L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
    (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.subgroupOf G₀)) eL.symm
      (Subgroup.map_center_eq eL.symm)).trans θ
  let η : ↥L ⧸ Subgroup.center ↥L ≃* P :=
    θL.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))
  let π₀ : ↥L →* P := η.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ₀surj : Function.Surjective π₀ :=
    (MulEquiv.surjective η).comp (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hα₀ : α = α₀ := hα
  have hπ₀ : π = π₀ := hπ
  rw [hα₀] at hρcov
  rw [hπ₀] at hρcov hN ⊢
  have hAe : CFSG.Open.IsElemAbelian 3 (A.subgroupOf G₀) := hAel.subgroupOf G₀
  obtain ⟨M, a₁₀, a₂₀, hM, hncM⟩ :=
    rckExcCaseV_exists_frame_matrices (ψ := ψ) (σ' := σ') hψ ι hAe hXM hNT
  let b₁ : ↥G₀ := a₁₀.1
  let b₂ : ↥G₀ := a₂₀.1
  let a₁ : A := ⟨(b₁ : X), Subgroup.mem_subgroupOf.mp a₁₀.2⟩
  let a₂ : A := ⟨(b₂ : X), Subgroup.mem_subgroupOf.mp a₂₀.2⟩
  let x₁ : ModGL Tag.E6 Ω := ι b₁
  let x₂ : ModGL Tag.E6 Ω := ι b₂
  have hx₁X : x₁ ∈ (A.subgroupOf G₀).map ι :=
    Subgroup.mem_map.mpr ⟨b₁, a₁₀.2, rfl⟩
  have hx₂X : x₂ ∈ (A.subgroupOf G₀).map ι :=
    Subgroup.mem_map.mpr ⟨b₂, a₂₀.2, rfl⟩
  have hJ_of : ∀ a₀ : ↥G₀, (a₀ : X) ∈ A →
      (L.subgroupOf G₀).map (MulAut.conj a₀).toMonoidHom = L.subgroupOf G₀ := by
    intro a₀ ha
    have hnorm : (a₀ : X) ∈ Subgroup.normalizer (L : Set X) := hAL ha
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzL : (z : X) ∈ L := Subgroup.mem_subgroupOf.mp hz
      have hres : (a₀ : X) * (z : X) * (a₀ : X)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hnorm (z : X)).mp hzL
      rw [← hzy]
      exact Subgroup.mem_subgroupOf.mpr (by simpa [MulAut.conj_apply] using hres)
    · intro hy
      have hyL : (y : X) ∈ L := Subgroup.mem_subgroupOf.mp hy
      have hpre : a₀⁻¹ * y * a₀ ∈ L.subgroupOf G₀ := by
        refine Subgroup.mem_subgroupOf.mpr ?_
        change (a₀ : X)⁻¹ * (y : X) * (a₀ : X) ∈ L
        have hres : (a₀ : X) * ((a₀ : X)⁻¹ * (y : X) * (a₀ : X)) *
            (a₀ : X)⁻¹ ∈ L := by
          simpa [mul_assoc] using hyL
        exact (Subgroup.mem_normalizer_iff.mp hnorm _).mpr hres
      refine Subgroup.mem_map.mpr ⟨a₀⁻¹ * y * a₀, hpre, ?_⟩
      apply Subtype.ext
      change (a₀ : X) * ((a₀ : X)⁻¹ * (y : X) * (a₀ : X)) * (a₀ : X)⁻¹ = (y : X)
      group
  have hJ₁ : (L.subgroupOf G₀).map
      (MulAut.conj b₁ : MulAut ↥G₀).toMonoidHom = L.subgroupOf G₀ :=
    hJ_of b₁ (Subgroup.mem_subgroupOf.mp a₁₀.2)
  have hJ₂ : (L.subgroupOf G₀).map
      (MulAut.conj b₂ : MulAut ↥G₀).toMonoidHom = L.subgroupOf G₀ :=
    hJ_of b₂ (Subgroup.mem_subgroupOf.mp a₂₀.2)
  have hx₁ : ∀ l ∈ L.subgroupOf G₀,
      ι ((MulAut.conj b₁ : MulAut ↥G₀) l) = x₁ * ι l * x₁⁻¹ := by
    intro l hl
    simp only [x₁, MulAut.conj_apply, map_mul, map_inv]
  have hx₂ : ∀ l ∈ L.subgroupOf G₀,
      ι ((MulAut.conj b₂ : MulAut ↥G₀) l) = x₂ * ι l * x₂⁻¹ := by
    intro l hl
    simp only [x₂, MulAut.conj_apply, map_mul, map_inv]
  have hσQ : ∀ c : Ω, iterateFrobeniusEquiv Ω 2 f c = c ^ 2 ^ f :=
    fun c => iterateFrobeniusEquiv_def (R := Ω) (p := 2) (n := f) c
  have hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) Ω) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center
      (ν := 6) (σ := σ') (by norm_num) hψ
  obtain ⟨A₁, hA₁, A₂, hA₂, u₁, u₂, hu₁, hu₂,
    ⟨φ₁, hφ₁mem, hφ₁ind⟩, ⟨φ₂, hφ₂mem, hφ₂ind⟩, hAnc⟩ :=
    CFSG.StandardType.SCFourCover.exists_noncommuting_gu_lifts_of_frame_matrices
      (Ω := Ω) hU.one_le h3dvd (σQ := iterateFrobeniusEquiv Ω 2 f) hσQ
      (G := ModGL Tag.E6 Ω) (ψ := ψ) hker (z := ψ S)
      (W := Matrix.SpecialLinearGroup.toGL S) hS (L' := ↥G₀)
      (J := L.subgroupOf G₀) (ι := ι) hι hFix (F := Fbar) hFmem
      (Φ := Φ) (θ := θ) hΦ hθ
      (a₁ := (MulAut.conj b₁ : MulAut ↥G₀))
      (a₂ := (MulAut.conj b₂ : MulAut ↥G₀)) hJ₁ hJ₂
      (x₁ := x₁) (x₂ := x₂) (B₁ := M x₁) (B₂ := M x₂)
      (fun Y => hM x₁ hx₁X Y) (fun Y => hM x₂ hx₂X Y) hx₁ hx₂ hncM
  obtain ⟨v₁, hv₁⟩ :=
    CFSG.StandardType.TableBU63.exists_unitary_of_gu (n := f) (d := 6) hU hA₁
  obtain ⟨v₂, hv₂⟩ :=
    CFSG.StandardType.TableBU63.exists_unitary_of_gu (n := f) (d := 6) hU hA₂
  let g₁ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ * A₁, hv₁⟩
  let g₂ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) :=
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ * A₂, hv₂⟩
  have hg₁ : (g₁ : GL (Fin 6) Fbar) = Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ * A₁ :=
    rfl
  have hg₂ : (g₂ : GL (Fin 6) Fbar) = Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ * A₂ :=
    rfl
  have hg12 : (g₁ : GL (Fin 6) Fbar) * (g₂ : GL (Fin 6) Fbar) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (v₁ * v₂) * (A₁ * A₂) := by
    rw [hg₁, hg₂, map_mul]
    calc
      (Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ * A₁) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ * A₂) =
          Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ *
            (A₁ * (Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ * A₂)) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ * (A₁ * A₂)) := by
        rw [← mul_assoc (A₁), ← Matrix.GeneralLinearGroup.scalar_commute, mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ *
            Matrix.GeneralLinearGroup.scalar (Fin 6) v₂) * (A₁ * A₂) := by group
  have hg21 : (g₂ : GL (Fin 6) Fbar) * (g₁ : GL (Fin 6) Fbar) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (v₂ * v₁) * (A₂ * A₁) := by
    rw [hg₁, hg₂, map_mul]
    calc
      (Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ * A₂) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ * A₁) =
          Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ *
            (A₂ * (Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ * A₁)) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) v₁ * (A₂ * A₁)) := by
        rw [← mul_assoc (A₂), ← Matrix.GeneralLinearGroup.scalar_commute, mul_assoc]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 6) v₂ *
            Matrix.GeneralLinearGroup.scalar (Fin 6) v₁) * (A₂ * A₁) := by group
  have hgnc : (g₁ : GL (Fin 6) Fbar) * (g₂ : GL (Fin 6) Fbar) ≠
      (g₂ : GL (Fin 6) Fbar) * (g₁ : GL (Fin 6) Fbar) := by
    intro h
    apply hAnc
    rw [hg12, hg21] at h
    rw [mul_comm v₂ v₁] at h
    exact mul_left_cancel h
  have hθL_mk : ∀ l : ↥L,
      θL (QuotientGroup.mk l) = θ (QuotientGroup.mk (eL.symm l)) := by
    intro l
    dsimp only [θL]
    rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
  have heL_symm : ∀ l : ↥L, (eL.symm l : X) = (l : X) := by
    intro l
    have h := heL (eL.symm l)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hαval : ∀ (a : A) (l : ↥L),
      (α₀ a l : X) = (a : X) * (l : X) * (a : X)⁻¹ := by
    intro a l
    exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(a : X), hAL a.2⟩ l
  have hφact₁ : ∀ l : ↥L,
      φ₁ (θL (QuotientGroup.mk l)) = θL (QuotientGroup.mk (α₀ a₁ l)) := by
    intro l
    let l₀ : ↥(L.subgroupOf G₀) := eL.symm l
    let l₀' : ↥(L.subgroupOf G₀) := eL.symm (α₀ a₁ l)
    have hrel : (l₀' : ↥G₀) =
        (MulAut.conj b₁ : MulAut ↥G₀) (l₀ : ↥G₀) := by
      apply Subtype.ext
      change (eL.symm (α₀ a₁ l) : X) =
        (b₁ : X) * (eL.symm l : X) * (b₁ : X)⁻¹
      rw [heL_symm, heL_symm, hαval]
    have h := hφ₁ind l₀ l₀' hrel
    simpa only [hθL_mk, l₀, l₀'] using h
  have hφact₂ : ∀ l : ↥L,
      φ₂ (θL (QuotientGroup.mk l)) = θL (QuotientGroup.mk (α₀ a₂ l)) := by
    intro l
    let l₀ : ↥(L.subgroupOf G₀) := eL.symm l
    let l₀' : ↥(L.subgroupOf G₀) := eL.symm (α₀ a₂ l)
    have hrel : (l₀' : ↥G₀) =
        (MulAut.conj b₂ : MulAut ↥G₀) (l₀ : ↥G₀) := by
      apply Subtype.ext
      change (eL.symm (α₀ a₂ l) : X) =
        (b₂ : X) * (eL.symm l : X) * (b₂ : X)⁻¹
      rw [heL_symm, heL_symm, hαval]
    have h := hφ₂ind l₀ l₀' hrel
    simpa only [hθL_mk, l₀, l₀'] using h
  have hcongr₁ : MulAut.congr (CFSG.StandardType.InndiagSU.projEquiv hU
        (by norm_num : 1 ≤ 6)) φ₁ =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ :=
    CFSG.StandardType.InndiagSU.congr_eq_primeFormConjHom_of_scalar_mul hU
      (by norm_num : 1 ≤ 6) A₁ v₁ g₁ rfl φ₁ hφ₁mem
  have hcongr₂ : MulAut.congr (CFSG.StandardType.InndiagSU.projEquiv hU
        (by norm_num : 1 ≤ 6)) φ₂ =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ :=
    CFSG.StandardType.InndiagSU.congr_eq_primeFormConjHom_of_scalar_mul hU
      (by norm_num : 1 ≤ 6) A₂ v₂ g₂ rfl φ₂ hφ₂mem
  have hact₁ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ = MulAut.conj (ρ a₁) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := hπ₀surj y
    change CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁
        (η (QuotientGroup.mk l)) = (MulAut.conj (ρ a₁)) (η (QuotientGroup.mk l))
    have hη : η (QuotientGroup.mk l) =
        (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
          (θL (QuotientGroup.mk l)) := rfl
    rw [hη]
    have hcg : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁
          ((CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
            (θL (QuotientGroup.mk l))) =
        (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
          (φ₁ (θL (QuotientGroup.mk l))) := by
      have h := congrArg (fun e : MulAut P =>
        e ((CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
          (θL (QuotientGroup.mk l)))) hcongr₁
      simpa [MulAut.congr_apply] using h.symm
    rw [hcg, hφact₁ l]
    change π₀ (α₀ a₁ l) = (MulAut.conj (ρ a₁)) (π₀ l)
    rw [hρcov a₁ l]
    rfl
  have hact₂ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ = MulAut.conj (ρ a₂) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨l, rfl⟩ := hπ₀surj y
    change CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂
        (η (QuotientGroup.mk l)) = (MulAut.conj (ρ a₂)) (η (QuotientGroup.mk l))
    have hη : η (QuotientGroup.mk l) =
        (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
          (θL (QuotientGroup.mk l)) := rfl
    rw [hη]
    have hcg : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂
          ((CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
            (θL (QuotientGroup.mk l))) =
        (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
          (φ₂ (θL (QuotientGroup.mk l))) := by
      have h := congrArg (fun e : MulAut P =>
        e ((CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))
          (θL (QuotientGroup.mk l)))) hcongr₂
      simpa [MulAut.congr_apply] using h.symm
    rw [hcg, hφact₂ l]
    change π₀ (α₀ a₂ l) = (MulAut.conj (ρ a₂)) (π₀ l)
    rw [hρcov a₂ l]
    rfl
  have hcomm12 : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ := by
    rw [hact₁, hact₂]
    calc
      MulAut.conj (ρ a₁) * MulAut.conj (ρ a₂) = MulAut.conj (ρ a₁ * ρ a₂) :=
        (map_mul MulAut.conj _ _).symm
      _ = MulAut.conj (ρ a₂ * ρ a₁) :=
        congrArg MulAut.conj (by
          simpa using congrArg ρ (hAel.1.is_comm.comm a₁ a₂))
      _ = MulAut.conj (ρ a₂) * MulAut.conj (ρ a₁) := map_mul MulAut.conj _ _
  have h1B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ := by
    rw [hact₁, hBconj]
    calc
      MulAut.conj (ρ a₁) * MulAut.conj (ρ dA) = MulAut.conj (ρ a₁ * ρ dA) :=
        (map_mul MulAut.conj _ _).symm
      _ = MulAut.conj (ρ dA * ρ a₁) :=
        congrArg MulAut.conj (by
          simpa using congrArg ρ (hAel.1.is_comm.comm a₁ dA))
      _ = MulAut.conj (ρ dA) * MulAut.conj (ρ a₁) := map_mul MulAut.conj _ _
  have h2B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ := by
    rw [hact₂, hBconj]
    calc
      MulAut.conj (ρ a₂) * MulAut.conj (ρ dA) = MulAut.conj (ρ a₂ * ρ dA) :=
        (map_mul MulAut.conj _ _).symm
      _ = MulAut.conj (ρ dA * ρ a₂) :=
        congrArg MulAut.conj (by
          simpa using congrArg ρ (hAel.1.is_comm.comm a₂ dA))
      _ = MulAut.conj (ρ dA) * MulAut.conj (ρ a₂) := map_mul MulAut.conj _ _
  have hN₁ : ∀ y ∈ (J.subgroupOf L).map π₀,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ y ∈
          (J.subgroupOf L).map π₀ := by
    intro y hy
    rw [hact₁]
    exact hN a₁ y hy
  have hN₂ : ∀ y ∈ (J.subgroupOf L).map π₀,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ y ∈
          (J.subgroupOf L).map π₀ := by
    intro y hy
    rw [hact₂]
    exact hN a₂ y hy
  obtain ⟨κ, hκ3, hκ1, hκ12⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.u6r_exists_nontrivial_cubic_scalar_commutator
      (h := hU) g₁ g₂ hcomm12 hgnc
  have hfOdd : Odd f :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.odd_of_three_dvd_two_pow_add_one h3dvd
  exact ⟨a₁, a₂, g₁, g₂, κ, hact₁, hact₂, hgnc, hκ3, hκ1, hκ12, hcomm12, h1B, h2B,
    hN₁, hN₂, hfOdd⟩

open CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem rckExcCaseV_exists_original_pair_with_natural_block
    {X : Type} [Group X] [Finite X]
    {G₀ A J L : Subgroup X} {f : ℕ}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (Fbar : Subfield Ω) [Finite Fbar]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f Fbar)
    (hFmem : ∀ c : Ω, c ∈ Fbar ↔ c ^ ((2 ^ f) ^ 2) = c)
    (h3dvd : 3 ∣ 2 ^ f + 1)
    (hAel : CFSG.Open.IsElemAbelian 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set X))
    (hAJ : A ≤ Subgroup.normalizer (J : Set X))
    {ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω}
    {σ' : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ')
    {S : Matrix.SpecialLinearGroup (Fin 6) Ω}
    (hS : ∀ Y : Matrix.SpecialLinearGroup (Fin 6) Ω,
      ψ S * ψ Y * (ψ S)⁻¹ =
        ψ (CFSG.RankThree.Classical2.conjSLn (Matrix.SpecialLinearGroup.toGL S) Y))
    {ι : ↥G₀ →* ModGL Tag.E6 Ω} (hι : Function.Injective ι)
    (hXM : (A.subgroupOf G₀).map ι ≤ torusGroup Tag.E6 Ω ⊔ ψ.range)
    (hNT : ¬ CFSG.StandardType.SCFourCover.E6AdToral ((A.subgroupOf G₀).map ι))
    (hFix : ∀ g : ModGL Tag.E6 Ω, g ∈ (L.subgroupOf G₀).map ι ↔
      ∃ Y ∈ CFSG.RankThree.Classical2.fixSubgroup
        (stdUnitaryEquiv (ν := 6) (iterateFrobeniusEquiv Ω 2 f)),
        g = ψ S * ψ Y * (ψ S)⁻¹)
    (eL : (L.subgroupOf G₀) ≃* ↥L) (heL : ∀ l₀, (eL l₀ : X) = (l₀ : X))
    {Φ : CFSG.Open.StatedSU 6 (2 ^ f) Fbar →* ↥(L.subgroupOf G₀)}
    {θ : ↥(L.subgroupOf G₀) ⧸ Subgroup.center ↥(L.subgroupOf G₀) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f))}
    (hΦ : ∀ s, ι (Φ s : ↥G₀) =
      ψ S * ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f) s) * (ψ S)⁻¹)
    (hθ : ∀ s, θ (QuotientGroup.mk (Φ s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) s)
    (α : A →* MulAut ↥L)
    (hα : α = L.normalizerMonoidHom.comp (Subgroup.inclusion hAL))
    (π : ↥L →* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
    (hπ : π = (((QuotientGroup.congr (Subgroup.center ↥L)
        (Subgroup.center ↥(L.subgroupOf G₀)) eL.symm
        (Subgroup.map_center_eq eL.symm)).trans θ).trans
      (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center ↥L)))
    (ρ : A →* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
    (hρcov : ∀ (a : A) (l : ↥L), π (α a l) = ρ a * π l * (ρ a)⁻¹)
    (B : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
    (hB3 : (B : GL (Fin 6) Fbar) ^ 3 = 1)
    (hBns : ¬ ∃ c : Fbarˣ,
      (B : GL (Fin 6) Fbar) = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (dA : A)
    (hBconj : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B = MulAut.conj (ρ dA))
    (hN : ∀ a : A, ∀ y ∈ (J.subgroupOf L).map π,
      MulAut.conj (ρ a) y ∈ (J.subgroupOf L).map π)
    (hJPcomp : CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map π)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B))) :
    letI : DecidableEq Fbar := Classical.decEq Fbar
    letI : DecidableEq (Polynomial Fbar) := inferInstance
    let Bop : Module.End Fbar (Fin 6 → Fbar) :=
      ((t6psub_toLin B : LinearMap.GeneralLinearGroup Fbar (Fin 6 → Fbar)) :
        Module.End Fbar (Fin 6 → Fbar))
    let JP := (J.subgroupOf L).map π
    ∃ (a₁ a₂ : A)
      (g₁ g₂ : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6))
      (κ : Fbarˣ),
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ = MulAut.conj (ρ a₁) ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ = MulAut.conj (ρ a₂) ∧
      (g₁ : GL (Fin 6) Fbar) * (g₂ : GL (Fin 6) Fbar) ≠
        (g₂ : GL (Fin 6) Fbar) * (g₁ : GL (Fin 6) Fbar) ∧
      κ ^ 3 = 1 ∧ κ ≠ 1 ∧
      (g₁ : GL (Fin 6) Fbar) * (g₂ : GL (Fin 6) Fbar) * (g₁ : GL (Fin 6) Fbar)⁻¹ *
        (g₂ : GL (Fin 6) Fbar)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ ∧
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) B *
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ ∧
      (∀ y ∈ (J.subgroupOf L).map π,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₁ y ∈
            (J.subgroupOf L).map π) ∧
      (∀ y ∈ (J.subgroupOf L).map π,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom hU
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram Fbar 6) g₂ y ∈
            (J.subgroupOf L).map π) ∧
      Odd f ∧
                                    ∃ (aSpec : t6psub_Idx hU 6 B) (cSpec dSpec : Fbar)
                                      (U : Matrix (Fin 6) (Fin 3) Fbar) (Lm : Matrix (Fin 3) (Fin 6) Fbar)
                                      (εblk : Matrix (Fin 6) (Fin 6) Fbar)
                                      (j : gramSU hU (idGram Fbar 3) →* gramSU hU (idGram Fbar 6))
                                      (T : gramSU hU (idGram Fbar 6)) (V : Matrix (Fin 6) (Fin 3) Fbar),
                                      let pC : Polynomial Fbar := (Polynomial.X : Polynomial Fbar) - Polynomial.C cSpec
                                      let pD : Polynomial Fbar := (Polynomial.X : Polynomial Fbar) - Polynomial.C dSpec
                                      (aSpec.1 : Polynomial Fbar) = pC ∧
                                      cSpec ^ 3 = 1 ∧
                                      primaryMultiplicity
                                        Bop (aSpec.1 : Polynomial Fbar) = 3 ∧
                                      (aSpec.1 : Polynomial Fbar).natDegree = 1 ∧
                                      dualPoly hU.bar (aSpec.1 : Polynomial Fbar) = (aSpec.1 : Polynomial Fbar) ∧
                                      dSpec ^ 3 = 1 ∧ dSpec ≠ cSpec ∧
                                      primaryFactors
                                        Bop = {pC, pD} ∧
                                      Module.finrank Fbar (primaryComponent
                                        Bop (pC)) = 3 ∧
                                      Module.finrank Fbar (primaryComponent
                                        Bop (pD)) = 3 ∧
                                      IsCompl
                                        (primaryComponent
                                          Bop (pC))
                                        (primaryComponent
                                          Bop (pD)) ∧
                                      (∀ v ∈ primaryComponent
                                          Bop (pC),
                                        ∀ w ∈ primaryComponent
                                          Bop (pD),
                                        idForm hU 6 v w = 0) ∧
                                      primaryProjection
                                        Bop (pC) +
                                      primaryProjection
                                        Bop (pD) = 1 ∧
                                      Bop =
                                        cSpec • primaryProjection
                                          Bop (pC) +
                                        dSpec • primaryProjection
                                          Bop (pD) ∧
                                      Function.Injective j ∧
                                      Lm = Matrix.transpose (U.map hU.bar) ∧
                                      Lm * U = 1 ∧
                                      U * Lm = εblk ∧
                                      Matrix.transpose (εblk.map hU.bar) = εblk ∧
                                      LinearMap.range U.mulVecLin = primaryComponent
                                        Bop (pC) ∧
                                      εblk.mulVecLin = primaryProjection
                                        Bop (pC) ∧
                                      (∀ P : gramSU hU (idGram Fbar 3),
                                        (((j P : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar) =
                                          U * ((P : GL (Fin 3) Fbar) : Matrix (Fin 3) (Fin 3) Fbar) * Lm + (1 - εblk)) ∧
                                      j.range = (specialBlock (idForm hU 6) (t6psub_toLin B) (pC)).comap
                                        (t6psuh_toLinSU hU 6) ∧
                                      j.range.map (QuotientGroup.mk' (normOneScalars hU (gramSU hU (idGram Fbar 6)) 6)) = JP ∧
                                      (((B : GL (Fin 6) Fbar) : Matrix (Fin 6) (Fin 6) Fbar) = cSpec • εblk + dSpec • (1 - εblk)) ∧
                                      (∀ i k, (((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar) i
                                          ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inl k)) = U i k) ∧
                                      (∀ i k, (((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar) i
                                          ((finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6) (Sum.inr k)) = V i k) ∧
                                      Matrix.transpose (V.map hU.bar) * V = 1 ∧
                                      Matrix.transpose (U.map hU.bar) * V = 0 ∧
                                      ((((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar)⁻¹ : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar) *
                                        (((B : GL (Fin 6) Fbar) : Matrix (Fin 6) (Fin 6) Fbar)) *
                                        ((((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar)) =
                                        Matrix.diagonal ![cSpec, cSpec, cSpec, dSpec, dSpec, dSpec] ∧
                                      ((((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar)⁻¹ : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar) * εblk *
                                        ((((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                          Matrix (Fin 6) (Fin 6) Fbar)) =
                                        Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
                                          (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
                                          (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) Fbar) (0 : Matrix (Fin 3) (Fin 3) Fbar)
                                            (0 : Matrix (Fin 3) (Fin 3) Fbar) (0 : Matrix (Fin 3) (Fin 3) Fbar)) ∧
                                      (∀ P : gramSU hU (idGram Fbar 3),
                                        ((((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar)⁻¹ : GL (Fin 6) Fbar) :
                                            Matrix (Fin 6) (Fin 6) Fbar) *
                                          (((j P : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                            Matrix (Fin 6) (Fin 6) Fbar) *
                                          ((((T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) Fbar) :
                                            Matrix (Fin 6) (Fin 6) Fbar)) =
                                          Matrix.reindex (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
                                            (finSumFinEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6)
                                            (Matrix.fromBlocks (((P : GL (Fin 3) Fbar) :
                                              Matrix (Fin 3) (Fin 3) Fbar)) (0 : Matrix (Fin 3) (Fin 3) Fbar)
                                              (0 : Matrix (Fin 3) (Fin 3) Fbar) (1 : Matrix (Fin 3) (Fin 3) Fbar))) ∧
                                      3 ≤ 2 ^ f
 := by
  classical
  obtain ⟨a₁, a₂, g₁, g₂, κ, hact₁, hact₂, hgnc, hκ3, hκ1, hκ12, hcomm12,
    h1B, h2B, hN₁, hN₂, hfOdd⟩ :=
    rckExcCaseV_exists_original_pair (Ω := Ω) (Fbar := Fbar) (hU := hU) (hFmem := hFmem)
      (h3dvd := h3dvd) (hAel := hAel) (hAL := hAL) (hAJ := hAJ)
      (ψ := ψ) (hψ := hψ) (S := S) (hS := hS)
      (ι := ι) (hι := hι) (hXM := hXM) (hNT := hNT) (hFix := hFix)
      (eL := eL) (heL := heL) (Φ := Φ) (θ := θ) (hΦ := hΦ) (hθ := hθ)
      (α := α) (hα := hα) (π := π) (hπ := hπ) (ρ := ρ) (hρcov := hρcov)
      (B := B) (hB3 := hB3) (hBns := hBns) (dA := dA) (hBconj := hBconj) (hN := hN)
  refine ⟨a₁, a₂, g₁, g₂, κ, hact₁, hact₂, hgnc, hκ3, hκ1, hκ12, hcomm12, h1B, h2B,
    hN₁, hN₂, hfOdd, ?_⟩
  exact CFSG.HardMathSupport.Dickson.Sec6.I1431.u6r_three_plus_three_of_normalizes_component
    (h := hU) hfOdd B g₁ g₂ hB3 hBns ((J.subgroupOf L).map π)
    (CFSG.Assembly.isComponentOf_iff_open.mp hJPcomp) κ hκ3 hκ1 hκ12 h1B h2B hN₁ hN₂

open CFSG.Open (StatedSU)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne
open CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open scoped MatrixGroups

private theorem rckExcCaseV_Q6_coe
    {Ω : Type} [Field Ω] (Fbar : Subfield Ω) {f : ℕ}
    (hU : UnitaryFieldData 2 f ↥Fbar)
    (g : gramSU hU (idGram Fbar 6)) :
    ((((statedSUToSL Fbar 6 (2 ^ f)).comp
        (CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl).toMonoidHom)
        g : SL(6, Ω)) : Matrix (Fin 6) (Fin 6) Ω) =
      (((g : GL (Fin 6) ↥Fbar)) : Matrix (Fin 6) (Fin 6) ↥Fbar).map Fbar.subtype := by
  exact CFSG.RankThree.Classical2.coe_statedSUToSL Fbar 6 (2 ^ f)
    ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
      (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl).toMonoidHom g)

private theorem rckExcCaseV_diagonal_map_eq
    {Ω : Type} [Field Ω] (Fbar : Subfield Ω) (c d : Fbarˣ) :
    (Matrix.diagonal ![(c : ↥Fbar), (c : ↥Fbar), (c : ↥Fbar),
      (d : ↥Fbar), (d : ↥Fbar), (d : ↥Fbar)]).map Fbar.subtype =
      Matrix.diagonal (fun k => ((![Units.map Fbar.subtype.toMonoidHom c,
        Units.map Fbar.subtype.toMonoidHom c, Units.map Fbar.subtype.toMonoidHom c,
        Units.map Fbar.subtype.toMonoidHom d, Units.map Fbar.subtype.toMonoidHom d,
        Units.map Fbar.subtype.toMonoidHom d] : Fin 6 → Ωˣ) k : Ω)) := by
  rw [Matrix.diagonal_map (map_zero Fbar.subtype)]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem rckExcCaseV_matrix_diagonal_transport
    {Ω : Type} [Field Ω] (Fbar : Subfield Ω) {f : ℕ}
    (hU : UnitaryFieldData 2 f ↥Fbar)
    (Bsu T : gramSU hU (idGram Fbar 6)) (c d : Fbarˣ)
    (hTdiag : (((T : GL (Fin 6) ↥Fbar)⁻¹ : GL (Fin 6) ↥Fbar) :
        Matrix (Fin 6) (Fin 6) ↥Fbar) *
      ((Bsu : GL (Fin 6) ↥Fbar) : Matrix (Fin 6) (Fin 6) ↥Fbar) *
      ((T : GL (Fin 6) ↥Fbar) : Matrix (Fin 6) (Fin 6) ↥Fbar) =
        Matrix.diagonal ![(c : ↥Fbar), (c : ↥Fbar), (c : ↥Fbar),
          (d : ↥Fbar), (d : ↥Fbar), (d : ↥Fbar)]) :
    ((((statedSUToSL Fbar 6 (2 ^ f)).comp
        (CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl).toMonoidHom)
        (T⁻¹ * Bsu * T) : SL(6, Ω)) : Matrix (Fin 6) (Fin 6) Ω) =
      Matrix.diagonal (fun k => ((![Units.map Fbar.subtype.toMonoidHom c,
        Units.map Fbar.subtype.toMonoidHom c, Units.map Fbar.subtype.toMonoidHom c,
        Units.map Fbar.subtype.toMonoidHom d, Units.map Fbar.subtype.toMonoidHom d,
        Units.map Fbar.subtype.toMonoidHom d] : Fin 6 → Ωˣ) k : Ω)) := by
  classical
  have hcoe : (((T⁻¹ * Bsu * T : gramSU hU (idGram Fbar 6)) : GL (Fin 6) ↥Fbar) :
      Matrix (Fin 6) (Fin 6) ↥Fbar) =
      (((T : GL (Fin 6) ↥Fbar)⁻¹ : GL (Fin 6) ↥Fbar) :
        Matrix (Fin 6) (Fin 6) ↥Fbar) *
      ((Bsu : GL (Fin 6) ↥Fbar) : Matrix (Fin 6) (Fin 6) ↥Fbar) *
      ((T : GL (Fin 6) ↥Fbar) : Matrix (Fin 6) (Fin 6) ↥Fbar) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_inv]
  rw [rckExcCaseV_Q6_coe (hU := hU) (g := T⁻¹ * Bsu * T), hcoe, hTdiag]
  exact rckExcCaseV_diagonal_map_eq Fbar c d

private theorem rckExcCaseV_config_root_pair
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) :
    R ≤ J ∧ Rm ≤ J ∧ GGRootPosJ J R Rm ∧ e ∈ D ∧ e ≠ 1 ∧
      CFSG.Assembly.IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) ∧
      J ≤ K ∧ Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  unfold RCKRPConfig at h
  obtain ⟨_, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          _, _, _, _, _,
          hRJ, hRmJ, hPosJ, heD, he1, hKcomp, hJK, hOddK⟩ := h
  exact ⟨hRJ, hRmJ, hPosJ, heD, he1, hKcomp, hJK, hOddK⟩

private theorem rckExcCaseV_isComponentOf_subgroupOf_centralizer
    {X : Type} [Group X] {G₀ K : Subgroup X} {e : X} (he : e ∈ G₀)
    (hK : CFSG.Assembly.IsComponentOf K
      (G₀ ⊓ Subgroup.centralizer ({e} : Set X))) :
    CFSG.Assembly.IsComponentOf (K.subgroupOf G₀)
      (Subgroup.centralizer ({⟨e, he⟩} : Set (↥G₀))) := by
  have hC : (G₀ ⊓ Subgroup.centralizer ({e} : Set X)).subgroupOf G₀ =
      Subgroup.centralizer ({⟨e, he⟩} : Set (↥G₀)) := by
    rw [Subgroup.inf_subgroupOf_left]
    simpa only [one_mul] using
      (CFSG.StandardType.ggCentralizer_singleton_subgroupOf (H := G₀) (c := (1 : X))
        (Subgroup.one_mem _) ⟨e, he⟩)
  have hrestricted := CFSG.StandardType.ggIsComponentOf_subgroupOf hK
    (show G₀ ⊓ Subgroup.centralizer ({e} : Set X) ≤ G₀ from inf_le_left)
  rwa [hC] at hrestricted

private theorem rckExcCaseV_identityFormFrobenius_eq
    {Ω : Type} [Field Ω] [CharP Ω 2] (h2 : (2 : Ω) = 0)
    (σQ : Ω ≃+* Ω) (J6 : SL(6, Ω))
    (hJ6mat : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    (η : Ωˣ) :
    e6IdentityFormFrobenius h2 σQ J6
        (E6GraphLevi.thetaSL2 Ω (nSL η)) =
      e6FrobEnd σQ.toRingHom η := by
  let ψ' : SL(6, Ω) →* ModGL TwistTag.E6.tag Ω := E6GraphLevi.realize h2
  let dθ : ModGL TwistTag.E6.tag Ω := E6GraphLevi.thetaSL2 Ω (nSL η)
  let θN : ModGL TwistTag.E6.tag Ω := e6ThetaN
  let θJ : ModGL TwistTag.E6.tag Ω := e6AntiIdJ
  let FW : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag Ω :=
    e6IdentityFormFrobenius h2 σQ J6 dθ
  let FEnd : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag Ω :=
    e6FrobEnd σQ.toRingHom η
  have hJ6eq' : J6 = e6AntiIdSL := by
    apply Subtype.ext
    simpa only [e6AntiIdSL] using hJ6mat
  have hj6 : ψ' J6 = θJ := by
    change ψ' J6 = e6AntiIdJ
    rw [hJ6eq']
    rfl
  have hHθ : thetaTorusHom Ω η = E6GraphLevi.thetaSL2 Ω (HSL η) :=
    E6GraphLevi.thetaTorusHom_eq_thetaSL2 η
  have hdθeq : dθ = thetaTorusHom Ω η * θN := by
    rw [hHθ]
    change E6GraphLevi.thetaSL2 Ω (nSL η) =
      E6GraphLevi.thetaSL2 Ω (HSL η) * θN
    rw [CFSG.LieType.Chevalley.nSL_eq_HSL_mul, map_mul]
    rfl
  have hFW : FW = FEnd := by
    apply MonoidHom.ext
    intro g
    change (dθ * ψ' J6) * twistHom TwistTag.E6 Ω σQ.toRingHom g * (dθ * ψ' J6)⁻¹ =
      (thetaTorusHom Ω η * θN * θJ) *
        twistHom TwistTag.E6 Ω σQ.toRingHom g *
        (thetaTorusHom Ω η * θN * θJ)⁻¹
    rw [hdθeq, hj6]
  exact hFW

private theorem rckExcCaseV_projEquiv_gramSUOneEquiv
    {F₀ H : Type} [Field F₀] [Group H] {f : ℕ}
    (hU : UnitaryFieldData 2 f F₀)
    (Φ : StatedSU 6 (2 ^ f) F₀ →* H)
    (θ : H ⧸ Subgroup.center H ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) F₀ (2 ^ f)))
    (hθ : ∀ s, θ (QuotientGroup.mk (Φ s)) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F₀ (2 ^ f)) s)
    (Bsu : gramSU hU (idGram F₀ 6)) :
    (θ.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num)))
      (QuotientGroup.mk (Φ
        ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) F₀)) rfl) Bsu))) =
      (Bsu : primeFormP hU (idGram F₀ 6)) := by
  rw [MulEquiv.trans_apply, hθ]
  let bH : LargeEvenSUGroup (Fin 6) F₀ (2 ^ f) :=
    (CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
      (C₀ := (1 : GL (Fin 6) F₀)) rfl) Bsu
  change CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num)
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F₀ (2 ^ f)) bH) =
    (Bsu : primeFormP hU (idGram F₀ 6))
  rw [show LargeEvenProjMk (LargeEvenSUGroup (Fin 6) F₀ (2 ^ f)) bH =
      (bH : LargeEvenProj (LargeEvenSUGroup (Fin 6) F₀ (2 ^ f))) from rfl]
  rw [CFSG.StandardType.InndiagSU.projEquiv_mk]
  have hrep :
      (⟨(bH : GL (Fin 6) F₀),
        CFSG.StandardType.InndiagSU.largeEvenSUGroup_eq_gramSU (d := 6) hU ▸ bH.2⟩ :
        gramSU hU (idGram F₀ 6)) = Bsu := by
    apply Subtype.ext
    rfl
  exact congrArg
    (fun g : gramSU hU (idGram F₀ 6) => (g : primeFormP hU (idGram F₀ 6))) hrep

private theorem rckExcCaseV_original_J_eq_of_natural_block
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {Fbar : Subfield Ω} {f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f ↥Fbar)
    (hFmem : ∀ c : Ω, c ∈ Fbar ↔ c ^ ((2 ^ f) ^ 2) = c)
    {σQ : Ω ≃+* Ω} (hσQ : ∀ a, σQ a = a ^ (2 ^ f))
    {J6 : Matrix.SpecialLinearGroup (Fin 6) Ω}
    (hJ6mat : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθrange : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range)
    {H : Type} [Group H] {J0 L0 : Subgroup H} (hJ0leL0 : J0 ≤ L0)
    (hJ0q : CFSG.Assembly.IsQuasisimple ↥J0)
    {j : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 3) →*
      CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6)}
    (hq3 : 3 ≤ 2 ^ f)
    {Φ : CFSG.Open.StatedSU 6 (2 ^ f) ↥Fbar →* ↥L0}
    {θ : ↥L0 ⧸ Subgroup.center ↥L0 ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) ↥Fbar (2 ^ f))}
    (hθ : ∀ s : CFSG.Open.StatedSU 6 (2 ^ f) ↥Fbar,
      θ (QuotientGroup.mk (Φ s)) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) ↥Fbar (2 ^ f)) s)
    (hJP0 : j.range.map
        (QuotientGroup.mk' (CFSG.ClassicalGroups.UnitaryFlag.normOneScalars hU
          (CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6)) 6)) =
      (J0.subgroupOf L0).map
        ((θ.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))).toMonoidHom.comp
          (QuotientGroup.mk' (Subgroup.center ↥L0))))
    {T : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6)}
    (hTj : ∀ P : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 3),
      (((T : GL (Fin 6) ↥Fbar)⁻¹ : GL (Fin 6) ↥Fbar) :
          Matrix (Fin 6) (Fin 6) ↥Fbar) *
        (((j P : GL (Fin 6) ↥Fbar) : Matrix (Fin 6) (Fin 6) ↥Fbar)) *
        (((T : GL (Fin 6) ↥Fbar) : Matrix (Fin 6) (Fin 6) ↥Fbar)) =
      Matrix.reindex (finSumFinEquiv (m := 3) (n := 3))
        (finSumFinEquiv (m := 3) (n := 3))
        (Matrix.fromBlocks (((P : GL (Fin 3) ↥Fbar) : Matrix (Fin 3) (Fin 3) ↥Fbar))
          (0 : Matrix (Fin 3) (Fin 3) ↥Fbar) (0 : Matrix (Fin 3) (Fin 3) ↥Fbar)
          (1 : Matrix (Fin 3) (Fin 3) ↥Fbar)))
    {ι : H →* ModGL Tag.E6 Ω} {S : Matrix.SpecialLinearGroup (Fin 6) Ω}
    (hΦ : let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω :=
        E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
      ∀ s : CFSG.Open.StatedSU 6 (2 ^ f) ↥Fbar,
        ι (Φ s : H) =
          ψ S * ψ (statedSUToSL Fbar 6 (2 ^ f) s) * (ψ S)⁻¹)
    (ιT : H →* ModGL Tag.E6 Ω)
    (hiT : let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω :=
        E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
      ιT = (MulAut.conj
        (ψ S * ψ (statedSUToSL Fbar 6 (2 ^ f)
          ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
            (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T)))⁻¹).toMonoidHom.comp ι)
    (hTfix : ∀ g ∈ ιT.range,
      e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ g = g) :
    J0.map ιT =
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6LineFactor Ω 0 ⊓ ιT.range := by
  classical
  let jS : CFSG.Open.StatedSU 3 (2 ^ f) ↥Fbar →*
      CFSG.Open.StatedSU 6 (2 ^ f) ↥Fbar :=
    (CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
      (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl).toMonoidHom.comp
      (j.comp (CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
        (C₀ := (1 : GL (Fin 3) ↥Fbar)) rfl).symm.toMonoidHom)
  let Φ3 : CFSG.Open.StatedSU 3 (2 ^ f) ↥Fbar →* H := L0.subtype.comp (Φ.comp jS)
  let projP : LargeEvenProj (LargeEvenSUGroup (Fin 6) ↥Fbar (2 ^ f)) ≃*
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6) :=
    CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6)
  let π0 : ↥L0 →* CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6) :=
    (θ.trans projP).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L0))
  have hπ0 : π0 =
      (θ.trans (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num : 1 ≤ 6))).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center ↥L0)) := rfl
  have hFbarcard : Nat.card ↥Fbar = (2 ^ f) ^ 2 := by
    rw [hU.card, mul_comm 2 f, pow_mul]
  have hJL0perfect : ⁅J0.subgroupOf L0, J0.subgroupOf L0⁆ = J0.subgroupOf L0 :=
    CFSG.SeitzReduction.commutator_subgroupOf_eq_self hJ0leL0
      (Subgroup.isPerfect_iff.mp ⟨hJ0q.1⟩)
  have hΨ3 : (Φ.comp jS).range = J0.subgroupOf L0 :=
    CFSG.StandardType.SCFourCover.naturalSU3_cover_range_eq_of_projective_eq
      (L := ↥L0) (F := ↥Fbar) hU (J := J0.subgroupOf L0) hθ π0 hπ0
      hJL0perfect hq3 (j := j) hJP0
  have hΦ3range : Φ3.range = J0 := by
    change (L0.subtype.comp (Φ.comp jS)).range = J0
    rw [MonoidHom.range_comp, hΨ3]
    exact Subgroup.map_subgroupOf_eq_of_le hJ0leL0
  have hdiagHom := CFSG.StandardType.SCFourCover.naturalSU3_cover_diagram_of_standard_frame
    (F := Fbar) (f := f) hU (H := H) (L := L0) (ι := ι) (S := S) (Φ6 := Φ)
    hΦ (j := j) (T := T) hTj
  have hdiagMap : ιT.comp Φ3 =
      (e6FirstBlockRealize (CharP.cast_eq_zero Ω 2)).comp
        (CFSG.RankThree.Classical2.statedSUToSL Fbar 3 (2 ^ f)) := by
    rw [hiT]
    exact hdiagHom
  have hdiag : ∀ s : CFSG.Open.StatedSU 3 (2 ^ f) ↥Fbar,
      ιT (Φ3 s) = e6FirstBlockRealize (CharP.cast_eq_zero Ω 2)
        (CFSG.RankThree.Classical2.statedSUToSL Fbar 3 (2 ^ f) s) := by
    intro s
    exact DFunLike.congr_fun hdiagMap s
  have hJΓ : J0.map ιT ≤ ιT.range := Subgroup.map_le_range (f := ιT) J0
  exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6OriginalJ_map_eq_inf
    (CharP.cast_eq_zero Ω 2) Nat.prime_two Fbar hFmem hFbarcard σQ hσQ hJ6mat
    hdθrange (J := J0) Φ3 hΦ3range ιT hdiag hJΓ hTfix

private theorem rckExcCaseV_naturalT_frame_fixed
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {Fbar : Subfield Ω} {f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f ↥Fbar)
    (hFmem : ∀ c : Ω, c ∈ Fbar ↔ c ^ ((2 ^ f) ^ 2) = c)
    (hFbarcard : Nat.card ↥Fbar = (2 ^ f) ^ 2)
    (σQ : Ω ≃+* Ω) (hσQ : ∀ a, σQ a = a ^ (2 ^ f))
    {J6 : Matrix.SpecialLinearGroup (Fin 6) Ω}
    (hJ6mat : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθrange : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range)
    {T : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6)}
    (W : Subgroup (ModGL Tag.E6 Ω))
    (hWfix : ∀ g ∈ W, e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ g = g) :
    let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω :=
      E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
    let τ : ModGL Tag.E6 Ω :=
      ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
        ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T))
    let κ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := (MulAut.conj τ⁻¹).toMonoidHom
    ∀ g ∈ W.map κ, e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ g = g := by
  classical
  let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω :=
    E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
  let TΩ : Matrix.SpecialLinearGroup (Fin 6) Ω :=
    CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
      ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
        (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T)
  let τ : ModGL Tag.E6 Ω := ψ TΩ
  let κ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := (MulAut.conj τ⁻¹).toMonoidHom
  change ∀ g ∈ W.map κ,
    e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ g = g
  intro g hg
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
  exact CFSG.StandardType.SCFourCover.e6IdentityFormFrobenius_conj_inv_statedSUToSL_position
    (F := Fbar) (f := f) hU hFmem hFbarcard σQ hσQ hJ6mat hdθrange T (hWfix w hw)

private theorem rckExcCaseV_naturalT_frame_normalizer
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {Fbar : Subfield Ω} {f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f ↥Fbar)
    (hFmem : ∀ c : Ω, c ∈ Fbar ↔ c ^ ((2 ^ f) ^ 2) = c)
    (hFbarcard : Nat.card ↥Fbar = (2 ^ f) ^ 2)
    (σQ : Ω ≃+* Ω) (hσQ : ∀ a, σQ a = a ^ (2 ^ f))
    {J6 : Matrix.SpecialLinearGroup (Fin 6) Ω}
    (hJ6mat : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθrange : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range)
    {T : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram ↥Fbar 6)}
    (W : Subgroup (ModGL Tag.E6 Ω))
    (hWnorm : ∀ y ∈ adjointGroup Tag.E6 Ω,
      e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ y = y →
      y ∈ Subgroup.normalizer (W : Set (ModGL Tag.E6 Ω))) :
    let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω :=
      E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
    let τ : ModGL Tag.E6 Ω :=
      ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
        ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T))
    let κ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := (MulAut.conj τ⁻¹).toMonoidHom
    ∀ y ∈ adjointGroup Tag.E6 Ω,
      e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ y = y →
      y ∈ Subgroup.normalizer (W.map κ : Set (ModGL Tag.E6 Ω)) := by
  classical
  let ψ : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL Tag.E6 Ω :=
    E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
  let TΩ : Matrix.SpecialLinearGroup (Fin 6) Ω :=
    CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
      ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
        (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T)
  let τ : ModGL Tag.E6 Ω := ψ TΩ
  let κ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := (MulAut.conj τ⁻¹).toMonoidHom
  have hτmem : τ ∈ subsystemGroup TwistTag.E6.tag Ω E6GraphLevi.setA := by
    change ψ TΩ ∈ _
    rw [← E6GraphLevi.range_realize (CharP.cast_eq_zero Ω 2)]
    exact ⟨_, rfl⟩
  have hτadj : τ ∈ adjointGroup Tag.E6 Ω :=
    E6GraphLevi.subsystemGroup_le_adjointGroup hτmem
  change ∀ y ∈ adjointGroup Tag.E6 Ω,
    e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ y = y →
    y ∈ Subgroup.normalizer (W.map κ : Set (ModGL Tag.E6 Ω))
  intro y hy hfy
  have hτinv : ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
      ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
        (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T⁻¹)) = τ⁻¹ := by
    change ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
        ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T⁻¹)) =
      (ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
        ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T)))⁻¹
    simp only [map_inv]
  have hposInv :=
    CFSG.StandardType.SCFourCover.e6IdentityFormFrobenius_conj_inv_statedSUToSL_position
      (F := Fbar) (f := f) hU hFmem hFbarcard σQ hσQ hJ6mat hdθrange
      (T := T⁻¹) (g := y) hfy
  have hvfix : e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ
      (τ * y * τ⁻¹) = τ * y * τ⁻¹ := by
    let τInv : ModGL Tag.E6 Ω :=
      ψ (CFSG.RankThree.Classical2.statedSUToSL Fbar 6 (2 ^ f)
        ((CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
          (C₀ := (1 : GL (Fin 6) ↥Fbar)) rfl) T⁻¹))
    have hτInv : τInv = τ⁻¹ := hτinv
    change e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ
      (τInv⁻¹ * y * τInv) = τInv⁻¹ * y * τInv at hposInv
    rw [hτInv, inv_inv] at hposInv
    exact hposInv
  have hvadj : τ * y * τ⁻¹ ∈ adjointGroup Tag.E6 Ω :=
    (adjointGroup Tag.E6 Ω).mul_mem
      ((adjointGroup Tag.E6 Ω).mul_mem hτadj hy)
      ((adjointGroup Tag.E6 Ω).inv_mem hτadj)
  have hvnorm : τ * y * τ⁻¹ ∈ Subgroup.normalizer (W : Set (ModGL Tag.E6 Ω)) :=
    hWnorm (τ * y * τ⁻¹) hvadj hvfix
  have hmem : y ∈ (Subgroup.normalizer (W : Set (ModGL Tag.E6 Ω))).map κ := by
    refine ⟨τ * y * τ⁻¹, hvnorm, ?_⟩
    change τ⁻¹ * (τ * y * τ⁻¹) * (τ⁻¹)⁻¹ = y
    group
  rw [Subgroup.map_normalizer_eq_of_bijective W (f := κ)
    (MulAut.conj τ⁻¹).bijective] at hmem
  exact hmem

theorem rckExcCaseV_original_strong_pair
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e)
    (hKne : K ≠ J) (hV : RCKExcCaseVData t f p G₀ A B₁) :
    1 ≤ f ∧
      ∃ (phiL phiK : (ggU .PSU 6 f).K →* X)
        (β : Fin (ggU .PSU 6 f).D.rank → ℤ) (r : (ggU .PSU 6 f).K),
        phiL.range = L ∧ phiK.range = K ∧ phiK.ker = phiL.ker ∧
        phiL.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧
        β ∈ (ggU .PSU 6 f).D.roots ∧ GGLongRoot (ggU .PSU 6 f).D β ∧
        R = ggRootSub (ggU .PSU 6 f).D phiL β r ∧
        Rm = ggRootSub (ggU .PSU 6 f).D phiL (-β) r ∧
        R = ggRootSub (ggU .PSU 6 f).D phiK β r ∧
        Rm = ggRootSub (ggU .PSU 6 f).D phiK (-β) r := by
  classical
  have hcore := rckCompCore_of_rpConfig h
  unfold RCKCompCore at hcore
  obtain ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0,
    hB1J, hB1Jc, hp4, hSC, hrank2, hAc, hB1L, hMarkL, hJcomp, hOddJ, hLG0,
    hx, hDnotc, hJcompL, hJnotA6⟩ := hcore
  obtain ⟨xgen, hxgenD, hxgenne, hxgencomp⟩ := hx
  obtain ⟨hRJ, hRmJ, hPosJ, heD, he1, hKcomp, hJK, hOddK⟩ :=
    rckExcCaseV_config_root_pair h
  have hVcfg := hV
  unfold RCKExcCaseVData at hVcfg
  obtain ⟨htag, hp3, h3dvd, h9dvd, hcardA, hB1Aeq, hAG, hZ⟩ := hVcfg
  have hDA : D ≤ A := hB1Aeq ▸ hDB1
  have heG0 : e ∈ G₀ := (hDA.trans hAG) heD
  have hKG0 : K ≤ G₀ := hKcomp.1.trans inf_le_left
  have hJG0 : J ≤ G₀ := hJK.trans hKG0
  have hJL : J ≤ L := hJcompL.1.trans inf_le_left
  let L₀ : Subgroup ↥G₀ := L.subgroupOf G₀
  let J₀ : Subgroup ↥G₀ := J.subgroupOf G₀
  let K₀ : Subgroup ↥G₀ := K.subgroupOf G₀

  have hAL : A ≤ Subgroup.normalizer (L : Set X) :=
    (le_of_eq hB1Aeq.symm).trans hB1L
  have hAJ : A ≤ Subgroup.normalizer (J : Set X) :=
    (le_of_eq hB1Aeq.symm).trans hB1J
  have hAelem3 : CFSG.Open.IsElemAbelian 3 A := by
    simpa only [hp3] using hAel
  have hinner := rckExcCaseV_inner_on_L h hV
  obtain ⟨F, hField, hFinite, σ, eF, x₀, hf, hFcard,
    hFcard2, hσ, hk, hxD, hx0A0, hxord0, hWeq, hxcomp, hLf, hntX, hSCgeom,
    c, Q, m, hQ, hQm, hcx, hLc,
    cbar, hcbar_eq, hcxbar, hLbar,
    nθ, hnθ, ⟨aξ, haξ⟩, S, hX, hLmap, hS, hFix,
    ⟨ζ, hζ3, hζeq⟩, ⟨J6, hJ6mat, hJ6eq⟩, Φ, θ, hΦ, hθ⟩ :=
    rckExcCaseV_exists_original_canonical_frame h hV
  letI : Field F := hField
  letI : Finite F := hFinite
  let Ω := AlgebraicClosure F
  let iF : F →+* Ω := algebraMap F Ω
  let Fbar : Subfield Ω := iF.fieldRange
  let ε : F ≃+* Fbar := iF.rangeRestrictFieldEquiv
  let σbar : Fbar ≃+* Fbar := ε.symm.trans (σ.trans ε)
  let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
  letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
  letI : Algebra k F := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
  letI : Algebra k Fbar := (ε.toRingHom.comp (algebraMap k F)).toAlgebra
  haveI : CharP F 2 := CFSG.SeitzReduction.TwistedE6Pilot.charP_two_of_card hf hFcard
  haveI : CharP Ω 2 := charP_of_injective_algebraMap
    (algebraMap F (AlgebraicClosure F)).injective 2
  let σQ : Ω ≃+* Ω := iterateFrobeniusEquiv Ω 2 f
  let bε : ModGL TwistTag.E6.tag F →* ModGL TwistTag.E6.tag Fbar :=
    baseChangeGL (τ := Tag.E6) ε.toRingHom
  let ι₁ : ↥G₀ →* ModGL TwistTag.E6.tag F :=
    (twistedE6RootGroup F σ).subtype.comp eF.toMonoidHom
  let ιbar : ↥G₀ →* ModGL TwistTag.E6.tag Fbar := bε.comp ι₁
  let ι : ↥G₀ →* ModGL TwistTag.E6.tag Ω :=
    (MulAut.conj nθ⁻¹).toMonoidHom.comp
      ((baseChangeGL (τ := Tag.E6) Fbar.subtype).comp
        ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar))
  let ψ' : Matrix.SpecialLinearGroup (Fin 6) Ω →* ModGL TwistTag.E6.tag Ω :=
    E6GraphLevi.realize (CharP.cast_eq_zero Ω 2)
  have hFbarcard : Nat.card ↥Fbar = (2 ^ f) ^ 2 := by
    rw [← Nat.card_congr ε.toEquiv]
    exact hFcard
  haveI : Finite ↥Fbar := Finite.of_surjective ε ε.surjective
  let hU : UnitaryFieldData 2 f ↥Fbar :=
    ⟨Nat.prime_two, hf, by rw [hFbarcard, ← pow_mul, mul_comm]⟩
  haveI : CharP ↥Fbar 2 := hU.charP
  have hFmem : ∀ z : Ω, z ∈ Fbar ↔ z ^ ((2 ^ f) ^ 2) = z := by
    intro z
    change z ∈ (algebraMap F Ω).fieldRange ↔ z ^ ((2 ^ f) ^ 2) = z
    rw [mem_algebraMap_fieldRange_iff_pow (F := F) z, hFcard]
  have hσQ : ∀ z : Ω, σQ z = z ^ 2 ^ f :=
    fun z => iterateFrobeniusEquiv_def (R := Ω) (p := 2) (n := f) z

  have hι₁ : Function.Injective ι₁ := Subtype.coe_injective.comp eF.injective
  have hιbar : Function.Injective ιbar :=
    (baseChangeGL_injective (τ := Tag.E6) (f := ε.toRingHom)).comp hι₁
  have hι : Function.Injective ι := by
    have hcb : Function.Injective
        (MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom :=
      (MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).injective
    have hbc : Function.Injective (baseChangeGL (τ := Tag.E6) Fbar.subtype) :=
      baseChangeGL_injective (τ := Tag.E6) (f := Fbar.subtype)
    have hn : Function.Injective (MulAut.conj nθ⁻¹).toMonoidHom :=
      (MulAut.conj nθ⁻¹).injective
    exact hn.comp (hbc.comp (hcb.comp hιbar))
  have hsub : Fbar.subtype.comp ε.toRingHom = algebraMap F Ω := by
    ext a
    rfl
  have hNT : ¬ CFSG.StandardType.SCFourCover.E6AdToral
      ((A.subgroupOf G₀).map ι) := by
    exact CFSG.StandardType.RCKRP.not_e6AdToral_frame_map
      (F := F) (Fbar := ↥Fbar) (Ω := Ω) (H := ↥G₀) (σbar := σbar)
      ε Fbar.subtype hsub Fbar.subtype.injective
      ι₁ (A.subgroupOf G₀) cbar nθ hnθ hntX
  have hx1 : (x₀ : X) ≠ 1 := by
    intro h1
    have h1' : x₀ = 1 := Subtype.ext h1
    rw [h1', orderOf_one] at hxord0
    omega
  have hxordX : orderOf (x₀ : X) = 3 := by
    rw [Subgroup.orderOf_coe, hxord0]
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hJcomp.2.2
  have hLperfect : Group.IsPerfect ↥L := ⟨hxcomp.2.2.1⟩
  haveI : Group.IsPerfect ↥L := hLperfect

  let eL : ↥(L.subgroupOf G₀) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG0
  have heL : ∀ l₀ : ↥(L.subgroupOf G₀), (eL l₀ : X) = (l₀ : X) := fun _ => rfl

  let P := primeFormP hU (idGram Fbar 6)
  let projP : LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) ≃* P :=
    CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num)
  let θL : ↥L ⧸ Subgroup.center ↥L ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) :=
    (QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
      (Subgroup.map_center_eq eL.symm)).trans θ
  let α : A →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAL)
  have hα : ∀ (a : A) (l : ↥L), (α a l : X) = (a : X) * (l : X) * (a : X)⁻¹ :=
    fun a l => Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(a : X), hAL a.2⟩ l
  let ηq : ↥L ⧸ Subgroup.center ↥L ≃* P := θL.trans projP
  let π : ↥L →* P := ηq.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : π = (((QuotientGroup.congr (Subgroup.center ↥L)
      (Subgroup.center ↥L₀) eL.symm
      (Subgroup.map_center_eq eL.symm)).trans θ).trans
    (CFSG.StandardType.InndiagSU.projEquiv hU (by norm_num))).toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center ↥L)) := rfl
  let π0 : ↥L₀ →* P := (θ.trans projP).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center ↥L₀))
  let E6 : gramSU hU (idGram Fbar 6) ≃* StatedSU 6 (2 ^ f) Fbar :=
    CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
      (C₀ := (1 : GL (Fin 6) Fbar)) rfl
  let E3 : gramSU hU (idGram Fbar 3) ≃* StatedSU 3 (2 ^ f) Fbar :=
    CFSG.SeitzReduction.SymplecticPilot.gramSUOneEquiv hU
      (C₀ := (1 : GL (Fin 3) Fbar)) rfl
  have hθL : ∀ s : StatedSU 6 (2 ^ f) Fbar,
      θL (QuotientGroup.mk ((eL.toMonoidHom.comp Φ) s)) =
        LargeEvenProjMk (LargeEvenSUGroup (Fin 6) Fbar (2 ^ f)) s := by
    intro s
    change θ ((QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀)
      eL.symm (Subgroup.map_center_eq eL.symm))
        (QuotientGroup.mk (eL (Φ s)))) = _
    rw [QuotientGroup.congr_mk, eL.symm_apply_apply]
    exact hθ s
  have hπcomp : π.comp eL.toMonoidHom = π0 := by
    apply MonoidHom.ext
    intro l0
    change π (eL l0) = π0 l0
    rw [hπ]
    change (((QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L₀) eL.symm
        (Subgroup.map_center_eq eL.symm)).trans θ).trans projP)
        (QuotientGroup.mk' (Subgroup.center ↥L) (eL l0)) =
      (θ.trans projP) (QuotientGroup.mk' (Subgroup.center ↥L₀) l0)
    simp only [MulEquiv.trans_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.congr_mk, eL.symm_apply_apply]
  have hJ0leL0 : J₀ ≤ L₀ := Subgroup.subgroupOf_mono G₀ hJL
  have hJLmap : (J₀.subgroupOf L₀).map eL.toMonoidHom = J.subgroupOf L := by
    ext l
    constructor
    · rintro ⟨l0, hl0, rfl⟩
      apply Subgroup.mem_subgroupOf.mpr
      have hl0' : ((l0 : ↥G₀) : X) ∈ J :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hl0)
      change ((l0 : ↥G₀) : X) ∈ J
      exact hl0'
    · intro hl
      refine ⟨eL.symm l, ?_, eL.apply_symm_apply l⟩
      apply Subgroup.mem_subgroupOf.mpr
      apply Subgroup.mem_subgroupOf.mpr
      have hl' : (l : X) ∈ J := Subgroup.mem_subgroupOf.mp hl
      have hcoe : ((eL.symm l : ↥L₀) : X) = (l : X) := by
        rw [← heL (eL.symm l), eL.apply_symm_apply]
      simpa only [hcoe] using hl'

  obtain ⟨ρ, ⟨hρker, hρcov, hρ1⟩, d, hdD, hdx, hsup, ⟨i, jExp, hij⟩,
    Bsu, hBsu, hB3, hBns, hBconj, hcovB⟩ :=
    exists_cube_one_su_lift h hV hDA hxD hx1 hxordX (Fbar := ↥Fbar) hU eL
      (Φ := Φ) (θ := θ) hAL hWeq hinner
  let dA : A := ⟨d, hDA hdD⟩
  have hdA : (dA : X) = d := rfl
  let B : primeFormUnitary hU (idGram Fbar 6) := ⟨Bsu, Bsu.2.1⟩
  let JP : Subgroup P := (J.subgroupOf L).map π
  have hB3' : (B : GL (Fin 6) Fbar) ^ 3 = 1 := hB3
  have hBns' : ¬ ∃ c : Fbarˣ, (B : GL (Fin 6) Fbar) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := hBns
  have hBconj' : primeFormConjHom hU (idGram Fbar 6) B = MulAut.conj (ρ dA) := hBconj
  obtain ⟨hJPcomp, hN⟩ :=
    exists_JP_component h hV hDA (Fbar := ↥Fbar) hU eL (Φ := Φ) (θ := θ) hAL hAJ hWeq
      (d := d) hdD hsup (B := B) ρ hρcov hBconj'
  have hgg : CFSG.StandardType.ggFix (primeFormConjHom hU (idGram Fbar 6) B) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hU (idGram Fbar 6) B) := by
    ext z
    rfl
  have hJPcomp' : CFSG.Assembly.IsComponentOf JP
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hU (idGram Fbar 6) B)) := by
    rw [← hgg]
    exact hJPcomp

  obtain ⟨a₁, a₂, g₁, g₂, κ, hact₁, hact₂, hgnc, hκ3, hκ1, hκ12, hcomm12,
    h1B, h2B, hN₁, hN₂, hfOdd,
    aSpec, cSpec, dSpec, U, Lm, εblk, j, T, V, hac, hc3, hmult3, hdeg, hself,
    hd3, hdne, hF, hfinC, hfinD, hcompl, horth, hproj, hop, hinj, hLmat, hLU, hUL,
    hεadj, hrangeU, hεproj, hformula, hrangej, hjmap, hBdiag, hTU, hTV, hVadj, hUV,
    hTdiag, hTeps, hTj, hq3⟩ :=
    rckExcCaseV_exists_original_pair_with_natural_block
      (Ω := Ω) (Fbar := Fbar) (hU := hU) (hFmem := hFmem) (h3dvd := h3dvd)
      (hAel := hAelem3) (hAL := hAL) (hAJ := hAJ)
      (ψ := ψ') (hψ := isSLFrame_realize_standard (Ω := Ω)) (S := S) (hS := hS)
      (ι := ι) (hι := hι) (hXM := hX) (hNT := hNT) (hFix := hFix)
      (eL := eL) (heL := heL) (Φ := Φ) (θ := θ) (hΦ := hΦ) (hθ := hθ)
      (α := α) (hα := rfl) (π := π) (hπ := rfl) (ρ := ρ) (hρcov := hρcov)
      (B := B) (hB3 := hB3') (hBns := hBns') (dA := dA) (hBconj := hBconj') (hN := hN)
      (hJPcomp := hJPcomp')
  have hJP0 : j.range.map
      (QuotientGroup.mk' (normOneScalars hU (gramSU hU (idGram Fbar 6)) 6)) =
        (J₀.subgroupOf L₀).map π0 := by
    have hJPL : j.range.map
        (QuotientGroup.mk' (normOneScalars hU (gramSU hU (idGram Fbar 6)) 6)) =
          (J.subgroupOf L).map π := hjmap
    exact hJPL.trans
      ((CFSG.StandardType.SCFourCover.map_range_eq_of_subgroupOfEquiv eL π0 π hπcomp hJLmap).symm)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ↥Fbar := Fintype.ofFinite ↥Fbar
  let E := GaloisField 2 (2 * f)
  have hEcard : Nat.card E = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hU.one_le
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; positivity)
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card ↥Fbar := by
    simpa only [Nat.card_eq_fintype_card] using hEcard.trans hU.card_eq_sq.symm
  let τGF : E ≃+* ↥Fbar := FiniteField.ringEquivOfCardEq (K := E) (K' := ↥Fbar) hcard
  obtain ⟨P3, hP3⟩ :=
    CFSG.LieType.Universal.Unitary.exists_wittMatrix
      (F := E) (p := 2) (f := f) hEcard 3
  obtain ⟨P6, hP6⟩ :=
    CFSG.LieType.Universal.Unitary.exists_wittMatrix
      (F := E) (p := 2) (f := f) hEcard 6
  have hJPL : j.range.map
      (QuotientGroup.mk' (normOneScalars hU (gramSU hU (idGram Fbar 6)) 6)) =
        (J.subgroupOf L).map ((θL.trans projP).toMonoidHom.comp
          (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    have hJPL0 : j.range.map
        (QuotientGroup.mk' (normOneScalars hU (gramSU hU (idGram Fbar 6)) 6)) =
          (J.subgroupOf L).map π := hjmap
    rw [← hπ]
    exact hJPL0
  obtain ⟨phiL, -, hphiLrange, hphiLker, β, r, hβmem, hβlong, hRphiL, hRmphiL⟩ :=
    CFSG.StandardType.SCFourCover.naturalSU3_whole_pair_in_original_cover
      (X := X) (J := J) (L := L) (R := R) (Rm := Rm)
      hJq hPosJ hJL hLperfect (F := ↥Fbar) hU
      (Φ6 := eL.toMonoidHom.comp Φ) (θ := θL) hθL (j := j) hinj
      (U := U) (D := Lm) (ε := εblk) hLmat hLU hUL hεadj hformula hJPL hq3
      τGF P3 hP3 P6 hP6

  let z : ModGL TwistTag.E6.tag Ω := ψ' S
  let η : Ωˣ := Units.map Fbar.subtype.toMonoidHom aξ
  let cΩ : ModGL TwistTag.E6.tag Ω :=
    baseChangeGL (τ := TwistTag.E6.tag) iF c.val
  let u : ModGL TwistTag.E6.tag Ω := (nθ * z)⁻¹ * cΩ
  let ιF : ↥G₀ →* ModGL TwistTag.E6.tag Ω :=
    (baseChangeGL (τ := TwistTag.E6.tag) iF).comp ι₁
  let ιW : ↥G₀ →* ModGL TwistTag.E6.tag Ω :=
    (MulAut.conj u).toMonoidHom.comp ιF
  have hsub : Fbar.subtype.comp ε.toRingHom = iF := by
    ext a
    rfl
  have hcΩ : baseChangeGL (τ := TwistTag.E6.tag) Fbar.subtype cbar.val = cΩ := by
    rw [hcbar_eq]
    change baseChangeGL (τ := TwistTag.E6.tag) Fbar.subtype
      (baseChangeGL (τ := TwistTag.E6.tag) ε.toRingHom c.val) = cΩ
    rw [baseChangeGL_baseChangeGL, hsub]
  have hiota : ι = (MulAut.conj (nθ⁻¹ * cΩ)).toMonoidHom.comp ιF := by
    have hconj := comp_conj_baseChangeGL_eq (F := F) (Fbar := ↥Fbar) (Ω := Ω) (H := ↥G₀)
      ε.toRingHom Fbar.subtype hsub ι₁ cbar.val nθ
    have hc : (baseChangeGL (τ := Tag.E6) Fbar.subtype)
        (cbar.val : ModGL Tag.E6 Fbar) = (cΩ : ModGL Tag.E6 Ω) := hcΩ
    rw [hc] at hconj
    exact hconj
  have hiW : ιW = (MulAut.conj z⁻¹).toMonoidHom.comp ι := by
    rw [hiota]
    apply MonoidHom.ext
    intro x
    dsimp only [ιW, u]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe,
      MulAut.conj_apply]
    group
  have hW := CFSG.StandardType.SCFourCover.original_twistedE6_frame_fixed_normalizer
    (F := F) (f := f) hf hFcard σ hσ eF c aξ nθ hnθ haξ S J6 hJ6mat hJ6eq
  change ιW.range ≤ adjointGroup Tag.E6 Ω ∧
    (∀ g ∈ ιW.range, e6FrobEnd σQ.toRingHom η g = g) ∧
    (∀ y ∈ adjointGroup Tag.E6 Ω, e6FrobEnd σQ.toRingHom η y = y →
      y ∈ Subgroup.normalizer (ιW.range : Set (ModGL TwistTag.E6.tag Ω))) at hW
  obtain ⟨hWadj, hWfix, hWnorm⟩ := hW

  let dθ : ModGL TwistTag.E6.tag Ω := E6GraphLevi.thetaSL2 Ω (nSL η)
  have hdθrange : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range := ⟨nSL η, rfl⟩
  let FW : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag Ω :=
    e6IdentityFormFrobenius (CharP.cast_eq_zero Ω 2) σQ J6 dθ
  let FEnd : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag Ω :=
    e6FrobEnd σQ.toRingHom η
  have hFW : FW = FEnd :=
    rckExcCaseV_identityFormFrobenius_eq (Ω := Ω) (CharP.cast_eq_zero Ω 2)
      σQ J6 hJ6mat η

  let b6 : StatedSU 6 (2 ^ f) Fbar := E6 Bsu
  let ell0 : ↥L₀ := Φ b6
  let ellL : ↥L := eL ell0
  let ell : ↥G₀ := (ell0 : ↥G₀)
  let Q6 : gramSU hU (idGram Fbar 6) →* SL(6, Ω) :=
    (statedSUToSL Fbar 6 (2 ^ f)).comp E6.toMonoidHom
  let BΩ : SL(6, Ω) := Q6 Bsu
  let TΩ : SL(6, Ω) := Q6 T
  have hBsu3 : Bsu ^ 3 = 1 := by
    apply Subtype.ext
    change (Bsu : GL (Fin 6) Fbar) ^ 3 = 1
    exact hB3
  have hb63 : b6 ^ 3 = 1 := by
    change (E6 Bsu) ^ 3 = 1
    rw [← map_pow, hBsu3, map_one]
  have hell03 : ell0 ^ 3 = 1 := by
    change (Φ b6) ^ 3 = 1
    rw [← map_pow, hb63, map_one]
  have hell3 : ell ^ 3 = 1 := by
    change (L₀.subtype ell0 : ↥G₀) ^ 3 = 1
    simpa only [map_pow, map_one] using congrArg L₀.subtype hell03
  have hellmem : ell ∈ L₀ := ell0.2
  have hellX : (ellL : X) = (ell : X) := heL ell0
  have hcover : ι ell = ψ' S * ψ' BΩ * (ψ' S)⁻¹ := by
    change ι ((Φ b6 : ↥L₀) : ↥G₀) = _
    exact hΦ b6
  have hπell : π ellL = ρ dA := by
    have h1 : π ellL = π0 ell0 := by
      change π (eL ell0) = π0 ell0
      exact DFunLike.congr_fun hπcomp ell0
    rw [h1]
    change (θ.trans projP) (QuotientGroup.mk (Φ b6)) = ρ dA
    rw [rckExcCaseV_projEquiv_gramSUOneEquiv (f := f) hU Φ θ hθ Bsu]
    exact hBsu
  have hπker : π.ker = Subgroup.center ↥L :=
    (MonoidHom.ker_comp_of_injective
      (QuotientGroup.mk' (Subgroup.center ↥L)) ηq.toMonoidHom ηq.injective).trans
        (QuotientGroup.ker_mk' (Subgroup.center ↥L))
  have hsame : (α dA).toMonoidHom = (MulAut.conj ellL).toMonoidHom := by
    apply CFSG.SeitzReduction.LinearPilot.eq_of_comp_eq_of_ker_le_center
      (p := π) hπker.le
    intro l
    change π (α dA l) = π (ellL * l * ellL⁻¹)
    rw [map_mul, map_mul, map_inv, hπell]
    exact hρcov dA l
  have hconjL : ∀ l : ↥L, α dA l = ellL * l * ellL⁻¹ := by
    intro l
    exact DFunLike.congr_fun hsame l
  let d0 : ↥G₀ := ⟨d, (hDA.trans hAG) hdD⟩
  have hact : ∀ y ∈ L₀, d0 * y * d0⁻¹ = ell * y * ell⁻¹ := by
    intro y hy
    have hyL : (y : X) ∈ L := (Subgroup.mem_subgroupOf.mp hy)
    let l : ↥L := ⟨(y : X), hyL⟩
    have hXeq : d * (l : X) * d⁻¹ = (ellL : X) * (l : X) * (ellL : X)⁻¹ := by
      have h := congrArg (fun z : ↥L => (z : X)) (hconjL l)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hα dA l, hdA] using h
    apply Subtype.ext
    change (d0 : X) * (y : X) * (d0 : X)⁻¹ = (ell : X) * (y : X) * (ell : X)⁻¹
    change d * (y : X) * d⁻¹ = (ell : X) * (y : X) * (ell : X)⁻¹
    rw [← hellX]
    exact hXeq
  have hAel3 : ∀ x ∈ A, x ^ 3 = 1 := by
    intro x hx
    simpa only [hp3] using hAel.2 x hx
  have hd03 : d0 ^ 3 = 1 := by
    apply Subtype.ext
    change d ^ 3 = 1
    simpa only using hAel3 d (hDA hdD)
  have hdx0 : d0 * x₀ = x₀ * d0 := by
    apply Subtype.ext
    change d * (x₀ : X) = (x₀ : X) * d
    exact hAel.comm (hDA hdD) (Subgroup.mem_subgroupOf.mp hx0A0)
  have hxL : ∀ y ∈ L₀, x₀ * y = y * x₀ := by
    intro y hy
    have hyL : (y : X) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hz : (x₀ : X) ∈ Subgroup.zpowers (x₀ : X) := Subgroup.mem_zpowers _
    have hxinf : (x₀ : X) ∈ A ⊓ Subgroup.centralizer (L : Set X) := by
      rw [hWeq]
      exact hz
    have hxcent : (x₀ : X) ∈ Subgroup.centralizer (L : Set X) := hxinf.2
    have hcomm : (x₀ : X) * (y : X) = (y : X) * (x₀ : X) :=
      (Subgroup.mem_centralizer_iff.mp hxcent (y : X) hyL).symm
    apply Subtype.ext
    exact hcomm
  let ζΩ : Ωˣ := Units.map Fbar.subtype.toMonoidHom ζ
  have hζΩord : orderOf ζΩ = 3 := by
    rw [orderOf_injective (Units.map Fbar.subtype.toMonoidHom)
      (Units.map_injective Fbar.subtype.injective)]
    exact hζ3
  have hxI : ((MulAut.conj nθ⁻¹).toMonoidHom.comp
      ((baseChangeGL (τ := Tag.E6) Fbar.subtype).comp
        ((MulAut.conj (cbar : ModGL TwistTag.E6.tag Fbar)).toMonoidHom.comp ιbar))) x₀ =
      thetaTorusHom Ω ζΩ := by
    change ι x₀ = thetaTorusHom Ω ζΩ
    rw [hζeq]
    rfl
  have hιrange : ι₁.range = twistedE6RootGroup F σ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (eF x).2
    · intro hy
      refine ⟨eF.symm ⟨y, hy⟩, ?_⟩
      change ((eF (eF.symm ⟨y, hy⟩) : twistedE6RootGroup F σ) : ModGL TwistTag.E6.tag F) = y
      rw [eF.apply_symm_apply]
  have hσbar : ∀ z : Fbar, σbar z = z ^ 2 ^ f := sigmaBar_eq_pow hσ
  have hrangebar : ιbar.range = twistedE6RootGroup Fbar σbar := by
    change (bε.comp ι₁).range = twistedE6RootGroup Fbar σbar
    rw [MonoidHom.range_comp, hιrange, twistedE6RootGroup, twistedE6RootGroup]
    change Subgroup.map (baseChangeGL (τ := Tag.E6) ε.toRingHom)
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom) =
      graphFixedRootGroup TwistTag.E6 Fbar σbar.toRingHom
    exact map_baseChangeGL_graphFixedRootGroup_eq (t := TwistTag.E6) (p := 2)
      Nat.prime_two hf F hFcard σ.toRingHom hσ ε.toRingHom hσbar σbar.surjective
  have hf2 : 2 ≤ f := by
    have hf0 : f ≠ 0 := by
      intro h0
      rw [h0] at hq3
      norm_num at hq3
    have hf1 : f ≠ 1 := by
      intro h1
      rw [h1] at hq3
      norm_num at hq3
    omega
  obtain ⟨tres, htres3, hres, hdW⟩ :=
    CFSG.StandardType.SCFourCover.exists_corootResidualTorus_of_original_data
      (F := Fbar) (σ := σbar) (k := k) (H := ↥G₀)
      (ι₀ := ιbar) (L := L₀) (x := x₀) (c := cbar) (n := nθ) (S := S) (ζ := ζΩ)
      (d := d0) (ell := ell) (B := BΩ)
      hf2 hFbarcard hσbar hk hrangebar hLbar hnθ hζΩord hxI
      hellmem hd03 hell3 hact hdx0 hxL hcover
  have hc0 : cSpec ≠ 0 := by
    intro h0
    rw [h0] at hc3
    norm_num at hc3
  have hd0 : dSpec ≠ 0 := by
    intro h0
    rw [h0] at hd3
    norm_num at hd3
  let cF : (↥Fbar)ˣ := Units.mk0 cSpec hc0
  let dF : (↥Fbar)ˣ := Units.mk0 dSpec hd0
  let cΩu : Ωˣ := Units.map Fbar.subtype.toMonoidHom cF
  let dΩu : Ωˣ := Units.map Fbar.subtype.toMonoidHom dF
  have hcF3 : cF ^ 3 = 1 := by
    apply Units.ext
    simpa only [cF, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using hc3
  have hdF3 : dF ^ 3 = 1 := by
    apply Units.ext
    simpa only [dF, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using hd3
  have hcΩ3 : cΩu ^ 3 = 1 := by
    dsimp only [cΩu]
    rw [← map_pow, hcF3, map_one]
  have hdΩ3 : dΩu ^ 3 = 1 := by
    dsimp only [dΩu]
    rw [← map_pow, hdF3, map_one]
  have hQ6mul : TΩ⁻¹ * BΩ * TΩ = Q6 (T⁻¹ * Bsu * T) := by
    dsimp only [TΩ, BΩ]
    rw [map_mul, map_mul, map_inv]
  have hTdiagU : (((T : GL (Fin 6) Fbar)⁻¹ : GL (Fin 6) Fbar) :
      Matrix (Fin 6) (Fin 6) Fbar) *
      ((Bsu : GL (Fin 6) Fbar) : Matrix (Fin 6) (Fin 6) Fbar) *
      ((T : GL (Fin 6) Fbar) : Matrix (Fin 6) (Fin 6) Fbar) =
        Matrix.diagonal ![(cF : Fbar), (cF : Fbar), (cF : Fbar),
          (dF : Fbar), (dF : Fbar), (dF : Fbar)] := by
    simpa only [cF, dF, Units.val_mk0] using hTdiag
  have hmatΩ : (((TΩ⁻¹ * BΩ * TΩ : SL(6, Ω)) : Matrix (Fin 6) (Fin 6) Ω)) =
      Matrix.diagonal (fun k => ((![cΩu, cΩu, cΩu, dΩu, dΩu, dΩu] : Fin 6 → Ωˣ) k : Ω)) := by
    rw [hQ6mul]
    simpa only [cΩu, dΩu, Q6, E6] using
      (rckExcCaseV_matrix_diagonal_transport (Fbar := Fbar) (hU := hU)
        (Bsu := Bsu) (T := T) (c := cF) (d := dF) (hTdiag := hTdiagU))
  have hζΩcube : ζΩ ^ 3 = 1 := by
    simpa only [hζΩord] using pow_orderOf_eq_one ζΩ
  have hxW : (MulAut.conj (ψ' S)⁻¹).toMonoidHom.comp ι x₀ = thetaTorusHom Ω ζΩ := by
    have hψS : ψ' S ∈ subsystemGroup TwistTag.E6.tag Ω E6GraphLevi.setA := by
      rw [← E6GraphLevi.range_realize (CharP.cast_eq_zero Ω 2)]
      exact ⟨S, rfl⟩
    have hcent := E6GraphLevi.subsystemGroup_le_centralizer_thetaSL2
      (CharP.cast_eq_zero Ω 2) hψS
    have hHmem : thetaTorusHom Ω ζΩ ∈ (E6GraphLevi.thetaSL2 Ω).range := by
      rw [E6GraphLevi.thetaTorusHom_eq_thetaSL2]
      exact ⟨HSL ζΩ, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hcent _ hHmem
    change (ψ' S)⁻¹ * ι x₀ * ψ' S = thetaTorusHom Ω ζΩ
    rw [hζeq]
    change (ψ' S)⁻¹ * thetaTorusHom Ω ζΩ * ψ' S = thetaTorusHom Ω ζΩ
    calc (ψ' S)⁻¹ * thetaTorusHom Ω ζΩ * ψ' S
        = (ψ' S)⁻¹ * (thetaTorusHom Ω ζΩ * ψ' S) := by group
      _ = (ψ' S)⁻¹ * (ψ' S * thetaTorusHom Ω ζΩ) := by rw [hcomm]
      _ = thetaTorusHom Ω ζΩ := by group
  let iN : ℕ := (i % 3).toNat
  let jN : ℕ := (jExp % 3).toNat
  have hiCast : (iN : ℤ) = i % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0))
  have hjCast : (jN : ℤ) = jExp % 3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg jExp (by norm_num : (3 : ℤ) ≠ 0))
  have hd0ne : d0 ≠ 1 := by
    intro h
    apply hdx
    rw [← show (d0 : X) = d from rfl, congrArg Subtype.val h]
    exact Subgroup.one_mem _
  have hdord : orderOf d0 = 3 := orderOf_eq_prime hd03 hd0ne
  have hxi : x₀ ^ i = x₀ ^ iN := by
    calc x₀ ^ i = x₀ ^ (i % 3) := by
          simpa only [hxord0, Nat.cast_ofNat] using (zpow_mod_orderOf x₀ i).symm
      _ = x₀ ^ iN := by rw [← hiCast, zpow_natCast]
  have hdj : d0 ^ jExp = d0 ^ jN := by
    calc d0 ^ jExp = d0 ^ (jExp % 3) := by
          simpa only [hdord, Nat.cast_ofNat] using (zpow_mod_orderOf d0 jExp).symm
      _ = d0 ^ jN := by rw [← hjCast, zpow_natCast]
  let e0 : ↥G₀ := ⟨e, heG0⟩
  have he0 : e0 = x₀ ^ iN * d0 ^ jN := by
    have he0' : e0 = x₀ ^ i * d0 ^ jExp := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_mk] using hij
    rw [he0', hxi, hdj]
  obtain ⟨hxT, hdT, heT, ha3, hb3⟩ :=
    CFSG.StandardType.SCFourCover.conj_rootDiagUnit_cubic_original_e
      (Ω := Ω) (H := ↥G₀) (CharP.cast_eq_zero Ω 2)
      (ιW := (MulAut.conj (ψ' S)⁻¹).toMonoidHom.comp ι)
      (x := x₀) (d := d0) (e := e0) (ζ := ζΩ) (t := tres)
      (c := cΩu) (dval := dΩu) (B := BΩ) (T := TΩ) (i := iN) (j := jN)
      hxW hdW he0 hmatΩ hζΩcube htres3 hcΩ3 hdΩ3
  let τ : ModGL TwistTag.E6.tag Ω := ψ' (statedSUToSL Fbar 6 (2 ^ f) (E6 T))
  let C : ModGL TwistTag.E6.tag Ω := z * τ
  let ιT : ↥G₀ →* ModGL TwistTag.E6.tag Ω := (MulAut.conj C⁻¹).toMonoidHom.comp ι
  let ΓT : Subgroup (ModGL TwistTag.E6.tag Ω) := ιT.range
  let κT : ModGL TwistTag.E6.tag Ω →* ModGL TwistTag.E6.tag Ω :=
    (MulAut.conj τ⁻¹).toMonoidHom
  have hιT : Function.Injective ιT := (MulAut.conj C⁻¹).injective.comp hι
  have hιT_cubic : ιT = (MulAut.conj (ψ' TΩ)⁻¹).toMonoidHom.comp
      ((MulAut.conj (ψ' S)⁻¹).toMonoidHom.comp ι) := by
    have hτT : ψ' TΩ = τ := rfl
    rw [hτT]
    apply MonoidHom.ext
    intro x
    change (z * τ)⁻¹ * ι x * ((z * τ)⁻¹)⁻¹ =
      τ⁻¹ * (z⁻¹ * ι x * (z⁻¹)⁻¹) * (τ⁻¹)⁻¹
    group
  have hτmem : τ ∈ subsystemGroup TwistTag.E6.tag Ω E6GraphLevi.setA := by
    change ψ' (statedSUToSL Fbar 6 (2 ^ f) (E6 T)) ∈ _
    rw [← E6GraphLevi.range_realize (CharP.cast_eq_zero Ω 2)]
    exact ⟨_, rfl⟩
  have hτadj : τ ∈ adjointGroup Tag.E6 Ω :=
    E6GraphLevi.subsystemGroup_le_adjointGroup hτmem
  have hiT : ιT = κT.comp ιW := by
    rw [hiW]
    apply MonoidHom.ext
    intro x
    change (z * τ)⁻¹ * ι x * ((z * τ)⁻¹)⁻¹ =
      τ⁻¹ * (z⁻¹ * ι x * (z⁻¹)⁻¹) * (τ⁻¹)⁻¹
    group
  have hΓT : ΓT = ιW.range.map κT := by
    change ιT.range = ιW.range.map κT
    rw [hiT, MonoidHom.range_comp]
  have hTfix : ∀ g ∈ ΓT, FW g = g := by
    rw [hΓT]
    exact rckExcCaseV_naturalT_frame_fixed
      (Ω := Ω) (Fbar := Fbar) (hU := hU) (hFmem := hFmem) (hFbarcard := hFbarcard)
      (σQ := σQ) (hσQ := hσQ) (hJ6mat := hJ6mat) (hdθrange := hdθrange)
      (T := T) (W := ιW.range)
      (hWfix := by
        intro g hg
        change FW g = g
        rw [hFW]
        exact hWfix g hg)
  have hΓTadj : ΓT ≤ adjointGroup Tag.E6 Ω := by
    rw [hΓT]
    intro g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    exact (adjointGroup Tag.E6 Ω).mul_mem
      ((adjointGroup Tag.E6 Ω).mul_mem ((adjointGroup Tag.E6 Ω).inv_mem hτadj)
        (hWadj hw)) hτadj
  have hJ0q : CFSG.Assembly.IsQuasisimple ↥J₀ :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJG0) hJq
  have hJ0K0 : J₀ ≤ K₀ := Subgroup.subgroupOf_mono G₀ hJK
  have hK0ne : K₀ ≠ J₀ := by
    intro heq
    apply hKne
    have hEqInf : K ⊓ G₀ = J ⊓ G₀ := Subgroup.subgroupOf_inj.mp heq
    simpa only [inf_eq_left.mpr hKG0, inf_eq_left.mpr hJG0] using hEqInf
  have hK0comp : CFSG.Assembly.IsComponentOf K₀
      (Subgroup.centralizer ({e0} : Set (↥G₀))) :=
    rckExcCaseV_isComponentOf_subgroupOf_centralizer heG0 hKcomp
  have hOriginalJ : J₀.map ιT =
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6LineFactor Ω 0 ⊓ ΓT :=
    rckExcCaseV_original_J_eq_of_natural_block
      (Ω := Ω) (Fbar := Fbar) (hU := hU) (hFmem := hFmem)
      (σQ := σQ) (hσQ := hσQ) (hJ6mat := hJ6mat) (hdθrange := hdθrange)
      (H := ↥G₀) (J0 := J₀) (L0 := L₀) (hJ0leL0 := hJ0leL0) (hJ0q := hJ0q)
      (j := j) (hq3 := hq3) (Φ := Φ) (θ := θ) (hθ := hθ) (hJP0 := hJP0)
      (T := T) (hTj := hTj) (ι := ι) (S := S) (hΦ := hΦ)
      (ιT := ιT) (hiT := rfl) (hTfix := hTfix)
  let aCoord : Ωˣ := ζΩ ^ iN * tres ^ jN
  let bCoord : Ωˣ := (cΩu / dΩu) ^ jN
  have hePlane : ιT e0 = rootDiagUnit Tag.E6
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6BlockPlaneChar aCoord bCoord) := by
    rw [hιT_cubic]
    simpa only [TwistTag.tag, ψ',
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6BlockPlaneChar,
      aCoord, bCoord] using heT
  have ha1 : aCoord ≠ 1 :=
    CFSG.StandardType.KGL.e6LineFactor_inf_coord_ne_one
      (H := ↥G₀) (ι := ιT) (J := J₀) (K := K₀) (e := e0)
      (a := aCoord) (b := bCoord)
      hιT hJ0q hK0comp hJ0K0 hK0ne hOriginalJ hΓTadj hePlane hb3 (by
        intro h
        apply he1
        exact congrArg Subtype.val h)
  have ha3' : aCoord ^ 3 = 1 := ha3
  have hb3' : bCoord ^ 3 = 1 := hb3
  obtain ⟨nActor, hnActorMem, hnActorFix, hnActorConj, hnActorComm0, hnActorComm1⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.exists_e6LineFactor_conj_blockPlane_fixed
      (Ω := Ω) (q := 2 ^ f) σQ.toRingHom hσQ η aCoord bCoord ha3' ha1 hb3'
  let nT : ModGL TwistTag.E6.tag Ω := nActor
  have hActorAdj : nActor ∈ adjointGroup Tag.E6 Ω :=
    CFSG.LieType.Chevalley.rootSpan_le_adjointGroup Ω _ hnActorMem
  have hynorm : nActor ∈ Subgroup.normalizer (ΓT : Set (ModGL TwistTag.E6.tag Ω)) := by
    rw [hΓT]
    exact rckExcCaseV_naturalT_frame_normalizer
      (Ω := Ω) (Fbar := Fbar) (hU := hU) (hFmem := hFmem) (hFbarcard := hFbarcard)
      (σQ := σQ) (hσQ := hσQ) (hJ6mat := hJ6mat) (hdθrange := hdθrange)
      (T := T) (W := ιW.range)
      (hWnorm := by
        intro y hy hfy
        change FW y = y at hfy
        rw [hFW] at hfy
        exact hWnorm y hy hfy)
      nActor hActorAdj (by
        change FW nActor = nActor
        rw [hFW]
        exact hnActorFix)
  have hyJ : ∀ t' : ↥G₀, (t' : X) ∈ J → nT * ιT t' = ιT t' * nT := by
    intro t' ht'
    have hmem : ιT t' ∈ J₀.map ιT :=
      Subgroup.mem_map_of_mem ιT (Subgroup.mem_subgroupOf.mpr ht')
    rw [hOriginalJ] at hmem
    exact hnActorComm0 (ιT t') (Subgroup.mem_inf.mp hmem).1
  have hxT' : ιT x₀ = thetaTorusHom Ω ζΩ := by
    rw [hιT_cubic]
    exact hxT
  obtain ⟨k, -, hak⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6Line_exists_pow_eq_of_pow_three_eq_one
      hζΩcube (by
        intro h
        rw [h, orderOf_one] at hζΩord
        omega) ha3'
  let e0T : ModGL Tag.E6 Ω := ιT e0
  have hePlaneT : e0T = rootDiagUnit Tag.E6
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6BlockPlaneChar aCoord bCoord) :=
    hePlane
  let x0T : ModGL Tag.E6 Ω := ιT x₀
  let θT : Ωˣ →* ModGL Tag.E6 Ω := thetaTorusHom Ω
  have hx0T : x0T = θT ζΩ := hxT'
  have hyePow : nActor * e0T * nActor⁻¹ = x0T ^ k := by
    calc nActor * e0T * nActor⁻¹
        = rootDiagUnit Tag.E6
            (CFSG.SeitzReduction.EPilot.highDiag .E6 aCoord) := by
          rw [hePlaneT]
          simpa only [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.e6BlockPlaneChar]
            using hnActorConj
      _ = θT aCoord := rfl
      _ = θT (ζΩ ^ k) := by rw [hak]
      _ = (θT ζΩ) ^ k := map_pow _ _ _
      _ = x0T ^ k := by rw [hx0T]
  have hye : nActor * e0T * nActor⁻¹ ∈ Subgroup.zpowers x0T := by
    rw [hyePow]
    exact (Subgroup.zpowers x0T).pow_mem (Subgroup.mem_zpowers _) k
  have hKcomp0 : CFSG.Assembly.IsComponentOf K
      (G₀ ⊓ Subgroup.centralizer ({(e0 : X)} : Set X)) := hKcomp
  obtain ⟨phiK, hphiKrange, hphiKker, hRphiK, hRmphiK⟩ :=
    exists_rootPairCover_of_normalizing_actor
      (D := (ggU .PSU 6 f).D) (G₀ := G₀) (J := J) (K := K) (L := L)
      (R := R) (Rm := Rm) (e₀ := e0) (x₀ := x₀) (p := 3)
      (U := (ggU .PSU 6 f).K)
      Nat.prime_three hxord0 (by
        intro h
        apply he1
        exact congrArg Subtype.val h) hKcomp0 hxcomp hJq hJK hJL hRJ hRmJ
      ιT hιT hynorm hyJ hye phiL hphiLrange β r hRphiL hRmphiL
  refine ⟨hf, phiL, phiK, β, r, hphiLrange, hphiKrange, hphiKker, hphiLker,
    hβmem, hβlong, hRphiL, hRmphiL, hRphiK, hRmphiK⟩

theorem rckExcCaseVNbr_holds :
    RCKExcCaseVNbr := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e hGG hcfg hKne hV
  obtain ⟨hf, phiL, phiK, β, r, hphiLrange, hphiKrange, hphiKker, hphiLker,
    hβmem, hβlong, hRphiL, hRmphiL, hRphiK, hRmphiK⟩ :=
    rckExcCaseV_original_strong_pair hcfg hKne hV
  exact ggRootPosNbr_of_rootPosJ
    (Or.inl ⟨.PSU, 6, f, β, Or.inr (Or.inl rfl), hf, hβlong,
      ⟨phiK, hphiKrange, by rw [hphiKker]; exact hphiLker, r, hRphiK, hRmphiK⟩⟩)

end RckExcCaseVInnerOnL

end CFSG.StandardType.RCKRP

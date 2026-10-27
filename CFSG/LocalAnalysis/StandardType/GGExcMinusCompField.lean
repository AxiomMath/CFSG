module

public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLarge
import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoBase
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
import CFSG.LocalAnalysis.StandardType.GGLangRatCompC
import CFSG.LocalAnalysis.StandardType.GGLangRatCompFieldLen
import CFSG.LocalAnalysis.StandardType.GGA6GlueTransport
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddToral
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7Model
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE8Model
import CFSG.LieType.Chevalley.SingleEdgePerfect
import CFSG.Blueprint.ChevalleyRoots
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
import CFSG.LocalAnalysis.StandardType.GGKGAF4Core
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

namespace ExcMinusField

private theorem frameDiag_mem_twistedTorus
    {τ : Tag} {p : ℕ} [NeZero p] {K : Type} [Field K] [Finite K]
    (hfull : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a ∈ torusGroup τ (AlgebraicClosure K))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ p = 1)
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (s : Fin τ.rank → ZMod p) :
    ExcFrames.frameDiag ζ hζ s ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (Units.map (entrywiseHom Fr)) := by
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  refine CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.2 ⟨hfull _, ?_⟩
  · have hds : ExcFrames.frameDiag ζ hζ s =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) * g0 := by
      rw [hbase s]
      group
    rw [hds]
    exact ExcTwoGen.frob_conj_baseChange_two hFr hg0 _

private theorem exists_langSetup_data
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {w : WeylGroup τ} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hdesc : ∀ D : LangDatum τ (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) →
      LangDescent D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype)) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5),
      S.D.Φ = Units.map (entrywiseHom Fr) ∧ S.D.q = Nat.card K ∧
      S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧ S.D.g0 = g0 ∧
      LangDescent S.D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype) := by
  classical
  let L := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let D : LangDatum τ L :=
    { Φ := Units.map (entrywiseHom Fr)
      q := Nat.card K
      n := canonicalRep (coxeterSystem τ) L w
      g0 := g0
      steinberg := ⟨Fr, hFr, ⟨1, Or.inl rfl, fun g => by simp⟩⟩
      n_weyl := ⟨w, rfl⟩
      g0_mem := hg0C
      lang := hg0 }
  have hd : LangDescent D 7 ((baseChangeGL (algebraMap K L)).comp
      (adjointGroup τ K).subtype) := hdesc D rfl
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    refine ⟨?_, ?_⟩
    · show IsPrimePow (Nat.card K)
      rw [hK]
      exact Nat.prime_two.isPrimePow.pow f.ne_zero
    · show ((Nat.card K : ℕ) : L) = 0
      rw [hK]
      exact (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 f.ne_zero)
  have hpq : ¬ 5 ∣ D.q := by
    show ¬ 5 ∣ Nat.card K
    rw [hK]
    intro h5
    have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h5
    norm_num at h52
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ L D
  let S : LangSetup τ L 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl le_rfl) hqpow hpq hd.finite_model
  exact ⟨S, rfl, rfl, rfl, rfl, hd⟩

theorem exists_langSetup_of_langFrame_of_descent
    {τ : Tag} {p : ℕ} [NeZero p] {K : Type} [Field K] [Finite K]
    [CharP K 2] {w : WeylGroup τ} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g0 : ModGL τ (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹)
    (hfull : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a ∈ torusGroup τ (AlgebraicClosure K))
    (hdesc : ∀ D : LangDatum τ (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) →
      LangDescent D 7 ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype)) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D.Φ = Units.map (entrywiseHom Fr) ∧ S.D.q = Nat.card K ∧
      S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s : Fin τ.rank → ZMod p,
        ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s) ∧
      ∀ s : Fin τ.rank → ZMod p, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus := by
  classical
  obtain ⟨S, hΦ, hq, hn, hg0S, hd⟩ := exists_langSetup_data hFr hg0C hg0 hdesc
  let bc : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype
  let ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp bc
  have hι : ∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL τ K) * g0 := by
    intro c
    change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c : ModGL τ K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hrange : ι.range = S.Γ := by
    have hcomp : ι = (MulAut.conj g0⁻¹).toMonoidHom.comp bc := rfl
    rw [hcomp, MonoidHom.range_comp, show S.Γ = S.D.Γ from rfl, hd.Γ_eq, hg0S]
  have hinjι : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp
      (Subgroup.subtype_injective _))
  refine ⟨S, ι, hΦ, hq, hn, hinjι, hrange, ?_, ?_⟩
  · intro s
    rw [hι, hbase s]
    group
  · intro s
    have hmem := frameDiag_mem_twistedTorus hfull hFr hg0 hζ hbase s
    rw [show S.D.torus = CFSG.RankThree.PartOne.KE.twistedTorusOf (canonicalRep (coxeterSystem τ)
      (AlgebraicClosure K) w) (Units.map (entrywiseHom Fr)) from by
        rw [LangDatum.torus, hΦ, hn]]
    exact hmem

theorem exists_langSetup_of_langFrame
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [NeZero p] {K : Type} [Field K] [Finite K]
    [CharP K 2] {w : WeylGroup τ} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g0 : ModGL τ (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hbase : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D.Φ = Units.map (entrywiseHom Fr) ∧ S.D.q = Nat.card K ∧
      S.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ s : Fin τ.rank → ZMod p,
        ι (ι₀ (Multiplicative.ofAdd s)) = ExcFrames.frameDiag ζ hζ s) ∧
      ∀ s : Fin τ.rank → ZMod p, ExcFrames.frameDiag ζ hζ s ∈ S.D.torus := by
  refine exists_langSetup_of_langFrame_of_descent hFr hg0C hg0 hbase (fun a => ?_)
    (fun D hΦ => ?_)
  · rcases hτ with rfl | rfl
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_E7 _
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_E8 _
  · have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
      single_edge_perfect τ K (by rcases hτ with rfl | rfl <;> simp)
    rcases hτ with h | h
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h, rfl⟩)) hFr D hΦ Nat.prime_seven
        (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h, rfl⟩)) hFr D hΦ Nat.prime_seven
        (by norm_num) hperf

end ExcMinusField

end CFSG.StandardType

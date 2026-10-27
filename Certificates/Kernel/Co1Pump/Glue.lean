module

public import Certificates.Kernel.Co1Pump.Fus
public import Certificates.Kernel.Co1Pump.Kill
public import Certificates.Kernel.Co1Pairs.Glue
public import Certificates.Kernel.Co1Pairs.OrbU
public import Certificates.Kernel.Co1SevenK.RepsGlue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
public import Certificates.Certificate13697
public import Certificates.Certificate13698
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Pump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native CFSG.KS.SporSch.M24
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.KC.Co1Pairs CFSG.KD.Co1Pump CertificateChecks.KernelCo1ThreeK CertificateChecks.KernelCo1Pairs
open CFSG.Sporadic.SmallF2.Native (transposeRows)
open CertificateChecks.KernelSporSch.Co1Elem (AF)

theorem fusOK_nil (gs : List Nat) (G : Nat → Nat) (D k : Nat) :
    fusOK gs G D [] k = Nat.beq k 729 := rfl

theorem fusOK_cons (gs : List Nat) (G : Nat → Nat) (D : Nat) (r : Nat × Nat) (L : List (Nat × Nat))
    (k : Nat) : fusOK gs G D (r :: L) k =
      Bool.rec (motive := fun _ => Bool) false (fusOK gs G D L (Nat.succ k)) (recOK gs G D k r.1 r.2) :=
  rfl

theorem fusOK_spec {gs : List Nat} {G : Nat → Nat} {D : Nat} :
    ∀ (L : List (Nat × Nat)) (k : Nat), fusOK gs G D L k = true →
      k + L.length = 729 ∧
        ∀ i < L.length, recOK gs G D (k + i) (L.getD i (0, 0)).1 (L.getD i (0, 0)).2 = true := by
  intro L
  induction L with
  | nil =>
    intro k h
    rw [fusOK_nil] at h
    refine ⟨by simpa using Nat.eq_of_beq_eq_true h, fun i hi => absurd hi (by simp)⟩
  | cons r L ih =>
    intro k h
    rw [fusOK_cons] at h
    obtain ⟨h1, h2⟩ := bAnd_eq h
    obtain ⟨hl, hall⟩ := ih (Nat.succ k) h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      have hi' : i < L.length := by simp only [List.length_cons] at hi; omega
      have e : k + (i + 1) = Nat.succ k + i := by omega
      rw [e]
      simpa using hall i hi'

theorem rootK_spec {j : Nat} (h : CFSG.KC.Co1Pairs.rootK j = true) :
    j = 243 ∨ j = 81 ∨ j = 324 := by
  unfold CFSG.KC.Co1Pairs.rootK at h
  cases h1 : Nat.beq j 243 <;> cases h2 : Nat.beq j 81 <;> rw [h1] at h <;> simp only [h2] at h <;>
    simp_all [Nat.beq_eq]

theorem recOK_spec {gs : List Nat} {G : Nat → Nat} {D j p g : Nat}
    (h : recOK gs G D j p g = true) :
    (p = j ∧ (j = 243 ∨ j = 81 ∨ j = 324)) ∨
      (0 < p ∧ p < 729 ∧ g < 3 ∧ depK D p < depK D j ∧
        CFSG.KC.Co1B.mulWK (G g) (eltK gs (dig3 p)) = CFSG.KC.Co1B.mulWK (eltK gs (dig3 j)) (G g)) := by
  unfold recOK at h
  generalize hc : Bool.rec (motive := fun _ => Bool) false (CFSG.KC.Co1Pairs.rootK j)
    (Nat.beq p j) = c at h
  cases c with
  | true =>
    obtain ⟨h1, h2⟩ := bAnd_eq hc
    exact Or.inl ⟨Nat.eq_of_beq_eq_true h1, rootK_spec h2⟩
  | false =>
    obtain ⟨h1, h⟩ := bAnd_eq h
    obtain ⟨h2, h⟩ := bAnd_eq h
    obtain ⟨h3, h⟩ := bAnd_eq h
    obtain ⟨h4, h5⟩ := bAnd_eq h
    simp only [Nat.blt_eq] at h1 h2 h3 h4
    exact Or.inr ⟨h1, h2, h3, h4, Nat.eq_of_beq_eq_true h5⟩

section Facts


theorem rep_G {i : Nat} (hi : i < 3) :
    MRep (unpack 24 24 (ch36909G i)) (Co1T.wG [14 + 2 * i] : GL24) := by
  have hl : CFSG.KS.SporSch.M24.lettersK 75 [14 + 2 * i] = true := by
    interval_cases i <;> decide +kernel
  have hw : wordWK L.M L.MI [14 + 2 * i] = ch36909G i := by interval_cases i <;> decide +kernel
  have e := Co1T.wordL_rep [14 + 2 * i]
  rwa [wordL_eq hl, hw] at e

theorem conj_of_rows {X A B : Nat} {x a b : ↥GA} (hx : MRep (unpack 24 24 X) (x : GL24))
    (ha : MRep (unpack 24 24 A) (a : GL24)) (hb : MRep (unpack 24 24 B) (b : GL24))
    (h : CFSG.KC.Co1B.mulWK X A = CFSG.KC.Co1B.mulWK B X) : x * a = b * x := by
  have e1 := hx.mul ha
  have e2 := hb.mul hx
  rw [mul_unpackW, h, ← mul_unpackW] at e1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact e1.eq e2

theorem fus_facts : ∀ k, 0 < k → k < 729 → ∃ h r : ↥GA,
    (r = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] ∨ r = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] ∨
      r = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0]) ∧ h * r * h⁻¹ = Co1T.eltG Co1T.aGA (dig3 k) := by
  have hs := fusOK_spec recs 1 ch36909f
  have key : ∀ n k, 0 < k → k < 729 → depK D k = n → ∃ h r : ↥GA,
      (r = Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] ∨ r = Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] ∨
        r = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0]) ∧ h * r * h⁻¹ = Co1T.eltG Co1T.aGA (dig3 k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk0 hk hn
      have hr := hs.2 (k - 1) (by omega)
      have e : 1 + (k - 1) = k := by omega
      rw [e] at hr
      rcases recOK_spec hr with ⟨-, hroot⟩ | ⟨hp0, hp, hg, hd, hc⟩
      · refine ⟨1, Co1T.eltG Co1T.aGA (dig3 k), ?_, by group⟩
        rcases hroot with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      · obtain ⟨h, r, hr', he⟩ := ih _ (hn ▸ hd) _ hp0 hp rfl
        have hgk := conj_of_rows (rep_G hg) (rep_elt _ rfl) (rep_elt _ rfl) hc
        refine ⟨Co1T.wG [14 + 2 * (recs.getD (k - 1) (0, 0)).2] * h, r, hr', ?_⟩
        calc Co1T.wG [14 + 2 * (recs.getD (k - 1) (0, 0)).2] * h * r *
              (Co1T.wG [14 + 2 * (recs.getD (k - 1) (0, 0)).2] * h)⁻¹ =
            Co1T.wG [14 + 2 * (recs.getD (k - 1) (0, 0)).2] * (h * r * h⁻¹) *
              (Co1T.wG [14 + 2 * (recs.getD (k - 1) (0, 0)).2])⁻¹ := by group
          _ = Co1T.eltG Co1T.aGA (dig3 k) := by
            rw [he, hgk, mul_inv_cancel_right]
  intro k hk0 hk
  exact key _ k hk0 hk rfl

theorem pair_facts : ∃ u₁ u₂ : ↥GA,
    u₁ * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * u₁ ∧
    u₂ * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] * u₂ ∧
    orderOf u₁ = 5 ∧ orderOf u₂ = 5 ∧
    1080 < Nat.card ↥(Subgroup.closure ({u₁, u₂} : Set ↥GA)) := by
  have hr := ch214033r
  simp only [Bool.and_eq_true] at hr
  have r2 := rep_elt [1, 1, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true hr.2)
  have hk := ch214033k
  simp only [Bool.and_eq_true] at hk
  have p5 : Nat.Prime 5 := by norm_num
  obtain ⟨q8, c8', o8⟩ := elt_facts p5 r2 ch36909u8 hk.1.1.2
  obtain ⟨q9, c9', o9⟩ := elt_facts p5 r2 ch36909u9 hk.1.2
  have hc8 : CFSG.KD.Co1Pairs.c8.toArray = transposeRows 24 (unpack 24 24 CFSG.KD.Co1Pairs.K8) := by
    decide +kernel
  have hc9 : CFSG.KD.Co1Pairs.c9.toArray = transposeRows 24 (unpack 24 24 CFSG.KD.Co1Pairs.K9) := by
    decide +kernel
  have hd := orbit_dvd q8 q9 hc8 hc9 ch36909o
  haveI : Finite ↥GA := Co1T.finite_GA
  have hpos : 0 < Nat.card ↥(Subgroup.closure ({Co1T.wG CFSG.KD.Co1Pairs.w8,
      Co1T.wG CFSG.KD.Co1Pairs.w9} : Set ↥GA)) := Nat.card_pos
  exact ⟨_, _, c8', c9', o8, o9, lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd hpos hd)⟩

theorem conj_facts {w : List Nat} {X A B : Nat} {a b : ↥GA} (ha : MRep (unpack 24 24 A) (a : GL24))
    (hb : MRep (unpack 24 24 B) (b : GL24)) (h : conjOK L.M L.MI w X A B = true) :
    MRep (unpack 24 24 X) (Co1T.wG w : GL24) ∧ Co1T.wG w * a = b * Co1T.wG w := by
  unfold conjOK at h
  obtain ⟨hl, h⟩ := bAnd_eq h
  obtain ⟨hw, hc⟩ := bAnd_eq h
  have hrep : MRep (unpack 24 24 X) (Co1T.wG w : GL24) := by
    have e := Co1T.wordL_rep w
    rwa [wordL_eq hl, Nat.eq_of_beq_eq_true hw] at e
  exact ⟨hrep, conj_of_rows hrep ha hb (Nat.eq_of_beq_eq_true hc)⟩

theorem rep_root {j : Nat} (hj : j < 3) : MRep (unpack 24 24 (R.M j)) (Co1T.root j : GL24) := by
  obtain ⟨h1, h2, -⟩ := KernelCo1ThreeK.rootK hj
  have e := Co1T.wordL_rep (Co1T.Data.rootWords.getD j [])
  rwa [wordL_eq h1, Nat.eq_of_beq_eq_true h2] at e

theorem kill_facts :
    (∃ c : ↥GA, c * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] = Co1T.root 1 * c) ∧
    (∃ c : ↥GA, c * Co1T.eltG Co1T.aGA [1, 1, 0, 0, 0, 0] = Co1T.root 0 * c) ∧
    (∃ v : ↥GA, v * Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] =
      Co1T.eltG Co1T.aGA [1, 0, 0, 0, 0, 0] * v ∧ orderOf v = 13) ∧
    (∃ v c : ↥GA, v * Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] =
      Co1T.eltG Co1T.aGA [0, 1, 0, 0, 0, 0] * v ∧ orderOf v = 7 ∧ c * v = Co1S.sE * c) ∧
    (∃ v c : ↥GA, v * Co1T.root 2 = Co1T.root 2 * v ∧ orderOf v = 7 ∧ c * v = Co1S.tE * c) := by
  have hr := ch214033r
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨e0, e1⟩, e2⟩ := hr
  have r0 := rep_elt [1, 0, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true e0)
  have r1 := rep_elt [0, 1, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true e1)
  have r2 := rep_elt [1, 1, 0, 0, 0, 0] (Nat.eq_of_beq_eq_true e2)
  have rS : MRep (unpack 24 24 (CertificateChecks.KernelCo1SevenK.D.M 66)) ((Co1S.sE : ↥GA) : GL24) := by
    have e := Certificates.certificate13697.2.2.2.2.2
    rwa [CertificateChecks.KernelCo1SevenK.rowAt_lt (by decide +kernel)] at e
  have rT : MRep (unpack 24 24 (CertificateChecks.KernelCo1SevenK.D.M 67)) ((Co1S.tE : ↥GA) : GL24) := by
    have e := Certificates.certificate13698.2.2.2
    rwa [CertificateChecks.KernelCo1SevenK.rowAt_lt (by decide +kernel)] at e
  have hk := ch36909kn
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨n0, n1⟩, n4⟩ := hk
  obtain ⟨-, c3⟩ := conj_facts r1 (rep_root (j := 1) (by norm_num)) ch36909c3
  obtain ⟨-, c6⟩ := conj_facts r2 (rep_root (j := 0) (by norm_num)) ch36909c6
  obtain ⟨-, m0, o0⟩ := elt_facts (by norm_num) r0 ch36909k0 n0
  obtain ⟨q1, m1, o1⟩ := elt_facts (by norm_num) r1 ch36909k1 n1
  obtain ⟨-, c2⟩ := conj_facts q1 rS ch36909c2
  obtain ⟨q4, m4, o4⟩ := elt_facts (by norm_num) (rep_root (j := 2) (by norm_num)) ch36909k4 n4
  obtain ⟨-, c5⟩ := conj_facts q4 rT ch36909c5
  exact ⟨⟨_, c3⟩, ⟨_, c6⟩, ⟨_, m0, o0⟩, ⟨_, _, m1, o1, c2⟩, ⟨_, _, m4, o4, c5⟩⟩

end Facts

end CertificateChecks.KernelCo1Pump

end

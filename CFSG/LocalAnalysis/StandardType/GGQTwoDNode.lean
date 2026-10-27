module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoDReflLin
import CFSG.Quasithin.Background.B1MoreTwelveB
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnOrd6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LargeExtraspecial.OfFStar
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
import CFSG.LocalAnalysis.SectionRank.QTK.Exc
import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Milestones.ASVolI.A2OddAut
import CFSG.Milestones.ASVolI.F48.Core
import CFSG.Models.Transport
import CFSG.Quasithin.Background.B1MoreTen
import CFSG.Quasithin.Background.B1MoreTwelveA
import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
import CFSG.Quasithin.Vol2.KGFactC31RuRef
import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.OddKernel.CompleteRankComparison
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.RankThree.PartOne.KF.ClsPSL
import CFSG.RankThree.PartOne.KF.SU5Model
import CFSG.RankThree.PartOne.KF.SymCtxMatrix
import CFSG.RankThree.PartOne.KF.ToralQuot
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.RankThree.PartOne.S11c.Sec66PSL
import CFSG.RankThree.PartOne.S11c.Sec66Sp
import CFSG.RankThree.PartOne.S11c.SuFiveD
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.HeldB.Common
import CFSG.Sporadic.Recognition.JankoWongPSLNine
import CFSG.Sporadic.Schreier.RuPair
import CFSG.Sporadic.Schreier.RuSylow
import Certificates.Certificate7233Base

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

variable {G : Type} [Group G]

theorem ggOTwoPrime_exists_ne_comm_of_card_six {Y : Subgroup G}
    (h6 : Nat.card (ggOTwoPrime Y) = 6) :
    ∃ a ∈ ggOTwoPrime Y, ∃ b ∈ ggOTwoPrime Y, a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a ∈ ggOTwoPrime Y, ∀ b ∈ ggOTwoPrime Y, a * b = b * a := by
    intro a ha b hb
    by_contra hne
    exact hcon ⟨a, ha, b, hb, hne⟩
  let O := ggOTwoPrime Y
  have hOcard : Nat.card O = 6 := h6
  have hgen_sq : ∀ y ∈ Y, (∃ k : ℕ, y ^ (2 ^ k) = 1) → y ^ 2 = 1 := by
    intro y hyY ⟨k, hk⟩
    have hyO : y ∈ O := Subgroup.subset_closure ⟨hyY, k, hk⟩
    have hdvd1 : orderOf y ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    have hdvd2 : orderOf y ∣ 6 := by
      simpa [Subgroup.orderOf_mk, hOcard] using orderOf_dvd_natCard (⟨y, hyO⟩ : O)
    have hdvd : orderOf y ∣ 2 := by
      have hd : orderOf y ∣ Nat.gcd (2 ^ k) 6 := Nat.dvd_gcd hdvd1 hdvd2
      have hgd : Nat.gcd (2 ^ k) 6 ∣ 2 := by
        have hc : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
        have hmul : Nat.gcd (2 ^ k) (2 * 3) =
            Nat.gcd (2 ^ k) 2 * Nat.gcd (2 ^ k) 3 := Nat.Coprime.gcd_mul _ (by norm_num)
        rw [show (6 : ℕ) = 2 * 3 from rfl, hmul, hc]
        simpa using Nat.gcd_dvd_right (2 ^ k) 2
      exact hd.trans hgd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hsq : ∀ x : O, x ^ 2 = 1 := by
    intro x
    let s : Set G := {y | y ∈ Y ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1}
    have hmain : ∀ (z : G) (hz : z ∈ Subgroup.closure s),
        (⟨z, hz⟩ : O) ^ 2 = 1 := by
      intro z hz
      refine Subgroup.closure_induction
        (p := fun z hz => (⟨z, hz⟩ : O) ^ 2 = 1) ?_ ?_ ?_ ?_ hz
      · intro w hw
        exact Subtype.ext (hgen_sq w hw.1 hw.2)
      · exact Subtype.ext (by simp)
      · intro u v hu hv hcu hcv
        have hcommO : (⟨u, hu⟩ : O) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨u, hu⟩ :=
          Subtype.ext (hcomm u hu v hv)
        have hmul : (⟨u * v, Subgroup.mul_mem _ hu hv⟩ : O) =
            ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
        rw [hmul]
        calc ((⟨u, hu⟩ : O) * ⟨v, hv⟩) ^ 2
            = ⟨u, hu⟩ * ⟨v, hv⟩ * (⟨u, hu⟩ * ⟨v, hv⟩) := by rw [sq]
          _ = ⟨u, hu⟩ * (⟨v, hv⟩ * ⟨u, hu⟩) * ⟨v, hv⟩ := by group
          _ = ⟨u, hu⟩ * (⟨u, hu⟩ * ⟨v, hv⟩) * ⟨v, hv⟩ := by rw [hcommO]
          _ = (⟨u, hu⟩ * ⟨u, hu⟩) * (⟨v, hv⟩ * ⟨v, hv⟩) := by group
          _ = 1 := by rw [← sq, ← sq, hcu, hcv, mul_one]
      · intro u hu hcu
        apply Subtype.ext
        show (u⁻¹) ^ 2 = 1
        have hu' : ((⟨u, hu⟩ : O) : G) ^ 2 = 1 := congrArg Subtype.val hcu
        calc (u⁻¹) ^ 2 = ((u : G) ^ 2)⁻¹ := by group
          _ = 1 := by rw [hu', inv_one]
    simpa using hmain (x : G) x.2
  obtain ⟨x, hxord⟩ :=
    @exists_prime_orderOf_dvd_card' O _ (Nat.finite_of_card_ne_zero (by rw [hOcard]; norm_num))
      3 Nat.fact_prime_three (by rw [hOcard]; norm_num)
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (hsq x)
  rw [hxord] at hdvd
  norm_num at hdvd
private lemma eq_or_eq_inv_of_mem_zpowers_of_orderOf_three {K : Type*} [Group K] {y z : K}
    (hy : orderOf y = 3) (hz : z ∈ Subgroup.zpowers y) (hz1 : z ≠ 1) :
    z = y ∨ z = y⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hk3 : z = y ^ (k % (3 : ℤ)) := by
    rw [← hk, ← zpow_mod_orderOf, hy]; norm_num
  have hb1 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hb2 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [hk3, h0] at hz1
    exact hz1 (zpow_zero y)
  · left
    rw [hk3, h1]
    simp
  · right
    rw [hk3, h2]
    have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    have hy2 : y ^ 2 = y⁻¹ := by
      have h : y ^ 2 * y = 1 := by simpa [pow_succ] using hy3
      calc y ^ 2 = y ^ 2 * y * y⁻¹ := by group
        _ = 1 * y⁻¹ := by rw [h]
        _ = y⁻¹ := one_mul _
    simpa using hy2
private lemma conj_eq_self_of_pow_three {K : Type*} [Group K] {x y : K}
    (hx : x ^ 3 = 1) (hy : orderOf y = 3)
    (h : x * y * x⁻¹ ∈ Subgroup.zpowers y) : x * y * x⁻¹ = y := by
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy
    norm_num at hy
  have hz1 : x * y * x⁻¹ ≠ 1 := by
    intro h1
    have h2 : y = 1 := by
      have := congrArg (fun t : K => x⁻¹ * t * x) h1
      simpa [mul_assoc] using this
    exact hy1 h2
  rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_three hy h hz1 with h' | h'
  · exact h'
  · exfalso
    have h2 : x * (x * y * x⁻¹) * x⁻¹ = y := by
      rw [h']
      calc x * y⁻¹ * x⁻¹ = (x * y * x⁻¹)⁻¹ := by group
        _ = y := by rw [h']; simp
    have h3 : x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = y⁻¹ := by
      rw [h2]
      exact h'
    have h4 : x ^ 3 * y * (x ^ 3)⁻¹ = y⁻¹ := by
      calc x ^ 3 * y * (x ^ 3)⁻¹
          = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by
            rw [pow_three]
            group
        _ = y⁻¹ := h3
    have hy_eq : y = y⁻¹ := by simpa [hx] using h4
    have hy2 : y ^ 2 = 1 := by
      have hyy : y * y = 1 := by
        nth_rewrite 1 [hy_eq]
        exact inv_mul_cancel y
      simpa [sq] using hyy
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
    rw [hy] at hdvd
    norm_num at hdvd
theorem exists_root_ggRankOne [Finite G] {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {r : MulAut ↥Bs} (hrI : r ∈ ggInduced ⊤ Bs) (h6 : Nat.card (ggRankOne Bs r) = 6) :
    ∃ c : ↥Bs, c ≠ 1 ∧ (c : G) ∈ ggRankOne Bs r ∧ r c = c⁻¹ ∧
      ∀ g ∈ ggRankOne Bs r, g ^ 3 = 1 → g ∈ Subgroup.zpowers (c : G) := by
  classical
  let H : Subgroup G := ggHyperplane Bs r
  let S : Subgroup G := ggRankOne Bs r
  have h6S : Nat.card S = 6 := by simpa [S] using h6
  have hHle : H ≤ Bs := Subgroup.map_subtype_le _
  have hSle : S ≤ Subgroup.centralizer (H : Set G) :=
    ggOTwoPrime_le (Subgroup.centralizer (H : Set G))
  have hcommBs : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hcommG : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hcommBs ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsCent : Bs ≤ Subgroup.centralizer (H : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hcommG b hb h (hHle hh)).symm
  have hcardO : Nat.card (ggOTwoPrime (Subgroup.centralizer (H : Set G))) = 6 := by
    simpa [S, ggRankOne] using h6S
  have hncS : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ :=
      ggOTwoPrime_exists_ne_comm_of_card_six (Y := Subgroup.centralizer (H : Set G)) hcardO
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by simpa using congrArg Subtype.val h)⟩
  have hncS' : ¬ ∀ a b : ↥S, a * b = b * a := by
    obtain ⟨a, b, hab⟩ := hncS
    exact fun h => hab (h a b)
  have hcenterS : Subgroup.center ↥S = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.center_eq_bot_of_card_six h6S hncS'
  obtain ⟨P, hPnorm, hP3, hPy⟩ :=
    CFSG.Quasithin.B1Red.exists_normal_card_three_of_card_six (Y := ↥S) h6S
  have hPbot : (⊥ : Subgroup ↥S) < P := by
    rw [lt_iff_le_and_ne]
    refine ⟨bot_le, ?_⟩
    intro h
    rw [← h, Subgroup.card_bot] at hP3
    norm_num at hP3
  obtain ⟨x, hxP, hxbot⟩ := SetLike.exists_of_lt hPbot
  have hx1 : x ≠ 1 := by simpa using hxbot
  have hxcube : x ^ 3 = 1 := (hPy x).1 hxP
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      have h := orderOf_dvd_natCard (⟨x, hxP⟩ : ↥P)
      rwa [Subgroup.orderOf_mk, hP3] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzP : Subgroup.zpowers x = P := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) ?_
    rw [hP3, Nat.card_zpowers, hxord]
  have hPz : P = Subgroup.zpowers x := hzP.symm
  have hordxG : orderOf (x : G) = 3 := by
    rw [Subgroup.orderOf_coe, hxord]
  have hxcubeG : (x : G) ^ 3 = 1 := congrArg (fun y : ↥S => (y : G)) hxcube
  have hbcomm : ∀ b ∈ Bs, b * (x : G) = (x : G) * b := by
    intro b hb
    have hbCent : b ∈ Subgroup.centralizer (H : Set G) := hBsCent hb
    have hbNormC : b ∈ Subgroup.normalizer ((Subgroup.centralizer (H : Set G)) : Set G) :=
      CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer H
        (Subgroup.centralizer_le_normalizer (H : Set G) hbCent)
    have hbNormS : b ∈ Subgroup.normalizer (S : Set G) :=
      ggMem_normalizer_oTwoPrime hbNormC
    have hconjS : b * (x : G) * b⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hbNormS (x : G)).mp x.2
    let d : ↥S := ⟨b * (x : G) * b⁻¹, hconjS⟩
    have hdcube : d ^ 3 = 1 := by
      apply Subtype.ext
      show (b * (x : G) * b⁻¹) ^ 3 = 1
      rw [conj_pow, hxcubeG, mul_one, mul_inv_cancel]
    have hdP : d ∈ P := (hPy d).2 hdcube
    have hdzpS : d ∈ Subgroup.zpowers x := by rw [← hPz]; exact hdP
    have hdzp : b * (x : G) * b⁻¹ ∈ Subgroup.zpowers (x : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdzpS
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
        have := congrArg (fun y : ↥S => (y : G)) hk
        simpa using this⟩
    have hdzp1 : b * (x : G) * b⁻¹ ≠ 1 := by
      intro h1
      have hx1G : (x : G) = 1 := by
        have := congrArg (fun t : G => b⁻¹ * t * b) h1
        simpa [mul_assoc] using this
      exact hx1 (Subtype.ext hx1G)
    have hb3 : b ^ 3 = 1 := hBs.2 b hb
    have hfix := conj_eq_self_of_pow_three hb3 hordxG hdzp
    have hfin : b * (x : G) = (x : G) * b := by
      have := congrArg (fun t : G => t * b) hfix
      simpa [mul_assoc] using this
    exact hfin
  have hxCentBs : (x : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hbcomm
  have hxBs : (x : G) ∈ Bs := by
    refine hSC (x : G) hxCentBs ?_
    have := congrArg (fun y : ↥S => (y : G)) hxcube
    simpa using this
  let c : ↥Bs := ⟨(x : G), hxBs⟩
  have hr_range : r ∈ Bs.normalizerMonoidHom.range := mem_ggInduced_top_iff.mp hrI
  obtain ⟨n, hn⟩ := hr_range
  have hnc : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = (n : G) * (b : G) * (n : G)⁻¹ := by
    intro b
    have h := Subgroup.normalizerMonoidHom_apply_apply_coe Bs n b
    rwa [hn] at h
  have hnCentH : (n : G) ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨b, hb, rfl⟩ := hh
    have hb' : r b = b := by simpa using hb
    have hbval : Bs.subtype b = (n : G) * Bs.subtype b * (n : G)⁻¹ := by
      have h := hnc b
      rwa [hb'] at h
    calc Bs.subtype b * (n : G)
        = ((n : G) * Bs.subtype b * (n : G)⁻¹) * (n : G) := by
          nth_rewrite 1 [hbval]
          rfl
      _ = (n : G) * Bs.subtype b := by group
  have hnNormS : (n : G) ∈ Subgroup.normalizer (S : Set G) :=
    ggMem_normalizer_oTwoPrime (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer H
      (Subgroup.centralizer_le_normalizer (H : Set G) hnCentH))
  have hnconjS : (n : G) * (x : G) * (n : G)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hnNormS (x : G)).mp x.2
  let dn : ↥S := ⟨(n : G) * (x : G) * (n : G)⁻¹, hnconjS⟩
  have hdncube : dn ^ 3 = 1 := by
    apply Subtype.ext
    show ((n : G) * (x : G) * (n : G)⁻¹) ^ 3 = 1
    rw [conj_pow, hxcubeG, mul_one, mul_inv_cancel]
  have hdnP : dn ∈ P := (hPy dn).2 hdncube
  have hdnzpS : dn ∈ Subgroup.zpowers x := by rw [← hPz]; exact hdnP
  have hdnzp : (n : G) * (x : G) * (n : G)⁻¹ ∈ Subgroup.zpowers (x : G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdnzpS
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      have := congrArg (fun y : ↥S => (y : G)) hk
      simpa using this⟩
  have hdnzp1 : (n : G) * (x : G) * (n : G)⁻¹ ≠ 1 := by
    intro h1
    have hx1G : (x : G) = 1 := by
      have := congrArg (fun t : G => (n : G)⁻¹ * t * (n : G)) h1
      simpa [mul_assoc] using this
    exact hx1 (Subtype.ext hx1G)
  have hndich := eq_or_eq_inv_of_mem_zpowers_of_orderOf_three hordxG hdnzp hdnzp1
  have hrc : r c = c⁻¹ := by
    rcases hndich with hfix | hinv
    · exfalso
      have hrcfix : r c = c := by
        apply Subtype.ext
        show ((r c : ↥Bs) : G) = (c : G)
        rw [hnc c]
        show (n : G) * (c : G) * (n : G)⁻¹ = (c : G)
        simpa [c] using hfix
      have hcH : (c : G) ∈ H := by
        refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
        simpa using hrcfix
      have hxCenter : x ∈ Subgroup.center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hSle y.2) (x : G) hcH)).symm
      rw [hcenterS, Subgroup.mem_bot] at hxCenter
      exact hx1 hxCenter
    · apply Subtype.ext
      show ((r c : ↥Bs) : G) = ((c⁻¹ : ↥Bs) : G)
      rw [hnc c]
      simpa [c] using hinv
  refine ⟨c, ?cne, ?cmem, hrc, ?cgen⟩
  · intro h
    exact hx1 (Subtype.ext (by simpa [c] using congrArg (fun y : ↥Bs => (y : G)) h))
  · simp [c]
  · intro g hgS hg3
    have hgP : (⟨g, hgS⟩ : ↥S) ∈ P := (hPy ⟨g, hgS⟩).2 (by
      apply Subtype.ext
      simpa using hg3)
    have hgzpS : (⟨g, hgS⟩ : ↥S) ∈ Subgroup.zpowers x := by rw [← hPz]; exact hgP
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgzpS
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      have := congrArg (fun y : ↥S => (y : G)) hk
      simpa [c] using this⟩
private lemma exists_mul_zpow_of_mem_sup {K : Type*} [Group K] {H : Subgroup K} {c x : K}
    (hcomm : ∀ a b : K, a * b = b * a) (hx : x ∈ H ⊔ Subgroup.zpowers c) :
    ∃ h₀ ∈ H, ∃ j : ℤ, h₀ * c ^ j = x := by
  have hx' : x ∈ Subgroup.closure ((H : Set K) ∪ (Subgroup.zpowers c : Set K)) := by
    rw [← Subgroup.sup_eq_closure]
    exact hx
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ h₀ ∈ H, ∃ j : ℤ, h₀ * c ^ j = x) ?_ ?_ ?_ ?_ hx'
  · rintro y (hy | hy)
    · exact ⟨y, hy, 0, by simp⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨1, Subgroup.one_mem H, j, by simp⟩
  · exact ⟨1, Subgroup.one_mem H, 0, by simp⟩
  · rintro a b _ _ ⟨h1, hh1, i, rfl⟩ ⟨h2, hh2, j, rfl⟩
    refine ⟨h1 * h2, Subgroup.mul_mem H hh1 hh2, i + j, ?_⟩
    calc (h1 * h2) * c ^ (i + j)
        = (h1 * h2) * (c ^ i * c ^ j) := by rw [zpow_add]
      _ = h1 * (h2 * c ^ i) * c ^ j := by group
      _ = h1 * (c ^ i * h2) * c ^ j := by rw [hcomm h2 (c ^ i)]
      _ = (h1 * c ^ i) * (h2 * c ^ j) := by group
  · rintro a _ ⟨h1, hh1, i, rfl⟩
    refine ⟨h1⁻¹, Subgroup.inv_mem H hh1, -i, ?_⟩
    calc h1⁻¹ * c ^ (-i) = c ^ (-i) * h1⁻¹ := hcomm _ _
      _ = (c ^ i)⁻¹ * h1⁻¹ := by rw [← zpow_neg]
      _ = (h1 * c ^ i)⁻¹ := by rw [mul_inv_rev]
theorem ggRankOne_le_normalizer_ggHyperplane [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {r r' : MulAut ↥Bs} (hr : GGIsReflection 3 r) (hrI : r ∈ ggInduced ⊤ Bs)
    (h6 : Nat.card (ggRankOne Bs r) = 6) (hr' : GGIsReflection 3 r')
    (hcomm : r * r' = r' * r) (hne : r ≠ r') :
    ggRankOne Bs r ≤ Subgroup.normalizer (ggHyperplane Bs r' : Set G) := by
  classical
  let H : Subgroup G := ggHyperplane Bs r
  let H' : Subgroup G := ggHyperplane Bs r'
  let S : Subgroup G := ggRankOne Bs r
  let Hrel : Subgroup ↥Bs :=
    MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs)
  have hSle : S ≤ Subgroup.centralizer (H : Set G) :=
    ggOTwoPrime_le (Subgroup.centralizer (H : Set G))
  obtain ⟨c, hcne, hcS, hrc, hcgen⟩ := exists_root_ggRankOne hBs hSC hrI h6
  have hccubeBs : c ^ 3 = 1 := Subtype.ext (hBs.2 (c : G) c.2)
  have hccube : (c : G) ^ 3 = 1 := congrArg (fun y : ↥Bs => (y : G)) hccubeBs
  have hrc' : r' c = c :=
    apply_eq_self_of_commute_of_isReflection (p := 3) (Bs := Bs) (r := r') (r' := r)
      (by decide : 3 ≠ 2) hBs hr' hr hcomm.symm hne.symm hrc
  have hcH' : (c : G) ∈ H' := by
    refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
    exact hrc'
  have hHrelcard : Nat.card ↥Hrel * 3 = Nat.card ↥Bs := hr.2
  have hHrelindex : Hrel.index = 3 := by
    have hmul := Subgroup.card_mul_index Hrel
    exact Nat.mul_left_cancel Nat.card_pos (hmul.trans hHrelcard.symm)
  have hcHrel : c ∉ Hrel := by
    intro hc
    have hceq : r c = c := hc
    have hcinv : c = c⁻¹ := hceq.symm.trans hrc
    have hc2 : c * c = 1 := by
      calc c * c = c⁻¹ * c := by
              nth_rewrite 1 [hcinv]
              rfl
        _ = 1 := inv_mul_cancel c
    have hc1 : c = 1 := by
      rw [pow_three, hc2] at hccubeBs
      simpa using hccubeBs
    exact hcne hc1
  let K : Subgroup ↥Bs := Hrel ⊔ Subgroup.zpowers c
  have hKle : Hrel ≤ K := le_sup_left
  have hcK : c ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hKne : Hrel ≠ K := by
    intro h
    apply hcHrel
    rw [← h] at hcK
    exact hcK
  have hrel_dvd : Hrel.relIndex K ∣ Hrel.index := by
    exact Dvd.intro _ (Subgroup.relIndex_mul_index hKle)
  have hrel_ne1 : Hrel.relIndex K ≠ 1 := by
    intro h1
    have hKH : K ≤ Hrel := Subgroup.relIndex_eq_one.mp h1
    exact hKne (le_antisymm hKle hKH)
  have hrel3 : Hrel.relIndex K = 3 := by
    have hdvd : Hrel.relIndex K ∣ 3 := by rwa [hHrelindex] at hrel_dvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd h hrel_ne1
    · exact h
  have hKindex : K.index = 1 := by
    have hmul := Subgroup.relIndex_mul_index hKle
    rw [hrel3, hHrelindex] at hmul
    omega
  have hKtop : K = ⊤ := Subgroup.index_eq_one.mp hKindex
  have hcommBs : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hconj_mem : ∀ {x h : G}, x ∈ S → h ∈ H' → x * h * x⁻¹ ∈ H' := by
    intro x h hxS hhH'
    obtain ⟨b, hb, hbval⟩ := Subgroup.mem_map.mp hhH'
    have hmemSup : b ∈ Hrel ⊔ Subgroup.zpowers c := by
      have hbK : b ∈ K := by
        rw [hKtop]
        exact Subgroup.mem_top b
      simpa [K] using hbK
    obtain ⟨h0, hh0, j, hbdeceq⟩ :=
      exists_mul_zpow_of_mem_sup hcommBs hmemSup
    have hbdec : b = h0 * c ^ j := hbdeceq.symm
    have hbdecG : Bs.subtype b = (h0 : G) * (c : G) ^ j := by
      have := congrArg (fun y : ↥Bs => (y : G)) hbdec
      simpa using this
    have hh0H : (h0 : G) ∈ H := Subgroup.mem_map.mpr ⟨h0, hh0, rfl⟩
    have hczH' : (c : G) ^ j ∈ H' := Subgroup.zpow_mem H' hcH' j
    have hh0H' : (h0 : G) ∈ H' := by
      have hh0eq : (h0 : G) = h * ((c : G) ^ j)⁻¹ := by
        rw [← hbval, hbdecG]
        group
      rw [hh0eq]
      exact Subgroup.mul_mem H' hhH' (Subgroup.inv_mem H' hczH')
    have hxh0 : x * (h0 : G) * x⁻¹ = (h0 : G) := by
      have hxCent : x ∈ Subgroup.centralizer (H : Set G) := hSle hxS
      have hcommH := (Subgroup.mem_centralizer_iff.mp hxCent) (h0 : G) hh0H
      rw [← hcommH]
      group
    have hxcS : x * (c : G) * x⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.le_normalizer (H := S)) hxS) (c : G)).mp hcS
    have hxccube : (x * (c : G) * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hccube, mul_one, mul_inv_cancel]
    have hxc_zp : x * (c : G) * x⁻¹ ∈ Subgroup.zpowers (c : G) :=
      hcgen (x * (c : G) * x⁻¹) hxcS hxccube
    have hxcH' : x * (c : G) * x⁻¹ ∈ H' :=
      Subgroup.zpowers_le.mpr hcH' hxc_zp
    have hfin : x * h * x⁻¹ = (h0 : G) * (x * (c : G) * x⁻¹) ^ j := by
      rw [← hbval, hbdecG]
      calc x * ((h0 : G) * (c : G) ^ j) * x⁻¹
          = (x * (h0 : G) * x⁻¹) * (x * (c : G) ^ j * x⁻¹) := by group
        _ = (h0 : G) * (x * (c : G) * x⁻¹) ^ j := by rw [hxh0, ← conj_zpow]
    rw [hfin]
    exact Subgroup.mul_mem H' hh0H' (Subgroup.zpow_mem H' hxcH' j)
  intro x hxS
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj_mem hxS hh
  · intro hh
    have h2 := hconj_mem (x := x⁻¹) (h := x * h * x⁻¹) (Subgroup.inv_mem S hxS) hh
    have h3 : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [h3] at h2
end CFSG.StandardType.QTwo
end

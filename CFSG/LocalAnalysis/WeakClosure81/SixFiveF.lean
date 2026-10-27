module

public import CFSG.RankThree.GF2n.QuotPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.SixFourSz
import CFSG.CGT.T75N.BenderCenter
import CFSG.CGT.T75N.UnitaryTwoGen
import CFSG.Quasithin.Background.I62Main
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.Blueprint.SourceExceptionalModels
public import CFSG.CGT.Timmesfeld75.Config214
public import CFSG.CGT.Timmesfeld75.Sec25
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.CGT.Timmesfeld75.ZStarSmall
public import CFSG.CharacterTheory.Semidihedral.CharacteristicSL2Layer
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Ree.Duality
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Walter.Defs
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate43
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Open.SplitBNPair
import CFSG.Permutation.BurnsideSchur
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B2FactorizationResidual
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.H13.StatementsL1
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n (QuotPair pairConj)
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {T T₁ : Subgroup X}

private theorem s65_SixFiveF_twoRank_dihedral {m : ℕ} [NeZero m] (hm : Odd m) :
    twoRank (DihedralGroup m) = 1 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨Subgroup.zpowers (DihedralGroup.sr 0), le_top,
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : (DihedralGroup.sr (0 : ZMod m)) ^ 2 = 1 := by
      rw [sq]; exact DihedralGroup.sr_mul_self 0
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  · rw [Nat.card_zpowers, DihedralGroup.orderOf_sr, pow_one]
  · rintro k ⟨E, -, -, hEcard⟩
    have hdvd : 2 ^ k ∣ 2 * m := by
      rw [← hEcard, ← DihedralGroup.nat_card]
      exact Subgroup.card_subgroup_dvd_card E
    by_contra hk
    push Not at hk
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have : 4 ∣ 2 * m := (by simpa using h4 : 4 ∣ 2 ^ k).trans hdvd
    have h2 : 2 ∣ m := by omega
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

private theorem s65_SixFiveF_center_eq_bot_of_isSimple (P : QuotPair T T₁)
    (hsimple : IsSimpleGroup X) :
    Subgroup.center X = ⊥ := by
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcenter : (⊤ : Subgroup X) ≤ Subgroup.center X := h.ge
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (hcenter (Subgroup.mem_top a)) b).symm
    obtain ⟨⟨u, hu⟩, hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp P.ne_bot
    obtain ⟨⟨v, hv⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp P.ne_bot₁
    have hu1 : u ≠ 1 := fun h' => hu1' (Subtype.ext h')
    have hv1 : v ≠ 1 := fun h' => hv1' (Subtype.ext h')
    exact P.ne (P.closed T QuotPair.mem_pairConj_left T₁ QuotPair.mem_pairConj_right
      u hu hu1 v hv hv1 (hcomm u v))

private theorem s65_SixFiveF_center_eq_bot_of_mulEquiv_dihedral {m : ℕ} (hm : Odd m) (hm1 : m ≠ 1)
    (e : X ≃* DihedralGroup m) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e z ∈ Subgroup.center (DihedralGroup m) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subgroup.mem_center_iff.mp hz x)
  rw [DihedralGroup.center_eq_bot_of_odd_ne_one hm hm1, Subgroup.mem_bot] at hz'
  exact e.injective (by rw [hz', map_one])

private theorem s65_SixFiveF_isL2Pair (P : QuotPair T T₁) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card T = 2 ^ f) (e : X ≃* PSL(2, GaloisField 2 f)) :
    IsL2Pair X T (2 ^ f) := by
  have hf0 : f ≠ 0 := by omega
  have hQcard : Nat.card X = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 f)).toEquiv,
      CFSG.CGT.Timmesfeld75.card_sl2, GaloisField.card 2 f hf0]
  have hAindex : T.index = (2 ^ f) ^ 2 - 1 := by
    have h1 := Subgroup.card_mul_index T
    rw [hcard, hQcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ f = 2 * j := by
    refine ⟨2 ^ (f - 1), ?_⟩
    calc 2 ^ f = 2 ^ (1 + (f - 1)) := by congr 1; omega
      _ = 2 ^ 1 * 2 ^ (f - 1) := by rw [pow_add]
      _ = 2 * 2 ^ (f - 1) := by norm_num
  have hj1 : 1 ≤ j := by
    have h2f : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hj2 : 1 ≤ j ^ 2 := by nlinarith [sq_nonneg j]
  have hidx : ¬ 2 ∣ T.index := by
    have hTodd : T.index = 2 * (2 * j ^ 2 - 1) + 1 := by
      rw [hAindex, hj]
      have h1 : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
      have h2 : 2 * (2 * j ^ 2 - 1) + 1 = 4 * j ^ 2 - 1 := by omega
      omega
    rw [hTodd]
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    omega
  exact IsL2Pair.of_psl_isPGroup hf0 ⟨e⟩ P.elem.isPGroup hidx

private theorem s65_SixFiveF_sup_zpowers_of_sup_conj {x : X} (htop : T ⊔ conjSubgroup x T = ⊤) :
    T ⊔ Subgroup.zpowers x = ⊤ := by
  have hle : conjSubgroup x T ≤ T ⊔ Subgroup.zpowers x := by
    intro y hy
    rw [mem_conjSubgroup] at hy
    have hy' : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
    rw [hy']
    exact (T ⊔ Subgroup.zpowers x).mul_mem
      ((T ⊔ Subgroup.zpowers x).mul_mem
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
        (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)))
  refine le_antisymm le_top ?_
  rw [← htop]
  exact sup_le le_sup_left hle

private theorem s65_SixFiveF_conjSubgroup_inv_smul (S : Sylow 2 X) (g : X) :
    CFSG.Quasithin.conjSubgroup (S : Subgroup X) g⁻¹ = ((g • S : Sylow 2 X) : Subgroup X) := by
  unfold CFSG.Quasithin.conjSubgroup
  rw [inv_inv]
  rfl

section Certified

theorem _root_.CFSG.RankThree.GF2n.QuotPair.quotShape (P : QuotPair T T₁) :
    ((∃ r : ℕ, IsL2 X r) ∨ (∃ r : ℕ, IsSz X r) ∨
      (∃ m : ℕ, Odd m ∧ Nonempty (X ≃* DihedralGroup m))) ∧
    Nat.card T = 2 ^ twoRank X := by
  obtain ⟨-, hmod⟩ := P.models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  rcases hmod with ⟨f, hf, hcard, ⟨e⟩⟩ | ⟨a, ha, hcard, ⟨e⟩⟩ | ⟨m, hm, hm3, hcard, ⟨e⟩⟩
  · have hL2 : IsL2 X f :=
      Or.inl ⟨by decide, CFSG.Quasithin.I62.isPSL_two_two_of_mulEquiv hf e⟩
    exact ⟨Or.inl ⟨f, hL2⟩, by
      rw [hcard, CFSG.GH74.twoRank_eq_of_lieModel_PSL_two_two hL2]⟩
  · have hSz : IsSz X (2 * a + 1) :=
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, CFSG.Quasithin.I62.isSz_of_mulEquiv ha e⟩))
    exact ⟨Or.inr (Or.inl ⟨2 * a + 1, hSz⟩), by
      rw [hcard, twoRank_eq_of_mulEquiv_sz ha e]⟩
  · haveI : NeZero m := ⟨by omega⟩
    exact ⟨Or.inr (Or.inr ⟨m, hm, ⟨e⟩⟩), by
      rw [hcard, CFSG.GH74.twoRank_eq_of_mulEquiv e, s65_SixFiveF_twoRank_dihedral hm]
      norm_num⟩

theorem _root_.CFSG.RankThree.GF2n.QuotPair.center_eq_bot (P : QuotPair T T₁) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, hmod⟩ := P.models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  rcases hmod with ⟨f, hf, -, ⟨e⟩⟩ | ⟨a, ha, -, ⟨e⟩⟩ | ⟨m, hm, hm3, -, ⟨e⟩⟩
  · have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [hFcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    haveI : IsSimpleGroup (PSL(2, GaloisField 2 f)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact s65_SixFiveF_center_eq_bot_of_isSimple P e.isSimpleGroup
  · haveI : IsSimpleGroup (Sz a) :=
      CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup ha
    exact s65_SixFiveF_center_eq_bot_of_isSimple P e.isSimpleGroup
  · exact s65_SixFiveF_center_eq_bot_of_mulEquiv_dihedral hm (by omega) e

theorem _root_.CFSG.RankThree.GF2n.QuotPair.sup_zpowers_eq_top (P : QuotPair T T₁) {x : X}
    (hx : x ∈ T₁) (hx1 : x ≠ 1) :
    T ⊔ Subgroup.zpowers x = ⊤ := by
  have hxN : x ∉ Subgroup.normalizer (T : Set X) := fun hxN =>
    hx1 (P.eq_one_of_mem_normalizer hx hxN)
  have hconj_ne : conjSubgroup x T ≠ T := fun heq =>
    hxN (mem_normalizer_iff_conjSubgroup_eq.mpr heq)
  obtain ⟨-, hmod⟩ := P.models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  rcases hmod with ⟨f, hf, hcard, ⟨e⟩⟩ | ⟨a, ha, hcard, ⟨e⟩⟩ | ⟨m, hm, hm3, hcard, ⟨e⟩⟩
  · have hpair := s65_SixFiveF_isL2Pair P hf hcard e
    have hne : conjSubgroup (1 : X) T ≠ conjSubgroup x T := by
      rw [conjSubgroup_one]; exact hconj_ne.symm
    have htop := hpair.sup_conj_eq_top hne
    rw [conjSubgroup_one] at htop
    exact s65_SixFiveF_sup_zpowers_of_sup_conj htop
  · obtain ⟨S, hTeq⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e P.elem hcard
    have hNA : Subgroup.normalizer (T : Set X) =
        Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [hTeq]
      exact normalizer_inf_centralizer_eq_of_mulEquiv_sz ha e S
    have hxN' : x ∉ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [← hNA]; exact hxN
    have hSne : S ≠ x • S := fun heq =>
      hxN' (Sylow.smul_eq_iff_mem_normalizer.mp heq.symm)
    have hconj : conjSubgroup x T = ((x • S : Sylow 2 X) : Subgroup X) ⊓
        Subgroup.centralizer (((x • S : Sylow 2 X) : Subgroup X) : Set X) := by
      rw [hTeq, timmesfeld_conjSubgroup_eq, CFSG.Quasithin.E3.conjSubgroup_inf,
        CFSG.Quasithin.E3.conjSubgroup_centralizer,
        s65_SixFiveF_conjSubgroup_inv_smul S x]
    have htop : T ⊔ conjSubgroup x T = ⊤ := by
      rw [hconj, hTeq]
      exact inf_centralizer_sup_inf_centralizer_eq_top ha e hSne
    exact s65_SixFiveF_sup_zpowers_of_sup_conj htop
  · obtain ⟨y, hy⟩ := P.exists_conj_eq
    have hcard₁ : Nat.card T₁ = 2 := by
      rw [hy, card_conjSubgroup]; exact hcard
    have hx2 : x * x = 1 := P.sq_eq_one QuotPair.mem_pairConj_right hx
    have hxord : orderOf x = 2 := orderOf_eq_prime (by simpa [sq] using hx2) hx1
    have hzx : Nat.card (Subgroup.zpowers x) = 2 := by
      rw [Nat.card_zpowers, hxord]
    have hzeq : Subgroup.zpowers x = T₁ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) (by omega)
    rw [hzeq]; exact P.sup

theorem _root_.CFSG.RankThree.GF2n.QuotPair.exists_swap (P : QuotPair T T₁) :
    ∃ l : X, conjSubgroup l T = T₁ ∧ conjSubgroup l T₁ = T := by
  obtain ⟨x, hx⟩ := P.exists_conj_eq
  have hconj_ne : conjSubgroup x T ≠ T := fun heq => P.ne (heq.symm.trans hx.symm)
  obtain ⟨-, hmod⟩ := P.models CFSG.CGT.T75N.benderCenterInput
    CFSG.CGT.T75N.unitaryTwoGenerationInput
  rcases hmod with ⟨f, hf, hcard, ⟨e⟩⟩ | ⟨a, ha, hcard, ⟨e⟩⟩ | ⟨m, hm, hm3, hcard, ⟨e⟩⟩
  · have hpair := s65_SixFiveF_isL2Pair P hf hcard e
    have hne : conjSubgroup (1 : X) T ≠ conjSubgroup x T := by
      rw [conjSubgroup_one]; exact hconj_ne.symm
    have hne2 : conjSubgroup x T ≠ conjSubgroup (1 : X) T := hne.symm
    obtain ⟨g, hg1, hg2⟩ := hpair.conjTwoTransitive 1 x x 1 hne hne2
    refine ⟨g, ?_, ?_⟩
    · rw [mul_one] at hg1
      rw [hg1]; exact hx.symm
    · rw [hx, conjSubgroup_conjSubgroup, hg2, conjSubgroup_one]
  · obtain ⟨S, hTeq⟩ := exists_sylow_eq_inf_centralizer_of_isElemAbelian ha e P.elem hcard
    have hNA : Subgroup.normalizer (T : Set X) =
        Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [hTeq]
      exact normalizer_inf_centralizer_eq_of_mulEquiv_sz ha e S
    have hxN : x ∉ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [← hNA]
      intro hxN
      exact hconj_ne (mem_normalizer_iff_conjSubgroup_eq.mp hxN)
    have hSne : S ≠ x • S := fun heq =>
      hxN (Sylow.smul_eq_iff_mem_normalizer.mp heq.symm)
    obtain ⟨z, hz1, hz2⟩ := exists_smul_eq_and_smul_eq_of_mulEquiv_sz ha e hSne
    have hconjT : ∀ g : X, conjSubgroup g T = ((g • S : Sylow 2 X) : Subgroup X) ⊓
        Subgroup.centralizer (((g • S : Sylow 2 X) : Subgroup X) : Set X) := by
      intro g
      rw [hTeq, timmesfeld_conjSubgroup_eq, CFSG.Quasithin.E3.conjSubgroup_inf,
        CFSG.Quasithin.E3.conjSubgroup_centralizer,
        s65_SixFiveF_conjSubgroup_inv_smul S g]
    refine ⟨z, ?_, ?_⟩
    · rw [hconjT z, hz1, hx, hconjT x]
    · rw [hx, conjSubgroup_conjSubgroup, hconjT (z * x), mul_smul, hz2, ← hTeq]
  · have hA2 : ∃ a ∈ T, a ≠ 1 ∧ a * a = 1 := by
      obtain ⟨⟨a, ha⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp P.ne_bot
      exact ⟨a, ha, (fun h => ha1' (Subtype.ext h)), P.sq_eq_one QuotPair.mem_pairConj_left ha⟩
    have hz₀ : CFSG.Quasithin.conjSubgroup T x⁻¹ = T₁ :=
      (timmesfeld_conjSubgroup_eq T x).symm.trans hx.symm
    obtain ⟨z, hz2, hzconj⟩ := exists_involution_conj_of_dihedral hm e hz₀ hA2
    have hzz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hTz : conjSubgroup z T = T₁ := by
      rw [timmesfeld_conjSubgroup_eq T z, hzz]; exact hzconj
    refine ⟨z, hTz, ?_⟩
    rw [← hTz, conjSubgroup_conjSubgroup, hz2, conjSubgroup_one]

end Certified

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec11.Item113
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCb
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
import CFSG.RankThree.PartTwo.Sec18.SylowTop
import CFSG.RankThree.PartTwo.Sec18.SylowFiveOmega
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace SylowFive

theorem center_eq_bot_and_card_mulAut {L : Subgroup G} (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
      Nat.card (MulAut (L ⧸ aschbacherSolvableCore 3 L)) = 241920 := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) :=
    Item18ResProof.isSimpleGroup_projSL_three_four
  have : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := eL.isSimpleGroup
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := inferInstance
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Sec19.Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  set ι : L ⧸ aschbacherSolvableCore 3 L ≃* L ⧸ CFSG.pCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq hθeq with hι
  have : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := ι.isSimpleGroup
  have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := inferInstance
  refine ⟨Sec19.Step1914TriProof.center_eq_bot_of_isSimpleGroup_of_isPerfect, ?_⟩
  rw [Nat.card_congr (MulAut.congr ((ι.trans eL).trans
    (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)))).toEquiv]
  exact KFacts.L34.card_mulAut KFacts.L34.card_galoisField_two_two

theorem card_dvd_mul_card_inf_thetaQuotCentralizer {L P : Subgroup G}
    (hAut : Nat.card (MulAut (L ⧸ aschbacherSolvableCore 3 L)) = 241920)
    (hP3 : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card P ∣ 27 * Nat.card (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  set φ : P →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec12.thetaBarAct L).comp (Subgroup.inclusion hPN) with hφ
  have hker : φ.ker.map P.subtype = P ⊓ Sec4.thetaQuotCentralizer L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (hPN y.2)).mpr hy⟩
    · rintro ⟨hxP, hxK⟩
      exact ⟨⟨x, hxP⟩, (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (hPN hxP)).mp hxK, rfl⟩
  have h1 : Nat.card φ.range * Nat.card φ.ker = Nat.card P := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have h2 : Nat.card φ.ker = Nat.card (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective P.subtype_injective]
  have h3 : Nat.card φ.range ∣ 27 := by
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.mp (hP3.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
    have hdvd : Nat.card φ.range ∣ 3 ^ 3 * 8960 := by
      rw [show (3 : ℕ) ^ 3 * 8960 = 241920 by norm_num, ← hAut]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hn] at hdvd ⊢
    have h := (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 8960)).dvd_of_dvd_mul_right hdvd
    rwa [show (3 : ℕ) ^ 3 = 27 by norm_num] at h
  rw [← h1, h2]
  exact mul_dvd_mul_right h3 _

theorem card_le_of_le_normalizer {A M : Subgroup G} (h : Sec18Std G A M) {E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (A : Set G)) (hEa : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec5.isPGroup_of_isElemAbelian hEa)
  have h1 : k ≤ CFSG.Assembly.pRank 3 M :=
    Sec5.le_pRank_of_elemAbelian Nat.prime_three (hE.trans (Rem187QProof.normalizer_le h)) hEa hk
  have h2 : CFSG.Open.pRank 3 M ≤ 3 :=
    (pRank_le_localRank_of_isTwoLocal Nat.prime_three h.mem_scriptM.1.1).trans
      h.toTheoremFourHyp.localRank_three.le
  have hk3 : k ≤ 3 := h1.trans h2
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

theorem mem_thetaQuotCentralizer_lc (H : Subgroup G) (c : G) :
    c ∈ Sec4.thetaQuotCentralizer (lc H c) := by
  have hcomm : ∀ l ∈ lc H c, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (SylowFusion.lc_le_centralizer H c hl)
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr
    ⟨Subgroup.centralizer_le_normalizer (lc H c : Set G)
      (Subgroup.mem_centralizer_iff.mpr hcomm), fun l hl => ?_⟩
  have e : c * l * c⁻¹ = l := by rw [← hcomm l hl, mul_inv_cancel_right]
  rw [e, inv_mul_cancel]
  exact Subgroup.one_mem _

section Certified


variable {A M H : Subgroup G} {c : G}

theorem omegaOne_of_le_normalizer_zpowers (h1812 : Item181_2) (h184 : Item184_1)
    (h1842 : Item184_2) (hH : Sec18H G A M H c) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)))
    (hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    (IsE27 (omegaOneThree P) ∨ IsZ3TimesHeis (omegaOneThree P)) ∧
      c ∉ (frattini (omegaOneThree P)).map (omegaOneThree P).subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ inSubgroup perfectResidual H with hB
  set K := Sec4.thetaQuotCentralizer (lc H c) with hK
  set Y := P ⊓ K with hY
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (mem_and_commutator_mem_of_sec18H hH).1
  have hc3 := orderOf_eq_three_of_sec18H h184 hH
  have hAeq : A = Subgroup.zpowers c ⊔ B := eq_zpowers_sup_of_sec18H h1812 h184 hH
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.1.2 _ x.2)⟩
  have hAP : A ≤ P := SylowTop.le_of_isSylowOf (Subgroup.le_normalizer (H := A)) hA3 hP
  have hPW : P ≤ Subgroup.normalizer (A : Set G) := hP.le
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec11.le_centralizer_of_le_normalizer_zpowers hc3 hP3 (hPW.trans hWc)
  have hPL : P ≤ Subgroup.normalizer (lc H c : Set G) :=
    (hPW.trans hWc).trans (normalizer_zpowers_le_normalizer_lc h1842 hH)
  have hB9 := card_inf_of_sec18H h1812 h184 hH
  have hBel : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hA.1 inf_le_left
  have hBP : B ≤ P := inf_le_left.trans hAP
  have hBlc : B ≤ lc H c := (inf_lc_eq h1812 h184 hH).ge.trans inf_le_right
  have hPB : P ≤ Subgroup.normalizer (B : Set G) := by
    intro x hx
    have h := Subgroup.inf_normalizer_le_normalizer_inf ⟨hPW hx, hPL hx⟩
    rwa [inf_lc_eq h1812 h184 hH] at h
  obtain ⟨eL⟩ := SylowFusion.nonempty_quotient_lc h184 hH
  obtain ⟨hZ, hAut⟩ := center_eq_bot_and_card_mulAut (commutator_inSubgroup_perfectResidual _) eL
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
    Sec12.mem_normalizer_inf_thetaQuotCentralizer (Subgroup.le_normalizer hx) (hPL hx)
  have hYB : Y ≤ Subgroup.centralizer (B : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Sec12.commute_of_mem_thetaQuotCentralizer hP3 (hBlc hb)
      (Subgroup.le_normalizer (hBP hb)) hy.1 hy.2
  have hYB1 : Y ⊓ B = ⊥ := by
    have h1 := Sec12.card_inf_le_card_center_of_le_thetaQuotCentralizer (L := lc H c)
      (hP3.to_le inf_le_left) (inf_le_right : Y ≤ K)
    rw [hZ, Subgroup.card_bot] at h1
    have h2 : Y ⊓ lc H c = ⊥ := Subgroup.eq_bot_of_card_le _ h1
    exact le_bot_iff.mp (h2 ▸ inf_le_inf_left Y hBlc)
  have hcY : c ∈ Y := ⟨hAP hcA, mem_thetaQuotCentralizer_lc H c⟩
  have hY3 : ∀ y ∈ Y, y ^ 3 = 1 → y ∈ Subgroup.zpowers c := by
    intro y hy hy3
    have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hPc hy.1)
    have hle : A ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [hAeq]
      refine sup_le ?_ fun b hb => ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hyc.symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hYB hy)) b hb
    have hyA : y ∈ A := Item183NMProof.mem_of_commute_of_sec18Std hH.toSec18Std hy3
      fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    have hcBn : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) :=
      Subgroup.zpowers_le.mpr (hPB (hAP hcA))
    have hyA' : y ∈ (Subgroup.zpowers c : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcBn, ← hAeq]
      exact hyA
    obtain ⟨z, hz, b, hb, rfl⟩ := hyA'
    have hzY : z ∈ Y := Subgroup.zpowers_le.mpr hcY hz
    have hbY : b ∈ Y := by
      have e : b = z⁻¹ * (z * b) := by group
      rw [e]
      exact Y.mul_mem (Y.inv_mem hzY) hy
    have hb1 : b = 1 := by
      have hmem : b ∈ Y ⊓ B := ⟨hbY, hb⟩
      rwa [hYB1, Subgroup.mem_bot] at hmem
    simpa [hb1] using hz
  exact omegaOne_structure hP3 hc3 hPc hBel hB9 hBP hPB inf_le_left hPY hYB hYB1 hcY hY3
    (card_dvd_mul_card_inf_thetaQuotCentralizer hAut hP3 hPL)
    fun E hEP hE => card_le_of_le_normalizer hH.toSec18Std (hEP.trans hPW) hE

end Certified

end SylowFive

end CFSG.RankThree.PartTwo.Sec18

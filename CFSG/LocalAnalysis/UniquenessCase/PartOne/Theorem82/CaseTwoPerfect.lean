module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoTransitive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs812
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
public import CFSG.GroupTheory.ConjActionModPCore
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSplit
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GroupTheory.CoprimeNormalizerSup
import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
import CFSG.Quasithin.MS93.S45C1
import CFSG.RankThree.PartOne.SRC.ProductCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G}

namespace Ctx812E

theorem mem_L_of_mem_ker_of_pow_three_eq_one (c : Ctx812E G) {y : G}
    (hy : y ∈ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype)
    (hy3 : y ^ 3 = 1) : y ∈ c.L := by
  classical
  set φ := CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L with hφ
  set C : Subgroup G := φ.ker.map c.S.M.subtype with hC
  by_contra hyL
  have hyM : y ∈ c.S.M := Subgroup.map_subtype_le φ.ker hy
  have hy_ne : y ≠ 1 := fun h => hyL (h ▸ c.L.one_mem)
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy_ne
  let R : Subgroup G := Subgroup.zpowers y
  have hR_le_C : R ≤ C := Subgroup.zpowers_le.mpr hy
  have hR_le_M : R ≤ c.S.M := hR_le_C.trans (Subgroup.map_subtype_le φ.ker)
  have hR : IsPGroup 3 R :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord]; norm_num)
  have hR_le_NL : R ≤ Subgroup.normalizer (c.L : Set G) := hR_le_M.trans c.le_normalizer_L
  have hRN : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    hR_le_NL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L c.S.M R
      c.le_normalizer_L hR_le_M).mp (by simpa [hC, hφ] using hR_le_C)
  have hN2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hN_not_dvd_3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
  obtain ⟨S, hS_sylow, hS_cent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := 3) (q := 3) (X := c.L) (N := CFSG.Open.pCoreOf 2 c.L) (R := R)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L) hR_le_NL hRN hR hN_not_dvd_3 hcomm
      hN_not_dvd_3
  have hS_rank : CFSG.Open.pRank 3 S = 3 := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf (p := 3) (by norm_num)
      hS_sylow, c.pRank_three_L]
  obtain ⟨E, hES, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) S
  rw [hS_rank] at hEcard
  have hEL : E ≤ c.L := hES.trans hS_sylow.le
  have hEM : E ≤ c.S.M := hEL.trans c.hyp81.1
  have hEcent : E ≤ Subgroup.centralizer (R : Set G) := hES.trans hS_cent
  have hcardR : Nat.card R = 3 := by rw [Nat.card_zpowers, hyord]
  have hRdisj_L : R ⊓ c.L = ⊥ := by
    have : Fact (Nat.Prime (Nat.card R)) := ⟨by rw [hcardR]; norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (G := ↥R) (c.L.subgroupOf R) with h | h
    · exact disjoint_iff.mp (disjoint_comm.mp (Subgroup.subgroupOf_eq_bot.mp h))
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      exact hyL (h (Subgroup.mem_zpowers y))
  have hdisj : Disjoint E R := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxR
    have hx : x ∈ R ⊓ c.L := ⟨hxR, hEL hxE⟩
    rw [hRdisj_L] at hx
    exact Subgroup.mem_bot.mp hx
  have hcommER : ∀ a ∈ E, ∀ b ∈ R, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hEcent ha) b hb).symm
  have hsup_ab : CFSG.Open.IsElemAbelian 3 (E ⊔ R) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEab (CFSG.Open.isElemAbelian_zpowers hy3) hcommER
  have hsup_le_M : E ⊔ R ≤ c.S.M := sup_le hEM hR_le_M
  have hsup_card : Nat.card ↥(E ⊔ R) = 3 ^ 4 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E R hcommER).1
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one, hEcard, hcardR] at h
    rw [h]; norm_num
  have h4 : 4 ≤ CFSG.Open.pRank 3 c.S.M :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hsup_le_M hsup_ab hsup_card
  rw [c.pRank_three_M] at h4
  omega

theorem not_three_dvd_card_map_ker (c : Ctx812E G)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) :
    ¬ 3 ∣ Nat.card ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) := by
  classical
  intro h3C
  set φ := CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L with hφ
  set C : Subgroup G := φ.ker.map c.S.M.subtype with hC
  obtain ⟨yC, hyCord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3C
  let y : G := (yC : C)
  have hyC : y ∈ C := yC.2
  have hyM : y ∈ c.S.M := Subgroup.map_subtype_le φ.ker hyC
  have hyord : orderOf y = 3 := by
    change orderOf (yC : G) = 3
    rw [Subgroup.orderOf_coe, hyCord]
  have hy3 : y ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hyL : y ∈ c.L := mem_L_of_mem_ker_of_pow_three_eq_one c hyC hy3
  set z : (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) :=
    QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) (⟨y, hyL⟩ : ↥c.L) with hz
  have hφy : φ ⟨y, hyM⟩ = 1 := by
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hyC
    rw [show (⟨y, hyM⟩ : ↥c.S.M) = a from Subtype.ext hay.symm]
    exact MonoidHom.mem_ker.mp ha
  have hconj : MulAut.conj z = φ ⟨y, hyM⟩ := by
    rw [hz]
    exact (CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L c.S.M c.le_normalizer_L
      hyM hyL).symm
  have hz_center : z ∈ Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : z * w * z⁻¹ = w := by
      have := congrArg (fun f : MulAut _ => f w) (hconj.trans hφy)
      simpa [MulAut.conj_apply] using this
    calc w * z = (z * w * z⁻¹) * z := by rw [h1]
      _ = z * w := by group
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hy_core : (⟨y, hyL⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_one_iff]; exact hz1
    have h3core : 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) :=
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk y hyL, hyord] :
        Nat.card (Subgroup.zpowers (⟨y, hyL⟩ : ↥c.L)) = 3) ▸
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy_core)
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
      Nat.prime_three (by norm_num) h3core
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← QuotientGroup.mk_pow,
      show (⟨y, hyL⟩ : ↥c.L) ^ 3 = 1 by ext; simpa using hy3]
    exact QuotientGroup.mk_one _
  have h3center : 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) :=
    (by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz_ne] :
      Nat.card (Subgroup.zpowers z) = 3) ▸
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz_center)
  exact hZ h3center

end Ctx812E

namespace SylowThreeData

private theorem conjModPCore_Lf_eq_one (d : SylowThreeData G) {P₀ : Subgroup G}
    (hPn : ∀ k, P₀ ≤ Subgroup.normalizer (d.Lf k : Set G))
    (hLP : ∀ k, d.Lf k ≤ P₀) {i j : Fin 3} (hij : i ≠ j) {h : G} (hh : h ∈ d.Lf j) :
    CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i) ⟨h, hLP j hh⟩ = 1 := by
  have hHnorm : d.Lf j ≤ Subgroup.normalizer (d.Lf i : Set G) := d.hLnorm i j
  have h1 : ⁅d.Lf i, d.Lf j⁆ ≤ d.Lf i :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hHnorm
  have h2 : ⁅d.Lf i, d.Lf j⁆ ≤ CFSG.Open.pCoreOf 2 d.M := d.hcomm i j hij
  have hcomm : ⁅d.Lf i, d.Lf j⁆ ≤ CFSG.Open.pCoreOf 2 (d.Lf i) :=
    (le_inf h1 h2).trans (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (d.hLM i))
  have hRle : d.Lf j ≤ ((CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hPn i)).ker.map
      P₀.subtype) :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 (d.Lf i) P₀ (d.Lf j) (hPn i)
      (hLP j)).mpr hcomm
  obtain ⟨a, ha, hay⟩ := hRle hh
  rw [show (⟨h, hLP j hh⟩ : ↥P₀) = a from Subtype.ext hay.symm]
  exact MonoidHom.mem_ker.mp ha

end SylowThreeData

namespace CaseTwoTransitive

theorem not_three_dvd_card_center (t : CaseTwoTransitive c) :
    ¬ 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let d := t.d
  rw [← t.hdL]
  have hLM : d.L ≤ d.M := by rw [t.hdL, t.hdM]; exact c.hyp81.1
  have hMnormL : d.M ≤ Subgroup.normalizer (d.L : Set G) := by
    rw [t.hdM, t.hdL]; exact c.le_normalizer_L
  have hMnormO : d.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 d.L : Set G) :=
    hMnormL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 d.L)
  have hO2L_le : CFSG.Open.pCoreOf 2 d.L ≤ d.N := by
    rw [SylowThreeData.N]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 d.L).trans hLM) hMnormO
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.L)
  have hinf : d.L ⊓ d.N = CFSG.Open.pCoreOf 2 d.L := by
    rw [SylowThreeData.N]
    exact le_antisymm
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLM)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 d.L) hO2L_le)
  have hKbar : d.Kbar = CFSG.Open.pCore 2 ↥d.L := by
    rw [SylowThreeData.Kbar, hinf]
    exact CFSG.openPCoreOf_subgroupOf 2 d.L
  let P : Type := ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2))
  letI : Group P := inferInstance
  letI : Finite P := inferInstance
  have hLb_eq_map (i : Fin 3) : d.Lb i = ((d.Lf i).subgroupOf d.L).map d.pi := by
    rw [SylowThreeData.Lb, SylowThreeData.phi, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hLb_sup : d.Lb 0 ⊔ d.Lb 1 ⊔ d.Lb 2 = ⊤ := by
    have hmap : ((d.Lf 0).subgroupOf d.L ⊔ (d.Lf 1).subgroupOf d.L ⊔
        (d.Lf 2).subgroupOf d.L) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (d.Lf_le_L 0) (d.Lf_le_L 1),
        ← Subgroup.subgroupOf_sup (sup_le (d.Lf_le_L 0) (d.Lf_le_L 1)) (d.Lf_le_L 2), ← d.hL]
      exact Subgroup.subgroupOf_self d.L
    rw [hLb_eq_map 0, hLb_eq_map 1, hLb_eq_map 2, ← Subgroup.map_sup, ← Subgroup.map_sup,
      hmap, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have hmu_range : d.mu.range = ⊤ := by
    erw [SylowThreeData.mu, MonoidHom.noncommCoprod_range, MonoidHom.noncommCoprod_range,
      Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.range_subtype, hLb_sup]
  have hmu_surj : Function.Surjective d.mu := MonoidHom.range_eq_top.mp hmu_range
  have hker_center : d.mu.ker ≤ Subgroup.center P := by
    intro y hy
    set a : ↥(d.Lb 0) := y.1.1 with ha
    set b : ↥(d.Lb 1) := y.1.2 with hb
    set e : ↥(d.Lb 2) := y.2 with he
    have habc : (a : d.Q) * b * e = 1 := by
      rw [MonoidHom.mem_ker] at hy
      change (y.1.1 : d.Q) * (y.1.2 : d.Q) * (y.2 : d.Q) = 1 at hy
      rw [← ha, ← hb, ← he] at hy
      exact hy
    have ha_center : a ∈ Subgroup.center ↥(d.Lb 0) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      show (w : d.Q) * (a : d.Q) = (a : d.Q) * (w : d.Q)
      have hb' : Commute (w : d.Q) (b : d.Q) := d.Lb_commute 0 1 (by decide) w.2 b.2
      have he' : Commute (w : d.Q) (e : d.Q) := d.Lb_commute 0 2 (by decide) w.2 e.2
      have ha_eq : (a : d.Q) = ((b : d.Q) * (e : d.Q))⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv, ← mul_assoc]
        exact habc
      rw [ha_eq]
      exact ((hb'.mul_right he').inv_right).eq
    have hb_center : b ∈ Subgroup.center ↥(d.Lb 1) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      show (w : d.Q) * (b : d.Q) = (b : d.Q) * (w : d.Q)
      have ha' : Commute (w : d.Q) (a : d.Q) := d.Lb_commute 1 0 (by decide) w.2 a.2
      have he' : Commute (w : d.Q) (e : d.Q) := d.Lb_commute 1 2 (by decide) w.2 e.2
      have hb_eq : (b : d.Q) = (a : d.Q)⁻¹ * (e : d.Q)⁻¹ := by
        calc (b : d.Q) = (a : d.Q)⁻¹ * ((a : d.Q) * b * e) * (e : d.Q)⁻¹ := by group
          _ = (a : d.Q)⁻¹ * 1 * (e : d.Q)⁻¹ := by rw [habc]
          _ = (a : d.Q)⁻¹ * (e : d.Q)⁻¹ := by group
      rw [hb_eq]
      exact ((ha'.inv_right).mul_right (he'.inv_right)).eq
    have he_center : e ∈ Subgroup.center ↥(d.Lb 2) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      show (w : d.Q) * (e : d.Q) = (e : d.Q) * (w : d.Q)
      have ha' : Commute (w : d.Q) (a : d.Q) := d.Lb_commute 2 0 (by decide) w.2 a.2
      have hb' : Commute (w : d.Q) (b : d.Q) := d.Lb_commute 2 1 (by decide) w.2 b.2
      have he_eq : (e : d.Q) = ((a : d.Q) * (b : d.Q))⁻¹ := eq_inv_of_mul_eq_one_right habc
      rw [he_eq]
      exact ((ha'.mul_right hb').inv_right).eq
    rw [Subgroup.mem_center_iff]
    intro w
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        change (w.1.1 : d.Q) * (a : d.Q) = (a : d.Q) * (w.1.1 : d.Q)
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha_center w.1.1)
      · apply Subtype.ext
        change (w.1.2 : d.Q) * (b : d.Q) = (b : d.Q) * (w.1.2 : d.Q)
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hb_center w.1.2)
    · apply Subtype.ext
      change (w.2 : d.Q) * (e : d.Q) = (e : d.Q) * (w.2 : d.Q)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp he_center w.2)
  have hPperfect : Group.IsPerfect P :=
    CFSG.RankThree.PartOne.SRC.isPerfect_prod
      (CFSG.RankThree.PartOne.SRC.isPerfect_prod (d.isPerfect_Lb 0) (d.isPerfect_Lb 1))
      (d.isPerfect_Lb 2)
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hPperfect d.mu hmu_surj hker_center
  have hmapcenter : (Subgroup.center P).map d.mu = Subgroup.center d.Q := by
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective hmu_surj _
  have hdvd : Nat.card (Subgroup.center d.Q) ∣ Nat.card (Subgroup.center P) := by
    rw [← hmapcenter]
    exact Subgroup.card_map_dvd (Subgroup.center P) d.mu
  have hZLb (i : Fin 3) : ¬ 3 ∣ Nat.card (Subgroup.center ↥(d.Lb i)) := by
    haveI := d.isPerfect_Lb i
    exact not_dvd_card_center_of_pRank_eq_one (q := 3) (by norm_num) (d.pRank_Lb i)
  have hZP : ¬ 3 ∣ Nat.card (Subgroup.center P) := by
    intro h3
    obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center P)) 3 h3
    have hzord' : orderOf ((z : Subgroup.center P) : P) = 3 := by
      rw [Subgroup.orderOf_coe, hzord]
    have hzpow : ((z : Subgroup.center P) : P) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hzord']
    have hz0_center : ((z : Subgroup.center P) : P).1.1 ∈ Subgroup.center ↥(d.Lb 0) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := Subgroup.mem_center_iff.mp z.2 (((w, 1), 1) : P)
      exact congrArg (fun x : P => x.1.1) h
    have hz1_center : ((z : Subgroup.center P) : P).1.2 ∈ Subgroup.center ↥(d.Lb 1) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := Subgroup.mem_center_iff.mp z.2 (((1, w), 1) : P)
      exact congrArg (fun x : P => x.1.2) h
    have hz2_center : ((z : Subgroup.center P) : P).2 ∈ Subgroup.center ↥(d.Lb 2) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := Subgroup.mem_center_iff.mp z.2 (((1, 1), w) : P)
      exact congrArg (fun x : P => x.2) h
    have hz0_pow : (((z : Subgroup.center P) : P).1.1) ^ 3 = 1 := by
      have h := congrArg (fun x : P => x.1.1) hzpow
      change (((z : Subgroup.center P) : P).1.1) ^ 3 = 1 at h
      exact h
    have hz1_pow : (((z : Subgroup.center P) : P).1.2) ^ 3 = 1 := by
      have h := congrArg (fun x : P => x.1.2) hzpow
      change (((z : Subgroup.center P) : P).1.2) ^ 3 = 1 at h
      exact h
    have hz2_pow : (((z : Subgroup.center P) : P).2) ^ 3 = 1 := by
      have h := congrArg (fun x : P => x.2) hzpow
      change (((z : Subgroup.center P) : P).2) ^ 3 = 1 at h
      exact h
    have hz0_one : ((z : Subgroup.center P) : P).1.1 = 1 :=
      CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hz0_center
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hZLb 0)).symm hz0_pow
    have hz1_one : ((z : Subgroup.center P) : P).1.2 = 1 :=
      CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hz1_center
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hZLb 1)).symm hz1_pow
    have hz2_one : ((z : Subgroup.center P) : P).2 = 1 :=
      CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hz2_center
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (hZLb 2)).symm hz2_pow
    have hzone : ((z : Subgroup.center P) : P) = 1 := by
      apply Prod.ext
      · apply Prod.ext
        · exact hz0_one
        · exact hz1_one
      · exact hz2_one
    have hz : z = 1 := Subtype.ext hzone
    rw [hz, orderOf_one] at hzord
    omega
  have hZQ : ¬ 3 ∣ Nat.card (Subgroup.center d.Q) := fun h3 => hZP (h3.trans hdvd)
  have e : d.Q ≃* (↥d.L ⧸ CFSG.Open.pCore 2 ↥d.L) :=
    QuotientGroup.quotientMulEquivOfEq hKbar
  have hcard : Nat.card (Subgroup.center d.Q) =
      Nat.card (Subgroup.center (↥d.L ⧸ CFSG.Open.pCore 2 ↥d.L)) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  intro h3
  exact hZQ (by rwa [hcard])


theorem not_three_dvd_card_ker (t : CaseTwoTransitive c) :
    ¬ 3 ∣ Nat.card ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) :=
  Ctx812E.not_three_dvd_card_map_ker c
    (not_three_dvd_card_center t)


theorem le_L_sup_ker_of_perfect (t : CaseTwoTransitive c) (hOut : PerfectAutInner)
    {Y : Subgroup G} (hYM : Y ≤ c.S.M) (hY : ⁅Y, Y⁆ = Y) :
    Y ≤ c.L ⊔ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let d := t.d
  have hMnormL : d.M ≤ Subgroup.normalizer (d.L : Set G) := by
    rw [t.hdM, t.hdL]; exact c.le_normalizer_L
  have hYM' : Y ≤ d.M := by rw [t.hdM]; exact hYM
  have hperm_d : ∀ m ∈ d.M, ∀ i, ∃ j,
      (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j := by
    intro m hm i
    exact t.hperm m (by rw [← t.hdM]; exact hm) i
  have hYperfect : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  let ρ : ↥Y →* Equiv.Perm (Fin 3) :=
    (d.permHom t.hinj hperm_d).comp (Subgroup.inclusion hYM')
  have hρrange : ρ.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥ρ.range := (Subgroup.nontrivial_iff_ne_bot ρ.range).mpr hne
    haveI : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
    haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Equiv.Perm.isSolvable (by norm_num : Nat.card (Fin 3) ≤ 4)
    haveI : Group.IsSolvable ↥ρ.range :=
      Group.isSolvable_of_isSolvable_injective (G := ↥ρ.range) (G' := Equiv.Perm (Fin 3))
        (f := ρ.range.subtype) ρ.range.subtype_injective
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥ρ.range)
    rw [Group.IsPerfect.commutator_eq_top (G := ↥ρ.range)] at hlt
    exact (lt_irrefl _) hlt
  have hYn (i : Fin 3) : Y ≤ Subgroup.normalizer (d.Lf i : Set G) := by
    intro y hy
    have hmem : ρ ⟨y, hy⟩ ∈ ρ.range := ⟨⟨y, hy⟩, rfl⟩
    rw [hρrange] at hmem
    have h1 : (d.permHom t.hinj hperm_d ⟨y, hYM' hy⟩) = 1 := Subgroup.mem_bot.mp hmem
    exact (SylowThreeData.mem_normalizer_Lf_iff d t.hinj hperm_d ⟨y, hYM' hy⟩ i).mpr (by
      rw [h1]; rfl)
  let P₀ : Subgroup G := Y ⊔ d.L
  have hYP0 : Y ≤ P₀ := le_sup_left
  have hLn (i : Fin 3) : d.L ≤ Subgroup.normalizer (d.Lf i : Set G) := by
    rw [d.hL]
    exact sup_le (sup_le (d.hLnorm i 0) (d.hLnorm i 1)) (d.hLnorm i 2)
  have hP0n (i : Fin 3) : P₀ ≤ Subgroup.normalizer (d.Lf i : Set G) :=
    sup_le (hYn i) (hLn i)
  have hLfP0 (j : Fin 3) : d.Lf j ≤ P₀ := (d.Lf_le_L j).trans le_sup_right
  have hLy : d.L ≤ P₀ := le_sup_right
  let φP : (i : Fin 3) → ↥P₀ →* MulAut (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)) :=
    fun i => CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0n i)
  let φY : (i : Fin 3) → ↥Y →* MulAut (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)) :=
    fun i => CFSG.GroupTheory.conjModPCore 2 (d.Lf i) Y (hYn i)
  have hinner (i : Fin 3) :
      (φY i).range ≤ (MulAut.conj : (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)) →*
        MulAut (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i))).range := by
    let X := ↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)
    letI : Group X := inferInstance
    letI : Finite X := inferInstance
    obtain ⟨hN, hQ⟩ := (t.hcomp i).2.2.2
    have hQX : CFSG.Open.IsQuasisimple X := hQ
    haveI : Group.IsPerfect X := ⟨hQX.1⟩
    have hne : d.Lf i ≠ ⊤ := by
      intro htop
      exact c.M_ne_top (t.hdM ▸ top_le_iff.mp (htop ▸ d.hLM i))
    have hKLi : CFSG.Open.IsKGroup ↥(d.Lf i) := c.standing.kProper.isKGroup (d.Lf i) hne
    have hKX : CFSG.Open.IsKGroup X := CFSG.Open.IsKGroup.quotient hKLi _
    have hrankX : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      have h1 : CFSG.pRank 3 X = CFSG.pRank 3 ↥(d.Lf i) :=
        CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
          (CFSG.GroupTheory.not_dvd_card_of_isPGroup
            (CFSG.pCore_isPGroup (p := 2) (G := ↥(d.Lf i))) Nat.prime_three
            (by norm_num : (3 : ℕ) ≠ 2))
      rw [h1, CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank i]
    have hZX : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
      not_dvd_card_center_of_pRank_eq_one (q := 3) (by norm_num) hrankX
    have hφperf : ⁅(φY i).range, (φY i).range⁆ = (φY i).range := by
      haveI : Group.IsPerfect ↥(φY i).range := Group.IsPerfect.range (φY i)
      exact Subgroup.isPerfect_iff.mp inferInstance
    exact hOut X hKX hQX hZX hrankX (φY i).range hφperf
  intro g hg
  have hchoose (i : Fin 3) :
      ∃ (l : G) (hl : l ∈ d.Lf i),
        φP i ⟨l, hLfP0 i hl⟩ = φP i ⟨g, hYP0 hg⟩ := by
    have hginn : φY i ⟨g, hg⟩ ∈ (MulAut.conj : (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)) →*
        MulAut (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i))).range :=
      hinner i ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hginn
    obtain ⟨l, hlq⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥(d.Lf i)) q
    have hcomp : φY i = (φP i).comp (Subgroup.inclusion (le_sup_left : Y ≤ P₀)) := by
      show CFSG.GroupTheory.conjModPCore 2 (d.Lf i) Y (hYn i) =
        (CFSG.GroupTheory.conjModPCore 2 (d.Lf i) P₀ (hP0n i)).comp
          (Subgroup.inclusion (le_sup_left : Y ≤ P₀))
      exact CFSG.GroupTheory.conjModPCore_comp_inclusion 2 (d.Lf i) le_sup_left (hP0n i) (hYn i)
    have hvalg : φP i ⟨g, hYP0 hg⟩ = MulAut.conj q := by
      have h1 : φY i ⟨g, hg⟩ = φP i ⟨g, hYP0 hg⟩ := by
        have hthis := congrArg
          (fun f : ↥Y →* MulAut (↥(d.Lf i) ⧸ CFSG.Open.pCore 2 ↥(d.Lf i)) =>
            f ⟨g, hg⟩) hcomp
        have hinc : (Subgroup.inclusion hYP0 ⟨g, hg⟩ : ↥P₀) = ⟨g, hYP0 hg⟩ := Subtype.ext rfl
        rw [MonoidHom.comp_apply, hinc] at hthis
        exact hthis
      rw [← h1, ← hq]
    have hφl : φP i ⟨(l : G), hLfP0 i l.2⟩ = MulAut.conj q := by
      rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 (d.Lf i) P₀ (hP0n i)
        (hLfP0 i l.2) l.2]
      rw [show QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥(d.Lf i))
        (⟨(l : G), l.2⟩ : ↥(d.Lf i)) = q by
        simpa using hlq]
    exact ⟨(l : G), l.2, hφl.trans hvalg.symm⟩
  choose l hlL hlφ using hchoose
  let lall : G := l 0 * l 1 * l 2
  have hlallL : lall ∈ d.L :=
    d.L.mul_mem (d.L.mul_mem (d.Lf_le_L 0 (hlL 0)) (d.Lf_le_L 1 (hlL 1)))
      (d.Lf_le_L 2 (hlL 2))
  have hlallP0 : lall ∈ P₀ := hLy hlallL
  let h : G := lall⁻¹ * g
  have hLM : d.L ≤ d.M := by
    rw [d.hL]
    exact sup_le (sup_le (d.hLM 0) (d.hLM 1)) (d.hLM 2)
  have hhM : h ∈ d.M :=
    d.M.mul_mem (d.M.inv_mem (hLM hlallL)) (hYM' hg)
  have hhP0 : h ∈ P₀ :=
    P₀.mul_mem (P₀.inv_mem hlallP0) (hYP0 hg)
  have hφh (i : Fin 3) : φP i ⟨h, hhP0⟩ = 1 := by
    have hP0eq : (⟨h, hhP0⟩ : ↥P₀) =
        (⟨lall, hlallP0⟩ : ↥P₀)⁻¹ * ⟨g, hYP0 hg⟩ := Subtype.ext rfl
    have hlall_eq : (⟨lall, hlallP0⟩ : ↥P₀) =
        ⟨l 0, hLfP0 0 (hlL 0)⟩ * ⟨l 1, hLfP0 1 (hlL 1)⟩ *
          ⟨l 2, hLfP0 2 (hlL 2)⟩ := Subtype.ext rfl
    have hφlall : φP i ⟨lall, hlallP0⟩ = φP i ⟨g, hYP0 hg⟩ := by
      rw [hlall_eq, map_mul, map_mul]
      simp only [φP]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 from by fin_cases i <;> simp) with rfl | rfl | rfl
      · rw [SylowThreeData.conjModPCore_Lf_eq_one d hP0n hLfP0 (i := 0) (j := 1) (by decide)
            (hlL 1),
          SylowThreeData.conjModPCore_Lf_eq_one d hP0n hLfP0 (i := 0) (j := 2) (by decide)
            (hlL 2),
          hlφ 0, mul_one, mul_one]
      · rw [SylowThreeData.conjModPCore_Lf_eq_one d hP0n hLfP0 (i := 1) (j := 0) (by decide)
            (hlL 0),
          SylowThreeData.conjModPCore_Lf_eq_one d hP0n hLfP0 (i := 1) (j := 2) (by decide)
            (hlL 2),
          hlφ 1, one_mul, mul_one]
      · rw [SylowThreeData.conjModPCore_Lf_eq_one d hP0n hLfP0 (i := 2) (j := 0) (by decide)
            (hlL 0),
          SylowThreeData.conjModPCore_Lf_eq_one d hP0n hLfP0 (i := 2) (j := 1) (by decide)
            (hlL 1),
          hlφ 2, one_mul, one_mul]
    rw [hP0eq, map_mul, map_inv, hφlall, inv_mul_cancel]
  have hcore_i (i : Fin 3) : CFSG.Open.pCoreOf 2 (d.Lf i) ≤ CFSG.Open.pCoreOf 2 d.L := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (d.Lf i)).trans (d.Lf_le_L i)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (d.Lf i))
    exact (hLn i).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (d.Lf i))
  have hcommLf (i : Fin 3) :
      ⁅d.Lf i, Subgroup.zpowers h⁆ ≤ CFSG.Open.pCoreOf 2 (d.Lf i) := by
    have hker : Subgroup.zpowers h ≤ ((φP i).ker.map P₀.subtype) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr
        ⟨⟨h, hhP0⟩, MonoidHom.mem_ker.mpr (hφh i), rfl⟩)
    exact (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 (d.Lf i) P₀
      (Subgroup.zpowers h) (hP0n i) (Subgroup.zpowers_le.mpr hhP0)).mp hker
  have hLN : d.L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 d.L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 d.L
  have hLfN (i : Fin 3) : d.Lf i ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 d.L : Set G) :=
    (d.Lf_le_L i).trans hLN
  have hcommLf' (i : Fin 3) : ⁅d.Lf i, Subgroup.zpowers h⁆ ≤ CFSG.Open.pCoreOf 2 d.L :=
    (hcommLf i).trans (hcore_i i)
  have hcommL : ⁅d.L, Subgroup.zpowers h⁆ ≤ CFSG.Open.pCoreOf 2 d.L := by
    conv_lhs => rw [d.hL]
    have h01 : ⁅d.Lf 0 ⊔ d.Lf 1, Subgroup.zpowers h⁆ ≤ CFSG.Open.pCoreOf 2 d.L :=
      CFSG.Quasithin.MS93.S45.commutator_sup_left_le (hLfN 0) (hLfN 1)
        (hcommLf' 0) (hcommLf' 1)
    exact CFSG.Quasithin.MS93.S45.commutator_sup_left_le (sup_le (hLfN 0) (hLfN 1)) (hLfN 2)
      h01 (hcommLf' 2)
  have hhC : h ∈ (CFSG.GroupTheory.conjModPCore 2 d.L d.M hMnormL).ker.map d.M.subtype := by
    have hz : Subgroup.zpowers h ≤
        (CFSG.GroupTheory.conjModPCore 2 d.L d.M hMnormL).ker.map d.M.subtype :=
      (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 d.L d.M (Subgroup.zpowers h)
        hMnormL (Subgroup.zpowers_le.mpr hhM)).mpr hcommL
    exact Subgroup.zpowers_le.mp hz
  have hgeq : g = lall * h := by
    simp only [h]
    group
  have hgoal : g ∈ d.L ⊔ (CFSG.GroupTheory.conjModPCore 2 d.L d.M hMnormL).ker.map
      d.M.subtype := by
    rw [hgeq]
    exact Subgroup.mul_mem (d.L ⊔ (CFSG.GroupTheory.conjModPCore 2 d.L d.M hMnormL).ker.map
      d.M.subtype) (Subgroup.mem_sup_left hlallL) (Subgroup.mem_sup_right hhC)
  have hCd : (CFSG.GroupTheory.conjModPCore 2 d.L d.M hMnormL).ker.map d.M.subtype =
      (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map c.S.M.subtype := by
    ext x
    rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 d.L d.M hMnormL,
      CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 c.L c.S.M c.le_normalizer_L,
      t.hdL, t.hdM]
  have hsup_eq : d.L ⊔ (CFSG.GroupTheory.conjModPCore 2 d.L d.M hMnormL).ker.map d.M.subtype =
      c.L ⊔ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype := by
    rw [hCd, t.hdL]
  rw [← hsup_eq]
  exact hgoal


theorem mem_L_of_mem_perfect (t : CaseTwoTransitive c) (hOut : PerfectAutInner)
    {Y : Subgroup G} (hYM : Y ≤ c.S.M) (hY : ⁅Y, Y⁆ = Y) {x : G} (hxY : x ∈ Y)
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : x ∈ c.L := by
  have hle := le_L_sup_ker_of_perfect t hOut hYM hY
  have hzx : Subgroup.zpowers x ≤
      c.L ⊔ (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
        c.S.M.subtype :=
    (Subgroup.zpowers_le.mpr hxY).trans hle
  have hCnorm : (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype ≤ Subgroup.normalizer (c.L : Set G) :=
    (Subgroup.map_subtype_le _).trans c.le_normalizer_L
  have hcop : ¬ 3 ∣ Nat.card ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M
      c.le_normalizer_L).ker.map c.S.M.subtype) := not_three_dvd_card_ker t
  have hQleK := CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card Nat.prime_three
    hCnorm hx hzx hcop
  exact hQleK (Subgroup.mem_zpowers x)


end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

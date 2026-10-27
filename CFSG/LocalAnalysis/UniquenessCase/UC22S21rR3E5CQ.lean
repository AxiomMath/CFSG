module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CQA
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Quot
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Quasithin.Background.F918Z4c1Sz
import CFSG.LocalAnalysis.WeakClosure81.W15SixC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_barImage_eq_top_of_sup {C L : Subgroup G} (hCL : C ≤ L)
    (hsup : C ⊔ CFSG.Open.pCoreOf 2 L = L) : barImage L C = ⊤ := by
  have hO : CFSG.Open.pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hOXeq : (CFSG.Open.pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    ext o
    rw [Subgroup.mem_subgroupOf, CFSG.mem_openPCoreOf_iff]
  haveI : ((CFSG.Open.pCoreOf 2 L).subgroupOf L).Normal := by
    rw [hOXeq]
    exact CFSG.pCore_normal
  have htop : C.subgroupOf L ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCL hO, hsup, Subgroup.subgroupOf_self]
  rw [eq_top_iff]
  intro q _
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : l ∈ C.subgroupOf L ⊔ (CFSG.Open.pCoreOf 2 L).subgroupOf L := by
    rw [htop]; trivial
  obtain ⟨c, hc, o, ho, hco⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := C.subgroupOf L)
      (t := (CFSG.Open.pCoreOf 2 L).subgroupOf L)).mp hmem
  have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
  have ho' : o ∈ CFSG.pCore 2 ↥L := hOXeq ▸ ho
  have h1 : uc22p21cPi L o = 1 := (QuotientGroup.eq_one_iff o).mpr ho'
  have hcl : uc22p21cPi L c = uc22p21cPi L l := by
    have hcl' : l = c * o := hco.symm
    rw [hcl', map_mul, h1, mul_one]
  exact uc22p21c_mem_barImage.mpr ⟨c, hcC, hcl⟩

theorem uc22r3e5c_surjective_of_sup {C L : Subgroup G} (hCL : C ≤ L)
    (hsup : C ⊔ CFSG.Open.pCoreOf 2 L = L) :
    Function.Surjective ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion hCL)) := by
  intro q
  have hq : q ∈ barImage L C := by
    rw [uc22r3e5c_barImage_eq_top_of_sup hCL hsup]; trivial
  obtain ⟨c, hc, hcq⟩ := uc22p21c_mem_barImage.mp hq
  exact ⟨⟨(c : G), hc⟩, hcq⟩

theorem uc22r3e5c_barImage_derInf8_eq_top {C L : Subgroup G} (hCL : C ≤ L)
    (hsup : C ⊔ CFSG.Open.pCoreOf 2 L = L) (hperf : Group.IsPerfect (Bar2 L)) :
    barImage L (F08.DerInf8 C) = ⊤ := by
  have hsurj := uc22r3e5c_surjective_of_sup hCL hsup
  have hmap := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hCL)) hsurj
  rw [eq_top_iff]
  intro q _
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hq : uc22p21cPi L l ∈
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥C).map
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hCL)) := by
    rw [hmap]; trivial
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hq
  have hyC : (y : G) ∈ C := y.2
  have hyJ : (y : G) ∈ F08.DerInf8 C := by
    rw [show F08.DerInf8 C = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥C).map
      C.subtype from rfl]
    exact Subgroup.mem_map_of_mem C.subtype hy
  exact uc22p21c_mem_barImage.mpr ⟨⟨(y : G), hCL hyC⟩, hyJ, hyx⟩

theorem uc22r3e5c_derInf8_sup_pCore {C L : Subgroup G} (hCL : C ≤ L)
    (hsup : C ⊔ CFSG.Open.pCoreOf 2 L = L) (hperf : Group.IsPerfect (Bar2 L)) :
    F08.DerInf8 C ⊔ CFSG.Open.pCoreOf 2 L = L := by
  have hO : CFSG.Open.pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hJ : F08.DerInf8 C ≤ L := by
    rw [show F08.DerInf8 C = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥C).map
      C.subtype from rfl]
    exact (Subgroup.map_subtype_le _).trans hCL
  have hbar := uc22r3e5c_barImage_derInf8_eq_top hCL hsup hperf
  refine le_antisymm (sup_le hJ hO) ?_
  intro l hl
  have hq : uc22p21cPi L ⟨l, hl⟩ ∈ barImage L (F08.DerInf8 C) := by rw [hbar]; trivial
  obtain ⟨j, hj, hjl⟩ := uc22p21c_mem_barImage.mp hq
  have hmem : j⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff]
    show uc22p21cPi L (j⁻¹ * ⟨l, hl⟩) = 1
    rw [map_mul, map_inv, hjl]
    simp
  have hmemG : (j : G)⁻¹ * l ∈ CFSG.Open.pCoreOf 2 L :=
    (CFSG.mem_openPCoreOf_iff _).mpr hmem
  have hle : l = (j : G) * ((j : G)⁻¹ * l) := by group
  rw [hle]
  exact Subgroup.mul_mem_sup hj hmemG

theorem uc22r3e5c_bar2_derInf8_equiv {C L : Subgroup G} (hCL : C ≤ L)
    (hsup : C ⊔ CFSG.Open.pCoreOf 2 L = L) (hperf : Group.IsPerfect (Bar2 L)) :
    Nonempty (Bar2 L ≃* Bar2 (F08.DerInf8 C)) := by
  have hJ : F08.DerInf8 C ≤ L := by
    rw [show F08.DerInf8 C = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥C).map
      C.subtype from rfl]
    exact (Subgroup.map_subtype_le _).trans hCL
  exact CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv hJ
    (uc22r3e5c_derInf8_sup_pCore hCL hsup hperf).symm

theorem uc22r3e5c_sec7Hyp
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (hSg : UC6S846.SigmaStd D) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0)
    (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) {p : ℕ}
    (hp : p ∈ D.sig) :
    F07.Sec7Hyp D p (normalizer (Subgroup.zpowers a : Set G)) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp
  have hcard5 : Nat.card ↥(Subgroup.zpowers a) = 5 := by
    rw [Nat.card_zpowers, ha5]
  have hB1 : Subgroup.zpowers a ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard5
    exact absurd hcard5 (by norm_num)
  have hBM : Subgroup.zpowers a ≤ D.M := zpowers_le.2 (c.hBM haB)
  have hN : ¬ normalizer (Subgroup.zpowers a : Set G) ≤ D.M :=
    fun h => u4x_false_of_normalizer_le h1930 c haB h
  have h2 := uc22r3e5c_two_le_pRank_centralizer h5 h15 h1930 c hL hc2 hSz h5n haB
    ha5 haT hp
  obtain ⟨hXM, -, -⟩ := uc22p22u_conjClosure_isProd (X := D.M) (K := L) le_rfl
    Subgroup.le_normalizer hL
  have hle : conjClosure D.M L ⊓ centralizer (Subgroup.zpowers a : Set G) ≤
      normalizer (Subgroup.zpowers a : Set G) ⊓ D.M := by
    intro x hx
    exact ⟨Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2,
      hXM (Subgroup.mem_inf.mp hx).1⟩
  have hrank : 1 < CFSG.Open.pRank p
      (normalizer (Subgroup.zpowers a : Set G) ⊓ D.M) := by
    have hmono := CFSG.SectionRank.pRank_mono hpp.one_lt hle
    omega
  exact uc22s13xm_sec7Hyp hpp hp2 hsp hB1 hBM hN hrank

theorem uc22r3e5c_derInf8_le (X : Subgroup G) : F08.DerInf8 X ≤ X := by
  rw [show F08.DerInf8 X = (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥X).map
    X.subtype from rfl]
  exact Subgroup.map_subtype_le _

theorem uc22r3e5c_derInf8_perfect (X : Subgroup G) :
    ⁅F08.DerInf8 X, F08.DerInf8 X⁆ = F08.DerInf8 X :=
  Subgroup.isPerfect_iff.mp (isPerfect_derInf8 X)

theorem uc22r3e5c_sup_pCore_centralizer
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) :
    (L ⊓ centralizer (Subgroup.zpowers a : Set G)) ⊔ CFSG.Open.pCoreOf 2 L = L := by
  have hCX := uc22r3e5c_centralizesBar_of_isSz h5 h1930 c hL hSz h5n haB ha5 haT
  have hcent : ∀ x ∈ Subgroup.zpowers a, CentralizesBar x L := fun x hx =>
    uc22p21d_centralizesBar_of_mem_zpowers hCX hx
  have hcard5 : Nat.card ↥(Subgroup.zpowers a) = 5 := by
    rw [Nat.card_zpowers, ha5]
  exact uc22p21d_sup_pCore_eq (L := L) (A := Subgroup.zpowers a) (r := 5)
    Nat.prime_five (by norm_num) hcard5 hcent

theorem uc22r3e5c_derInf8_le_normalizer_inf {D : Data G} {L : Subgroup G} {a : G}
    (hL : L ∈ calC D.M) :
    F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)) ≤
      normalizer (Subgroup.zpowers a : Set G) ⊓ D.M := by
  intro x hx
  have hxC : x ∈ L ⊓ centralizer (Subgroup.zpowers a : Set G) :=
    uc22r3e5c_derInf8_le _ hx
  exact ⟨Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hxC).2,
    hL.1.le (Subgroup.mem_inf.mp hxC).1⟩

theorem uc22r3e5c_core_setup
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) {p : ℕ}
    (hp : p ∈ D.sig) :
    ∃ eJ : Bar2 L ≃* Bar2 (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G))),
      ⁅F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)),
        F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G))⁆ =
        F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)) ∧
      F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)) ≤
        normalizer (Subgroup.zpowers a : Set G) ⊓ D.M ∧
      IsSimpleGroup (Bar2 (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)))) ∧
      p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)))) := by
  have hsup := uc22r3e5c_sup_pCore_centralizer h5 h1930 c hL hSz h5n haB ha5 haT
  have hperf : Group.IsPerfect (Bar2 L) := isPerfect_bar2_of_isSz hSz
  obtain ⟨eJ⟩ := uc22r3e5c_bar2_derInf8_equiv inf_le_left hsup hperf
  have hJperf := uc22r3e5c_derInf8_perfect (L ⊓ centralizer (Subgroup.zpowers a : Set G))
  have hJN := uc22r3e5c_derInf8_le_normalizer_inf (a := a) hL
  have hsimpJ : IsSimpleGroup
      (Bar2 (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)))) := by
    haveI : IsSimpleGroup (Bar2 L) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
    exact eJ.symm.isSimpleGroup
  have hpJ : p ∣ Nat.card (Bar2 (F08.DerInf8
      (L ⊓ centralizer (Subgroup.zpowers a : Set G)))) := by
    rw [← Nat.card_congr eJ.toEquiv]
    exact uc22r3e5c_dvd_card_bar2 h15 h1930 c hL hc2 hSz hp
  exact ⟨eJ, hJperf, hJN, hsimpJ, hpJ⟩

theorem uc22r3e5c_dvd_card_derInf8
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) {p : ℕ}
    (hp : p ∈ D.sig) :
    p ∣ Nat.card (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G))) := by
  have hsup := uc22r3e5c_sup_pCore_centralizer h5 h1930 c hL hSz h5n haB ha5 haT
  have hperf : Group.IsPerfect (Bar2 L) := isPerfect_bar2_of_isSz hSz
  have hbarJ := uc22r3e5c_barImage_derInf8_eq_top inf_le_left hsup hperf
  have hJL : F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)) ≤ L :=
    (uc22r3e5c_derInf8_le _).trans inf_le_left
  let fJ : ↥(F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G))) →* Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hJL)
  have hfJ : Function.Surjective fJ := by
    intro q
    have hq : q ∈ barImage L (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G))) := by
      rw [hbarJ]; trivial
    obtain ⟨j, hj, hqj⟩ := uc22p21c_mem_barImage.mp hq
    exact ⟨⟨(j : G), hj⟩, hqj⟩
  have hdvd : Nat.card (Bar2 L) ∣
      Nat.card (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G))) := by
    have hcard := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective fJ hfJ).toEquiv
    rw [← hcard]
    exact Subgroup.card_quotient_dvd_card _
  exact (uc22r3e5c_dvd_card_bar2 h15 h1930 c hL hc2 hSz hp).trans hdvd

theorem uc22r3e5c_false_of_isAlt_bar2 {L : Subgroup G} {n : ℕ} (hAlt : IsAlt (Bar2 L) 5)
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) : False := by
  obtain ⟨e5⟩ := hAlt
  have hcard60 : Nat.card (Bar2 L) = 60 := by
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcardSz : Nat.card (Bar2 L) = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) :=
    CFSG.Quasithin.card_of_isSz (CFSG.LocalAnalysis.WeakClosure81.isSz_iff_isSz.mp hSz)
  have h2n : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 65 ≤ (2 ^ n) ^ 2 + 1 := by nlinarith
  have hB : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
  have hC : 7 ≤ 2 ^ n - 1 := by omega
  have hge : 60 < ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
    calc 60 < 65 * 64 * 7 := by norm_num
      _ ≤ ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC
  omega

theorem uc22r3e5c_false_of_solvable
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) {p : ℕ}
    (hp : p ∈ D.sig)
    (hsol : Group.IsSolvable ↥(F07.ImageModK p (normalizer (Subgroup.zpowers a : Set G))
      (normalizer (Subgroup.zpowers a : Set G) ⊓ D.M))) : False := by
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨-, hJperf, hJN, -, -⟩ :=
    uc22r3e5c_core_setup h5 h15 h1930 c hL hc2 hSz h5n haB ha5 haT hp
  have hJcore : F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)) ≤
      F07.PPrimeCoreIn p (normalizer (Subgroup.zpowers a : Set G)) :=
    le_pPrimeCoreIn_of_isSolvable inf_le_left hJN hJperf hsol
  have hpJ := uc22r3e5c_dvd_card_derInf8 h5 h15 h1930 c hL hc2 hSz h5n haB ha5 haT hp
  haveI : (CFSG.pPrimeCore p ↥(normalizer (Subgroup.zpowers a : Set G))).Normal :=
    CFSG.pPrimeCore_normal
  have hcop : Nat.Coprime p
      (Nat.card (F07.PPrimeCoreIn p (normalizer (Subgroup.zpowers a : Set G)))) := by
    have hcard : Nat.card (F07.PPrimeCoreIn p (normalizer (Subgroup.zpowers a : Set G))) =
        Nat.card (CFSG.pPrimeCore p ↥(normalizer (Subgroup.zpowers a : Set G))) :=
      Subgroup.card_map_of_injective (normalizer _).subtype_injective
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  exact (hpp.coprime_iff_not_dvd.mp hcop)
    (hpJ.trans (Subgroup.card_dvd_of_le hJcore))

theorem uc22r3e5c_false_of_altTen
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (h5n : ¬ 5 ∣ n) {a : G} (haB : a ∈ c.B0) (ha5 : orderOf a = 5)
    (haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) {p : ℕ}
    (hp : p ∈ D.sig) (hn : 2 < n)
    (hA5 : ∀ Y : Subgroup (F07.QuotK7 p (normalizer (Subgroup.zpowers a : Set G))),
      Y ≤ F07.ImageModK p (normalizer (Subgroup.zpowers a : Set G))
        (normalizer (Subgroup.zpowers a : Set G) ⊓ D.M) → ⁅Y, Y⁆ = Y →
      ∀ (S : Type) [Group S], IsSimpleGroup S → ∀ f : ↥Y →* S, Function.Surjective f →
        IsAlt S 5) : False := by
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨eJ, hJperf, hJN, hsimpJ, hpJ⟩ :=
    uc22r3e5c_core_setup h5 h15 h1930 c hL hc2 hSz h5n haB ha5 haT hp
  have hAltJ : IsAlt (Bar2 (F08.DerInf8 (L ⊓ centralizer (Subgroup.zpowers a : Set G)))) 5 :=
    isAlt_five_bar2_of_perfect hpp inf_le_left hJN hJperf hsimpJ hpJ hA5
  have hAltL : IsAlt (Bar2 L) 5 := by
    obtain ⟨e5⟩ := hAltJ
    exact ⟨eJ.trans e5⟩
  exact uc22r3e5c_false_of_isAlt_bar2 hAltL hn hSz

theorem uc22r3e5c_false_of_not_five_dvd {D : Data G}
    {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch) (hSg : UC6S846.SigmaStd D)
    (h72 : F07.R72 D) (hK72 : KStrongEmbedded72) (h1930 : H1930 D) (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) (h5n : ¬ 5 ∣ n)
    (hB0 : ∀ a ∈ c.B0, a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G)) :
    False := by
  obtain ⟨a, haB, ha5⟩ := uc22r3e5c_exists_elt_of_order_five c hn3 hpow
  have haT : a ∈ normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G) := hB0 a haB
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hS : F07.Sec7Hyp D p (normalizer (Subgroup.zpowers a : Set G)) :=
    uc22r3e5c_sec7Hyp h5 h15 hSg h1930 c hL hc2 hSz h5n haB ha5 haT hp
  rcases solvable_or_altTen_of_sec7Hyp h72 hK72 hS with hsol | ⟨hp5, -, -, -, hA5⟩
  · exact uc22r3e5c_false_of_solvable h5 h15 h1930 c hL hc2 hSz h5n haB ha5 haT hp hsol
  · exact uc22r3e5c_false_of_altTen h5 h15 h1930 c hL hc2 hSz h5n haB ha5 haT hp hn hA5

end CFSG.LocalAnalysis.UniquenessCase.UC22

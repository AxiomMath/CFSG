module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.FrattiniSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarKernel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

open scoped commutatorElement

private theorem k89ooy_ne_bot_of_one_le_pRank {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (h : 1 ≤ CFSG.Open.pRank 3 Q) : Q ≠ ⊥ := by
  intro hbot
  have hzero : CFSG.Open.pRank 3 Q ≤ 0 := by
    rw [hbot]
    refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
    intro E hE _
    have hEb : E = ⊥ := eq_bot_iff.mpr hE
    rw [hEb, Subgroup.card_bot]
    norm_num
  omega

private theorem k89ooy_orderOf_eq_three {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {x : G} (hx : x ∈ A) (hcard : Nat.card A = 3) (hx1 : x ≠ 1) :
    orderOf x = 3 := by
  have hdvd : orderOf x ∣ 3 := by
    rw [← hcard, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hx)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

private theorem k89ooy_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {x : G} (hx : x ∈ A) (hcard : Nat.card A = 3) : x ^ 3 = 1 := by
  have hdvd : orderOf x ∣ 3 := by
    rw [← hcard, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hx)
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private theorem k89ooy_isElemAbelian_sup {G : Type} [Group G] [Finite G]
    {P Z Y : Subgroup G} (hZP : Z ≤ P) (hYP : Y ≤ P)
    (hZc : Z ≤ Subgroup.centralizer (P : Set G)) (hYc : Y ≤ Subgroup.centralizer (P : Set G))
    (hZcard : Nat.card Z = 3) (hYcard : Nat.card Y = 3) :
    IsElemAbelian 3 (Z ⊔ Y) := by
  have hcomm : ∀ z ∈ Z, ∀ y ∈ Y, z * y = y * z := fun z hz y hy =>
    Subgroup.mem_centralizer_iff.mp (hYc hy) z (hZP hz)
  constructor
  · have hsupP : Z ⊔ Y ≤ P := sup_le hZP hYP
    have hsupC : Z ⊔ Y ≤ Subgroup.centralizer (P : Set G) := sup_le hZc hYc
    exact Subgroup.le_centralizer_iff_isMulCommutative.mp
      (hsupC.trans (Subgroup.centralizer_le (fun x hx => hsupP hx)))
  · have hZYnorm : Z ≤ Subgroup.normalizer (Y : Set G) :=
      (hZc.trans (Subgroup.centralizer_le (fun y hy => hYP hy))).trans
        (Subgroup.centralizer_le_normalizer (Y : Set G))
    intro x hx
    obtain ⟨z, hz, y, hy, rfl⟩ := r889_mem_sup_of_le_normalizer hZYnorm hx
    rw [Commute.mul_pow (hcomm z hz y hy) 3, k89ooy_pow_three_eq_one hz hZcard,
      k89ooy_pow_three_eq_one hy hYcard, mul_one]

private theorem k89ooy_exists_of_not_le_gamma {G : Type} [Group G] [Finite G] {M E : Subgroup G}
    (h : ¬ CFSG.Open.rankThreeGamma 1 3 E ≤ M) :
    ∃ X : Subgroup G, X ≤ E ∧ X ≠ ⊥ ∧ ¬ Subgroup.normalizer (X : Set G) ≤ M := by
  by_contra hc
  apply h
  rw [CFSG.Open.rankThreeGamma, CFSG.Open.GLBCore]
  refine sSup_le (fun N hN => ?_)
  obtain ⟨Q, hQE, hQr, rfl⟩ := hN
  by_contra hNM
  exact hc ⟨Q, hQE, k89ooy_ne_bot_of_one_le_pRank hQr, hNM⟩

theorem s889_omega_of_y {G : Type} [Group G] [Finite G]
    (D : Data G) (hSg : SigmaStd D) (h6_14 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_14 D)
    (h885 : R885 D) (h886 : R886 D) (h887 : R887 D)
    (hY : ∀ L P : Subgroup G, Set880 D L P → ¬ P ≤ L → ∃ Y : Subgroup G, Y889 D L P Y) :
    S889Omega D := by
  classical
  intro L P hS hPL
  obtain ⟨Y, hY8⟩ := hY L P hS hPL
  set Z : Subgroup G := ZOf (P ⊓ L) with hZdef
  set E : Subgroup G := Z ⊔ Y with hEdef
  have hZcard : Nat.card Z = 3 := (h886 L P hS).1
  have hZnorm : Subgroup.normalizer (Z : Set G) ≤ D.M := h887 L P hS
  have hJ2 : IsSpor (Bar2 L) .J2 := (h885 L P hS).1
  have hsig : D.sig = {5} := (h885 L P hS).2.1
  have h3notsig : 3 ∉ D.sig := by rw [hsig]; simp
  have hZL : Z ≤ L := by rw [hZdef]; exact inf_le_left.trans inf_le_right
  have hZP : Z ≤ P := by rw [hZdef]; exact inf_le_left.trans inf_le_left
  have hYP : Y ≤ P := hY8.mem.trans inf_le_left
  have hYcP : Y ≤ Subgroup.centralizer (P : Set G) := hY8.mem.trans inf_le_right
  have hZcP : Z ≤ Subgroup.centralizer (P : Set G) := hY8.zcentral
  have hEP : E ≤ P := by rw [hEdef]; exact sup_le hZP hYP
  have hEcP : E ≤ Subgroup.centralizer (P : Set G) := by rw [hEdef]; exact sup_le hZcP hYcP
  have hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G) := le_inf hEP hEcP
  have hEel : IsElemAbelian 3 E := by
    rw [hEdef]
    exact k89ooy_isElemAbelian_sup hZP hYP hZcP hYcP hZcard hY8.card
  have hdisjZY : Disjoint Z Y := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxZ, hxY⟩ := Subgroup.mem_inf.mp hx
    have hxYL : x ∈ Y ⊓ L := ⟨hxY, hZL hxZ⟩
    rw [disjoint_iff.mp hY8.disj] at hxYL
    exact hxYL
  have hZYnorm : Z ≤ Subgroup.normalizer (Y : Set G) :=
    (hZcP.trans (Subgroup.centralizer_le (fun y hy => hYP hy))).trans
      (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hYZnorm : Y ≤ Subgroup.normalizer (Z : Set G) :=
    (hYcP.trans (Subgroup.centralizer_le (fun z hz => hZP hz))).trans
      (Subgroup.centralizer_le_normalizer (Z : Set G))
  have hEcard9 : Nat.card E = 9 := by
    rw [hEdef, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Z Y
      hYZnorm hdisjZY, hZcard, hY8.card]
  have hEcard : Nat.card E = 3 ^ 2 := by rw [hEcard9]; norm_num
  have hsig1 : D.sig ⊆ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hS.mem)
  have hGamma : ¬ CFSG.Open.rankThreeGamma 1 3 E ≤ D.M := by
    intro hle
    exact hS.notStrong
      (h6_14 hsig1 3 Nat.prime_three (by norm_num) h3notsig P hS.sylow E hE hEel hEcard hle)
  obtain ⟨X, hXE, hXne, hXnorm⟩ := k89ooy_exists_of_not_le_gamma hGamma
  have hXcard9 : Nat.card X ∣ 9 := by
    rw [← hEcard9]
    exact Subgroup.card_dvd_of_le hXE
  have hXne1 : Nat.card X ≠ 1 := fun h1 => hXne (Subgroup.eq_bot_of_card_eq X h1)
  have hXneE : X ≠ E := fun h => hXnorm (by rw [h]; exact hY8.normE)
  have hXneZ : X ≠ Z := fun h => hXnorm (by rw [h]; exact hZnorm)
  have hXneY : X ≠ Y := fun h => hXnorm (by rw [h]; exact hY8.normY)
  have hXcard : Nat.card X = 3 := by
    have hdiv : Nat.card X ∣ 3 ^ 2 := by rwa [show (9 : ℕ) = 3 ^ 2 by norm_num] at hXcard9
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl | rfl
    · rw [hk] at hXne1; norm_num at hXne1
    · simpa using hk
    · exact absurd (Subgroup.eq_of_le_of_card_ge hXE (by rw [hEcard9, hk]; norm_num)) hXneE
  have hXnotleZ : ¬ X ≤ Z := fun h => hXneZ (Subgroup.eq_of_le_of_card_ge h (by rw [hXcard, hZcard]))
  obtain ⟨ω, hωX, hωZ⟩ := Set.not_subset.mp hXnotleZ
  have hω1 : ω ≠ 1 := fun h => hωZ (h ▸ Z.one_mem)
  have hω3 : orderOf ω = 3 := k89ooy_orderOf_eq_three hωX hXcard hω1
  have hzp : Subgroup.zpowers ω = X := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hωX) ?_
    rw [Nat.card_zpowers, hω3, hXcard]
  have hωsup : ω ∈ Z ⊔ Y := by rw [← hEdef]; exact hXE hωX
  obtain ⟨z, hzZ, y, hyY, hzy⟩ := r889_mem_sup_of_le_normalizer hZYnorm hωsup
  have hωY : ω ∉ Y := by
    intro hY
    apply hXneY
    rw [← hzp]
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hY)
      (by rw [Nat.card_zpowers, hω3, hY8.card])
  have hz1 : z ≠ 1 := by
    intro hz
    exact hωY (by rw [← hzy, hz, one_mul]; exact hyY)
  refine ⟨ω, ?_⟩
  refine ⟨hS, hPL, hE (hXE hωX), hω3, ⟨z, ?_, y, hY8.cent hyY, hzy.symm⟩, ?_, ?_, ?_,
    hY8.sylow3, hY8.normP, hY8.zcentral⟩
  · rw [← hZdef]; exact hzZ
  · rw [← hZdef]; exact hωZ
  ·
    intro hωC
    have hyC : y ∈ CentOverO2 D.M L := hY8.cent hyY
    have hzC : z ∈ CentOverO2 D.M L := by
      have hz_eq : z = ω * y⁻¹ := by rw [← hzy]; group
      rw [hz_eq]
      exact (CentOverO2 D.M L).mul_mem hωC ((CentOverO2 D.M L).inv_mem hyC)
    obtain ⟨hzM, hzcomm⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hzC
    have hzcb : z ∈ centralizerBar D.M L :=
      mem_centralizerBar_iff.mpr ⟨hzM, fun l hl => by
        simpa [commutatorElement_def] using hzcomm l hl⟩
    have hzL : z ∈ L := hZL hzZ
    have hzO : z ∈ CFSG.Open.pCoreOf 2 L :=
      inf_centralizerBar_le_pCore_of_center_bar2 (P := D.M) (L := L)
        (r889_center_eq_bot_of_isSpor_J2 hJ2) ⟨hzcb, hzL⟩
    have hz3 : orderOf z = 3 := k89ooy_orderOf_eq_three hzZ hZcard hz1
    have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    obtain ⟨k, hk⟩ := hO2 ⟨z, hzO⟩
    have hdvd : orderOf z ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hk
    rw [hz3] at hdvd
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  ·
    intro hC
    have hCeq : Subgroup.centralizer (Subgroup.zpowers ω : Set G) =
        Subgroup.centralizer ({ω} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hK_le : Subgroup.centralizer (Subgroup.zpowers ω : Set G) ≤ D.M := hCeq.le.trans hC
    have hPK : P ≤ Subgroup.centralizer (Subgroup.zpowers ω : Set G) := by
      rw [hzp]
      exact (Subgroup.le_centralizer_iff (H := P) (K := X)).mpr (hXE.trans hEcP)
    have hKC : Subgroup.centralizer (Subgroup.zpowers ω : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers ω : Set G) :=
      Subgroup.centralizer_le_normalizer _
    have hKnorm : (Subgroup.centralizer (Subgroup.zpowers ω : Set G)).subgroupOf
        (Subgroup.normalizer (Subgroup.zpowers ω : Set G)) |>.Normal :=
      Subgroup.normal_subgroupOf_centralizer_normalizer (Subgroup.zpowers ω : Set G)
    have hPK' : IsSylowOf 3 P (Subgroup.centralizer (Subgroup.zpowers ω : Set G)) :=
      hY8.sylow3.of_le hPK le_top
    obtain ⟨S, hS⟩ := hPK'.exists_sylow_eq_subgroupOf
    have hM : (S : Subgroup ↥(Subgroup.centralizer (Subgroup.zpowers ω : Set G))).map
        (Subgroup.centralizer (Subgroup.zpowers ω : Set G)).subtype = P := by
      rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPK]
    have hfr := eq_sup_normalizer_of_sylow hKC hKnorm S
    rw [hM] at hfr
    have hC_le : Subgroup.normalizer (Subgroup.zpowers ω : Set G) ≤ D.M := by
      rw [hfr]
      exact sup_le hK_le (inf_le_left.trans hY8.normP)
    exact hXnorm (by rw [← hzp]; exact hC_le)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

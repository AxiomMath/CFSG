module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Fixed

import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.GroupTheory.CoprimeCovering
import CFSG.GroupTheory.CoprimeNormalizerSup
import CFSG.GroupTheory.DedekindNormalizer
import CFSG.Quasithin.Background.C1PackImage
import CFSG.Quasithin.H13.NQTermAmbientQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barImage_kOf8103 {L B : Subgroup G} (hBL : B ≤ L) (hB : IsPGroup 3 B) :
    barImage L (F08.KOf8103 L B) = F08.KOf8103 ⊤ (barImage L B) :=
  barImage_derInf8_eq inf_le_left
    (barImage_inf_centralizer_eq hBL Nat.prime_three (by decide) hB)

theorem std8105_of_at (hK2 : KU45Syl3) {D : Data G} (hSg : SigmaStd D) (h61 : UC6.R6_1 D)
    {L P B : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (hB : F08.NotationB8103 L P n B) (h8103 : R8103At D L P p n) :
    Std8105 D L P B p n := by
  obtain ⟨hEven, ⟨hmod, hevenRank⟩, hstrong, -, -, -, -, hsylow3⟩ := h8103
  have hp : p.Prime := (D.sig_prime p hH.2.2.2.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hH.2.2.2.1).2
  have hdvd : p ∣ 2 ^ n + 1 := by
    have h1 : (p : ℤ) ∣ (2 : ℤ) ^ n + 1 := by
      have h2 : (p : ℤ) ∣ (-1 : ℤ) - (2 : ℤ) ^ n := Int.ModEq.dvd hmod
      have h3 : ((2 : ℤ) ^ n + 1) = -((-1 : ℤ) - (2 : ℤ) ^ n) := by ring
      rw [h3]
      exact dvd_neg.mpr h2
    exact_mod_cast h1
  have hn0 : n ≠ 0 := by
    intro hn
    rw [hn, pow_zero] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have htwo : 2 ≤ n := by
    rcases hEven with ⟨k, hk⟩
    omega
  exact ⟨hH, hB, hSg, h61, isU45_of_hyp8102 hH hEven, hEven, htwo, hp, hdvd, hevenRank,
    hstrong p hp hdvd, hsylow3, le_normalizer_of_hyp8102 hSg hK2 hH (isU45_of_hyp8102 hH hEven)⟩

private theorem commute_of_barImage {L P : Subgroup G} (hPL : P ≤ L) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hP : IsPGroup s P)
    (hc : ∀ x ∈ barImage L P, ∀ y ∈ barImage L P, x * y = y * x) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hsN : ¬ s ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hs hs2
  let Q : Subgroup ↥L := P.subgroupOf L
  let f : ↥Q →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp Q.subtype
  have hf : Function.Injective f :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hsN hP.comap_subtype
  let e : ↥P ≃* ↥Q := (Subgroup.subgroupOfEquivOfLe hPL).symm
  let g : ↥P →* Bar2 L := f.comp e.toMonoidHom
  have hg : Function.Injective g := hf.comp e.injective
  have hmem : ∀ z : ↥P, g z ∈ barImage L P := by
    intro z
    exact Subgroup.mem_map_of_mem _ (e z).2
  intro x hx y hy
  have hxyP : (⟨x * y, P.mul_mem hx hy⟩ : ↥P) = ⟨y * x, P.mul_mem hy hx⟩ := by
    apply hg
    rw [show (⟨x * y, P.mul_mem hx hy⟩ : ↥P) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl,
      show (⟨y * x, P.mul_mem hy hx⟩ : ↥P) = ⟨y, hy⟩ * ⟨x, hx⟩ from rfl,
      map_mul, map_mul]
    exact hc (g ⟨x, hx⟩) (hmem ⟨x, hx⟩) (g ⟨y, hy⟩) (hmem ⟨y, hy⟩)
  exact congrArg Subtype.val hxyP

private theorem kOf8103_le_and_normalizer {L B : Subgroup G} (hBL : B ≤ L) :
    F08.KOf8103 L B ≤ L ∧ F08.KOf8103 L B ≤ L ⊓ centralizer (B : Set G) ∧
      (L ⊓ centralizer (B : Set G)) ≤ Subgroup.normalizer (F08.KOf8103 L B : Set G) ∧
      F08.KOf8103 L B ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
  have hKC : F08.KOf8103 L B ≤ L ⊓ centralizer (B : Set G) := by
    change CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (L ⊓ centralizer (B : Set G)) ≤ L ⊓ centralizer (B : Set G)
    exact Subgroup.map_subtype_le _
  have hKL : F08.KOf8103 L B ≤ L := hKC.trans inf_le_left
  have hC : (L ⊓ centralizer (B : Set G)) ≤
      Subgroup.normalizer (F08.KOf8103 L B : Set G) := by
    refine Subgroup.le_normalizer.trans ?_
    change _ ≤ Subgroup.normalizer
      (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (L ⊓ centralizer (B : Set G)) : Set G)
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _
  exact ⟨hKL, hKC, hC, hKL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)⟩

private theorem le_of_barImage_le_of_card_three {L K C B' : Subgroup G}
    (hB'L : B' ≤ L) (hB'card : Nat.card B' = 3) (hB'C : B' ≤ C)
    (hKC : K ≤ C) (hKN : K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G))
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (h : barImage L B' ≤ barImage L K) : B' ≤ K := by
  have hB3 : IsPGroup 3 B' := IsPGroup.of_card (n := 1) (by rw [hB'card, pow_one])
  have hsup : B' ≤ K ⊔ pCoreOf 2 L :=
    CFSG.Quasithin.C1Pack.le_sup_pCoreOf_of_barImage_le hB'L h
  have hDed : C ⊓ (K ⊔ pCoreOf 2 L) = K ⊔ (C ⊓ pCoreOf 2 L) :=
    CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hKC hKN
  have hBC : B' ≤ K ⊔ (C ⊓ pCoreOf 2 L) := by
    rw [← hDed]
    exact le_inf hB'C hsup
  refine CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card Nat.prime_three
    ?_ hB3 hBC ?_
  · exact inf_le_left.trans hCK
  · have hC2 : IsPGroup 2 ↥(C ⊓ pCoreOf 2 L) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L).to_le inf_le_right
    obtain ⟨k, hk⟩ := hC2.exists_card_eq
    rw [hk]
    intro h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

private theorem commutator_mem_inf_pCoreOf {L P K : Subgroup G} {x : ↥L} {y : Bar2 L}
    (hPL : P ≤ L) (hKL : K ≤ L) (hxK : (x : G) ∈ K)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hxy : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) x = y)
    (hy : y ∈ centralizer (barImage L P : Set (Bar2 L))) :
    ∀ r ∈ P, ⁅(x : G), r⁆ ∈ K ⊓ pCoreOf 2 L := by
  intro r hr
  have hxL : (x : G) ∈ L := hKL hxK
  have hrL : r ∈ L := hPL hr
  have hxrL : ⁅(x : G), r⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem hxL hrL) (L.inv_mem hxL)) (L.inv_mem hrL)
  have hxrK : ⁅(x : G), r⁆ ∈ K := by
    have hrx : r * (x : G) * r⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hPK hr) (x : G)).mp hxK
    have hEq : ⁅(x : G), r⁆ = (x : G) * (r * (x : G) * r⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hEq]
    exact K.mul_mem hxK (K.inv_mem hrx)
  refine ⟨hxrK, ?_⟩
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨⁅(x : G), r⁆, hxrL⟩ = 1 := by
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨⁅(x : G), r⁆, hxrL⟩ =
        ⁅(QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨(x : G), hxL⟩,
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨r, hrL⟩⁆ := by
      rw [show (⟨⁅(x : G), r⁆, hxrL⟩ : ↥L) = ⁅(⟨(x : G), hxL⟩ : ↥L), ⟨r, hrL⟩⁆ from rfl,
        map_commutatorElement]
    rw [h1, hxy]
    have hrbar : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨r, hrL⟩ ∈ barImage L P :=
      uc22p21c_mem_barImage.2 ⟨⟨r, hrL⟩, hr, rfl⟩
    have hcent := (Subgroup.mem_centralizer_iff.mp hy) _ hrbar
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcent.symm
  exact (CFSG.mem_openPCoreOf_iff ⟨⁅(x : G), r⁆, hxrL⟩).2
    ((QuotientGroup.eq_one_iff _).1 hker)

private theorem exists_mem_inf_centralizer_of_barImage {L P K : Subgroup G} {x : ↥L}
    {y : Bar2 L} (hPL : P ≤ L) (hKL : K ≤ L) (hxK : (x : G) ∈ K) (hP3 : IsPGroup 3 P)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hKN : K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G))
    (hxy : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) x = y)
    (hy : y ∈ centralizer (barImage L P : Set (Bar2 L))) :
    ∃ z : ↥L, (z : G) ∈ K ⊓ centralizer (P : Set G) ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) z = y := by
  let N0 : Subgroup G := K ⊓ pCoreOf 2 L
  have hN0K : N0 ≤ K := inf_le_left
  have hN0norm : (N0.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0K).2
      ((le_inf Subgroup.le_normalizer hKN).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hN02 : IsPGroup 2 N0 :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L).to_le inf_le_right
  have hN0solv : Group.IsSolvable ↥N0 := by
    haveI : Group.IsNilpotent ↥N0 := hN02.isNilpotent
    infer_instance
  have hPN : P ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hPL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hN0P : P ≤ Subgroup.normalizer (N0 : Set G) :=
    (le_inf hPK hPN).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcop : Nat.Coprime (Nat.card N0) (Nat.card P) :=
    IsPGroup.coprime_card_of_ne 2 3 (by norm_num) N0 P hN02 hP3
  obtain ⟨nn, hnnN0, hxnCK⟩ :=
    CFSG.GroupTheory.exists_mul_mem_inf_centralizer_of_commutator_mem hN0K hN0norm hN0P
      hN0solv hcop hxK (commutator_mem_inf_pCoreOf hPL hKL hxK hPK hxy hy)
  refine ⟨⟨(x : G) * nn, hKL hxnCK.1⟩, hxnCK, ?_⟩
  have hnnL : nn ∈ L := hKL hnnN0.1
  have hnn_core : ⟨nn, hnnL⟩ ∈ CFSG.pCore 2 ↥L :=
    (CFSG.mem_openPCoreOf_iff ⟨nn, hnnL⟩).1 hnnN0.2
  have hnn_ker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨nn, hnnL⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 hnn_core
  have h1 : (⟨(x : G) * nn, hKL hxnCK.1⟩ : ↥L) = x * ⟨nn, hnnL⟩ := rfl
  rw [h1, map_mul, hxy, hnn_ker, mul_one]

private theorem dvd_card_of_barImage_order_p {L CK : Subgroup G} {p : ℕ} {y : Bar2 L}
    (hy : orderOf y = p) (hyCK : y ∈ barImage L CK) (hCKL : CK ≤ L) :
    p ∣ Nat.card CK := by
  have hpdvd_bar : p ∣ Nat.card (barImage L CK) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyCK)
    rwa [Nat.card_zpowers, hy] at h
  have hcard : Nat.card CK =
      Nat.card (barImage L CK) * Nat.card ↥(CK.subgroupOf L ⊓ CFSG.pCore 2 ↥L) := by
    have h1 := CFSG.GroupTheory.CoprimeTransport.card_eq_card_map_mk_mul_card_inf
      (N := CFSG.pCore 2 ↥L) (CK.subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCKL).toEquiv, show
      (CK.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
        barImage L CK from rfl] at h1
    exact h1
  rw [hcard]
  exact hpdvd_bar.trans (dvd_mul_right _ _)

private theorem exists_order_p_mem_barImage_inf_centralizer (hK1 : KU45Lines) (hCP : KU45CentP)
    {D : Data G} {L P B : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n) :
    ∃ y : Bar2 L, orderOf y = p ∧
      y ∈ barImage L (F08.KOf8103 L B ⊓ centralizer (P : Set G)) := by
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  obtain ⟨hKL, -, hCK, hKN⟩ := kOf8103_le_and_normalizer hBL
  let Pbar := barImage L P
  have hBbar : F08.NotationB8103 ⊤ Pbar n (barImage L B) :=
    (notationB8103_barImage_iff hPL hP3 hBP).2 s.notB
  obtain ⟨hPbar, hPidx⟩ :=
    isPGroup_barImage_of_isSylowOf (L := L) Nat.prime_three s.hyp.2.2.2.2
  obtain ⟨Dbar, hDbarK, hDbarCard, hDbarCent⟩ :=
    hCP (Bar2 L) n s.isU45 p s.prime s.dvd Pbar hPbar hPidx (barImage L B) hBbar
  have hKbar : barImage L (F08.KOf8103 L B) = F08.KOf8103 ⊤ (barImage L B) :=
    barImage_kOf8103 hBL hB3
  haveI : Fact p.Prime := ⟨s.prime⟩
  obtain ⟨yD, hyD⟩ := exists_prime_orderOf_dvd_card' (G := ↥Dbar) p (by rw [hDbarCard])
  have hy : orderOf (yD : Bar2 L) = p := (Subgroup.orderOf_coe yD).trans hyD
  have hyK : (yD : Bar2 L) ∈ barImage L (F08.KOf8103 L B) := by
    rw [hKbar]
    exact hDbarK yD.2
  obtain ⟨xL, hxK, hxy⟩ := uc22p21c_mem_barImage.1 hyK
  have hcommP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a :=
    commute_of_barImage hPL Nat.prime_three (by norm_num) hP3
      (hK1 (Bar2 L) n s.isU45 Pbar hPbar hPidx).1
  have hPcent : P ≤ centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcommP b (hBP hb) a ha
  have hPK : P ≤ Subgroup.normalizer (F08.KOf8103 L B : Set G) :=
    (le_inf hPL hPcent).trans hCK
  have hyCent : (yD : Bar2 L) ∈ centralizer (Pbar : Set (Bar2 L)) := hDbarCent yD.2
  obtain ⟨z, hzCK, hzy⟩ :=
    exists_mem_inf_centralizer_of_barImage hPL hKL hxK hP3 hPK hKN hxy hyCent
  exact ⟨yD, hy, uc22p21c_mem_barImage.2 ⟨z, hzCK, hzy⟩⟩

private theorem exists_order_p_centralizing (hK1 : KU45Lines) (hCP : KU45CentP) {D : Data G}
    {L P B : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n) :
    ∃ D₀ : Subgroup G, D₀ ≤ F08.KOf8103 L B ∧ Nat.card D₀ = p ∧
      D₀ ≤ centralizer (P : Set G) := by
  obtain ⟨y, hy, hybarCK⟩ := exists_order_p_mem_barImage_inf_centralizer hK1 hCP s
  haveI : Fact p.Prime := ⟨s.prime⟩
  have hBL : B ≤ L := s.notB.2.1.trans s.hyp.2.2.2.2.le
  have hKL : F08.KOf8103 L B ≤ L := (kOf8103_le_and_normalizer hBL).1
  let CK : Subgroup G := F08.KOf8103 L B ⊓ centralizer (P : Set G)
  have hCKL : CK ≤ L := by
    change F08.KOf8103 L B ⊓ centralizer (P : Set G) ≤ L
    exact (inf_le_left : F08.KOf8103 L B ⊓ centralizer (P : Set G) ≤
      F08.KOf8103 L B).trans hKL
  have hpdvd : p ∣ Nat.card CK := dvd_card_of_barImage_order_p hy hybarCK hCKL
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥CK) p hpdvd
  refine ⟨Subgroup.zpowers (c : G), ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.1 c.2).1
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc]
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.1 c.2).2

private theorem exists_lines_B (hK1 : KU45Lines) {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) :
    ∃ B' : Subgroup G, F08.NotationB8103 L P n B' ∧ B' ≠ B ∧ B' ≤ F08.KOf8103 L B ∧
      ∀ Y : Subgroup G, F08.NotationB8103 L P n Y → Y = B ∨ Y = B' := by
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  obtain ⟨hKL, hKC, hCK, hKN⟩ := kOf8103_le_and_normalizer hBL
  let Pbar := barImage L P
  have hBbar : F08.NotationB8103 ⊤ Pbar n (barImage L B) :=
    (notationB8103_barImage_iff hPL hP3 hBP).2 s.notB
  obtain ⟨hPbar, hPidx⟩ :=
    isPGroup_barImage_of_isSylowOf (L := L) Nat.prime_three s.hyp.2.2.2.2
  have hcomm := (hK1 (Bar2 L) n s.isU45 Pbar hPbar hPidx).1
  obtain ⟨B1, hB1le, hB1not, hB1ne, hB1all⟩ :=
    (hK1 (Bar2 L) n s.isU45 Pbar hPbar hPidx).2 (barImage L B) hBbar
  obtain ⟨B', hB'P, hB'bar⟩ :=
    exists_barImage_eq hPL Nat.prime_three (by norm_num) hP3 hB1not.2.1
  have hB'not : F08.NotationB8103 L P n B' :=
    (notationB8103_barImage_iff hPL hP3 hB'P).1 (by rw [hB'bar]; exact hB1not)
  have hne : B' ≠ B := by
    intro heq
    exact hB1ne (by rw [← hB'bar, heq])
  have hKbar : barImage L (F08.KOf8103 L B) = F08.KOf8103 ⊤ (barImage L B) :=
    barImage_kOf8103 hBL hB3
  have hPcomm := commute_of_barImage hPL Nat.prime_three (by norm_num) hP3 hcomm
  have hPcent : P ≤ centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hPcomm b (hBP hb) a ha
  have hB'cent : B' ≤ centralizer (B : Set G) := hB'P.trans hPcent
  have hB'C : B' ≤ L ⊓ centralizer (B : Set G) := le_inf (hB'P.trans hPL) hB'cent
  have hbarle : barImage L B' ≤ barImage L (F08.KOf8103 L B) := by
    rw [hB'bar, hKbar]
    exact hB1le
  have hle : B' ≤ F08.KOf8103 L B :=
    le_of_barImage_le_of_card_three (hB'P.trans hPL) hB'not.1 hB'C hKC hKN hCK hbarle
  refine ⟨B', hB'not, hne, hle, ?_⟩
  intro Y hY
  have hYbar : F08.NotationB8103 ⊤ Pbar n (barImage L Y) :=
    (notationB8103_barImage_iff hPL hP3 hY.2.1).2 hY
  rcases hB1all (barImage L Y) hYbar with h | h
  · exact Or.inl (eq_of_barImage_eq hPL Nat.prime_three (by norm_num) hP3 hY.2.1 hBP h)
  · exact Or.inr (eq_of_barImage_eq hPL Nat.prime_three (by norm_num) hP3 hY.2.1 hB'P
      (h.trans hB'bar.symm))

private theorem pRank_sup_kOf8103_eq {L B B' : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hBL : B ≤ L) (hB'L : B' ≤ L) (hB3 : IsPGroup 3 B)
    (hB'3 : IsPGroup 3 B') :
    Open.pRank p (F08.KOf8103 L B ⊔ F08.KOf8103 L B') =
      Open.pRank p (F08.KOf8103 ⊤ (barImage L B) ⊔ F08.KOf8103 ⊤ (barImage L B')) := by
  have hKL : F08.KOf8103 L B ≤ L := (kOf8103_le_and_normalizer hBL).1
  have hK'L : F08.KOf8103 L B' ≤ L := (kOf8103_le_and_normalizer hB'L).1
  have hKbar : barImage L (F08.KOf8103 L B) = F08.KOf8103 ⊤ (barImage L B) :=
    barImage_kOf8103 hBL hB3
  have hK'bar : barImage L (F08.KOf8103 L B') = F08.KOf8103 ⊤ (barImage L B') :=
    barImage_kOf8103 hB'L hB'3
  have hsup : barImage L (F08.KOf8103 L B ⊔ F08.KOf8103 L B') =
      F08.KOf8103 ⊤ (barImage L B) ⊔ F08.KOf8103 ⊤ (barImage L B') := by
    calc barImage L (F08.KOf8103 L B ⊔ F08.KOf8103 L B')
        = ((F08.KOf8103 L B ⊔ F08.KOf8103 L B').subgroupOf L).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := rfl
      _ = ((F08.KOf8103 L B).subgroupOf L ⊔ (F08.KOf8103 L B').subgroupOf L).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
            rw [Subgroup.subgroupOf_sup hKL hK'L]
      _ = ((F08.KOf8103 L B).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⊔
            ((F08.KOf8103 L B').subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
            Subgroup.map_sup _ _ _
      _ = barImage L (F08.KOf8103 L B) ⊔ barImage L (F08.KOf8103 L B') := rfl
      _ = F08.KOf8103 ⊤ (barImage L B) ⊔ F08.KOf8103 ⊤ (barImage L B') := by
            rw [hKbar, hK'bar]
  have hN : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 ↥L) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L) hp hp2
  have hrank1 := CFSG.PreuniquenessRankFour.Helpers.pRank_quotient_map_of_coprime_normal
    p hp (CFSG.pCore 2 ↥L) hN ((F08.KOf8103 L B ⊔ F08.KOf8103 L B').subgroupOf L)
  have hrank1' : Open.pRank p (barImage L (F08.KOf8103 L B ⊔ F08.KOf8103 L B')) =
      Open.pRank p ((F08.KOf8103 L B ⊔ F08.KOf8103 L B').subgroupOf L) := by
    rw [show barImage L (F08.KOf8103 L B ⊔ F08.KOf8103 L B') =
      ((F08.KOf8103 L B ⊔ F08.KOf8103 L B').subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl]
    exact hrank1
  have hrank2 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective
    p hp L.subtype L.subtype_injective
    ((F08.KOf8103 L B ⊔ F08.KOf8103 L B').subgroupOf L)
  rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hKL hK'L)] at hrank2
  rw [hrank2, ← hrank1']
  exact congrArg (Open.pRank p) hsup

private theorem two_le_pRank_sup_kOf8103 (hGR : KU45GenRank) {D : Data G}
    {L P B B' : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n) (hB'P : B' ≤ P)
    (hB'not : F08.NotationB8103 L P n B') (hne : B' ≠ B) :
    2 ≤ Open.pRank p (F08.KOf8103 L B ⊔ F08.KOf8103 L B') := by
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB'L : B' ≤ L := hB'P.trans hPL
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  have hB'3 : IsPGroup 3 B' := hP3.to_le hB'P
  let Pbar := barImage L P
  have hBbar : F08.NotationB8103 ⊤ Pbar n (barImage L B) :=
    (notationB8103_barImage_iff hPL hP3 hBP).2 s.notB
  have hB'bar : F08.NotationB8103 ⊤ Pbar n (barImage L B') :=
    (notationB8103_barImage_iff hPL hP3 hB'P).2 hB'not
  have hBbarne : barImage L B ≠ barImage L B' := by
    intro h
    exact hne (eq_of_barImage_eq hPL Nat.prime_three (by norm_num) hP3 hBP hB'P h).symm
  obtain ⟨hPbar, hPidx⟩ :=
    isPGroup_barImage_of_isSylowOf (L := L) Nat.prime_three s.hyp.2.2.2.2
  have hgr := hGR (Bar2 L) n s.isU45 p s.prime s.dvd Pbar hPbar hPidx
    (barImage L B) (barImage L B') hBbar hB'bar hBbarne
  have hp2 : p ≠ 2 := (D.sig_prime p s.hyp.2.2.2.1).2
  rw [pRank_sup_kOf8103_eq s.prime hp2 hBL hB'L hB3 hB'3]
  exact hgr

theorem exists_lines8105 (hK1 : KU45Lines) (hCP : KU45CentP) (hGR : KU45GenRank) {D : Data G}
    {L P B : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n) :
    ∃ B' D₀ : Subgroup G, Lines8105 L P B B' D₀ p n := by
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hBP : B ≤ P := s.notB.2.1
  obtain ⟨hPbar, hPidx⟩ :=
    isPGroup_barImage_of_isSylowOf (L := L) Nat.prime_three s.hyp.2.2.2.2
  have hcomm := (hK1 (Bar2 L) n s.isU45 (barImage L P) hPbar hPidx).1
  obtain ⟨B', hB'not, hne, hle, hlines⟩ := exists_lines_B hK1 s
  obtain ⟨D₀, hD₀le, hD₀card, hD₀cent⟩ := exists_order_p_centralizing hK1 hCP s
  have hB'P : B' ≤ P := hB'not.2.1
  refine ⟨B', D₀, ?_⟩
  exact ⟨commute_of_barImage hPL Nat.prime_three (by norm_num) hP3 hcomm,
    hB'not, hne, hle, hlines, hD₀le, hD₀card, hD₀cent,
    two_le_pRank_sup_kOf8103 hGR s hB'P hB'not hne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

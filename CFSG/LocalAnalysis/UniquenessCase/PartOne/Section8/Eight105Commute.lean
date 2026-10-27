module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105PStruct
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.GroupTheory.PerfectNormalConjugate
import CFSG.GroupTheory.DihedralQuotientNormalizer
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.GLTheoremA.S8.Close
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_of_le_normalizer_of_isL2 {K X D : Subgroup G} {m : ℕ}
    (hK : ⁅K, K⁆ = K) (hL2 : IsL2 (Bar2 K) m) (hXK : X ≤ K)
    (hKX : K ≤ normalizer (X : Set G)) (hDX : D ≤ X) (hD3 : Nat.card D = 3) : X = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  have hXnorm : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  haveI := hXnorm
  have hDK : D ≤ K := hDX.trans hXK
  have hD3K : Nat.card (D.subgroupOf K) = 3 := by
    rw [← hD3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  have hDsub_le : D.subgroupOf K ≤ X.subgroupOf K := Subgroup.subgroupOf_mono K hDX
  have hDsub_p : IsPGroup 3 ↥(D.subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by simpa using hD3K)
  have hdisj : Disjoint (D.subgroupOf K) (CFSG.pCore 2 ↥K) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hDsub_p CFSG.pCore_isPGroup
  have hDnot : ¬ D.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    intro hle
    have hbot : D.subgroupOf K = ⊥ := by
      have h := hdisj.eq_bot
      rwa [inf_eq_left.mpr hle] at h
    rw [hbot, Subgroup.card_bot] at hD3K
    omega
  rcases CFSG.GroupTheory.le_or_sup_eq_top_of_normal_of_isSimpleGroup_quotient
      (N := CFSG.pCore 2 ↥K) (K := X.subgroupOf K) hsimple with hle | hsup
  · exact absurd (hDsub_le.trans hle) hDnot
  · have hP : IsPGroup 2 (↥K ⧸ X.subgroupOf K) := by
      let q : ↥K →* (↥K ⧸ X.subgroupOf K) := QuotientGroup.mk' (X.subgroupOf K)
      have hmap : (CFSG.pCore 2 ↥K).map q = ⊤ := by
        have h := congrArg (Subgroup.map q) hsup
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
          Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _), bot_sup_eq] at h
        exact h
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥K).map q) := CFSG.pCore_isPGroup.map q
      rw [hmap] at hp
      exact hp.of_equiv Subgroup.topEquiv
    haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
    have htop : X.subgroupOf K = ⊤ :=
      CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect
        (p := 2) (X.subgroupOf K) hP
    exact le_antisymm hXK (Subgroup.subgroupOf_eq_top.mp htop)

private lemma le_ncl {N X : Subgroup G} (hXN : X ≤ N) : X ≤ ncl N X := by
  intro x hx
  rw [ncl]
  exact Subgroup.subset_closure ⟨1, N.one_mem, x, hx, by simp⟩

private lemma ncl_le_self {N X : Subgroup G} (hXN : X ≤ N) : ncl N X ≤ N := by
  rw [ncl]
  refine (Subgroup.closure_le N).mpr ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact N.mul_mem (N.mul_mem hg (hXN hx)) (N.inv_mem hg)

private lemma le_normalizer_ncl (N X : Subgroup G) :
    N ≤ normalizer (ncl N X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold ncl
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨h, hh, x, hx, rfl⟩, rfl⟩
    exact ⟨g * h, N.mul_mem hg hh, x, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨h, hh, x, hx, rfl⟩
    refine ⟨(g⁻¹ * h) * x * (g⁻¹ * h)⁻¹,
      ⟨g⁻¹ * h, N.mul_mem (N.inv_mem hg) hh, x, hx, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private lemma ncl_eq_nclIn {N X : Subgroup G} (hXN : X ≤ N) :
    ncl N X = CFSG.AGLEmbedding.nclIn N X := by
  apply le_antisymm
  · rw [ncl]
    refine (Subgroup.closure_le (CFSG.AGLEmbedding.nclIn N X)).mpr ?_
    rintro y ⟨g, hg, x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.AGLEmbedding.le_normalizer_nclIn N X hg) x).mp
      (CFSG.AGLEmbedding.le_nclIn hXN hx)
  · refine CFSG.AGLEmbedding.nclIn_le ?_ ?_ ?_
    · exact le_ncl hXN
    · exact ncl_le_self hXN
    · exact le_normalizer_ncl N X

private lemma ncl_eq_normalClosure_map {N X : Subgroup G} (hXN : X ≤ N) :
    ncl N X =
      (Subgroup.normalClosure ((X.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype := by
  rw [ncl_eq_nclIn hXN]
  rfl

private lemma ncl_mono_left {K N X : Subgroup G} (hKN : K ≤ N) :
    ncl K X ≤ ncl N X := by
  rw [ncl, ncl]
  refine Subgroup.closure_mono ?_
  rintro y ⟨g, hg, x, hx, rfl⟩
  exact ⟨g, hKN hg, x, hx, rfl⟩

theorem kOf8103_le_ncl {D : Data G} {L P B B' D₀ H N : Subgroup G} {p n : ℕ}
    (c : Ctx8105 D L P B B' D₀ H N p n) : F08.KOf8103 L B ≤ ncl N B' := by
  let K : Subgroup G := F08.KOf8103 L B
  have hB'K : B' ≤ K := c.le
  have hB'N : B' ≤ N := hB'K.trans (c.memH.2.2.1.trans c.memN.2)
  have hKN : K ≤ N := c.memH.2.2.1.trans c.memN.2
  have hperf : ⁅K, K⁆ = K := by
    haveI : Group.IsPerfect ↥K := isPerfect_derInf8 (L ⊓ centralizer (B : Set G))
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hXK : ncl K B' ≤ K := by
    rw [ncl_eq_nclIn hB'K]
    exact CFSG.AGLEmbedding.nclIn_le_self K B'
  have hKX : K ≤ normalizer (ncl K B' : Set G) := by
    rw [ncl_eq_nclIn hB'K]
    exact CFSG.AGLEmbedding.le_normalizer_nclIn K B'
  have hB'X : B' ≤ ncl K B' := by
    rw [ncl_eq_nclIn hB'K]
    exact CFSG.AGLEmbedding.le_nclIn hB'K
  have hXeq : ncl K B' = K :=
    eq_of_le_normalizer_of_isL2 hperf c.notB.2.2 hXK hKX hB'X c.notB'.1
  calc F08.KOf8103 L B = ncl K B' := hXeq.symm
    _ ≤ ncl N B' := ncl_mono_left hKN


private lemma pRank_subgroupOf_eq {N X : Subgroup G} (hXN : X ≤ N) :
    Open.pRank 3 (X.subgroupOf N : Subgroup ↥N) = Open.pRank 3 X := by
  calc Open.pRank 3 (X.subgroupOf N : Subgroup ↥N)
      = Open.pRank 3 (⊤ : Subgroup ↥(X.subgroupOf N)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
    _ = Open.pRank 3 (⊤ : Subgroup ↥X) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
          (Subgroup.subgroupOfEquivOfLe hXN)
    _ = Open.pRank 3 X := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup X).symm

private lemma not_three_dvd_card_relPPrimeCore (N : Subgroup G) :
    ¬ 3 ∣ Nat.card (relPPrimeCore 3 N) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_three N)

private lemma pRank_sup_relPPrimeCore_le_one {N X : Subgroup G} (hXN : X ≤ N)
    (hXrank : Open.pRank 3 X ≤ 1) :
    Open.pRank 3 (X ⊔ relPPrimeCore 3 N) ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let I : Subgroup G := relPPrimeCore 3 N
  haveI hInormal : (I.subgroupOf N).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      Nat.prime_three N
  let π : ↥N →* ↥N ⧸ I.subgroupOf N := QuotientGroup.mk' (I.subgroupOf N)
  have hIN : I ≤ N := by
    change relPPrimeCore 3 N ≤ N
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hO3 : ¬ 3 ∣ Nat.card I := not_three_dvd_card_relPPrimeCore N
  have hker : ¬ 3 ∣ Nat.card ↥(MonoidHom.ker π) := by
    have hkerEq : π.ker = I.subgroupOf N := by
      dsimp [π]
      exact QuotientGroup.ker_mk' _
    rw [hkerEq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIN).toEquiv]
    exact hO3
  have hsub : (X ⊔ I).subgroupOf N = (X.subgroupOf N) ⊔ (I.subgroupOf N) :=
    Subgroup.subgroupOf_sup hXN hIN
  have hmapJoin : ((X ⊔ I).subgroupOf N).map π = (X.subgroupOf N).map π := by
    rw [hsub, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  calc Open.pRank 3 (X ⊔ I)
      = Open.pRank 3 ((X ⊔ I).subgroupOf N) :=
        (pRank_subgroupOf_eq (sup_le hXN hIN)).symm
    _ = Open.pRank 3 (((X ⊔ I).subgroupOf N).map π) :=
        (CFSG.pRank_map_eq_of_not_dvd_card_ker π (QuotientGroup.mk'_surjective _)
          Nat.prime_three hker _).symm
    _ = Open.pRank 3 ((X.subgroupOf N).map π) := by rw [hmapJoin]
    _ = Open.pRank 3 (X.subgroupOf N) :=
        CFSG.pRank_map_eq_of_not_dvd_card_ker π (QuotientGroup.mk'_surjective _)
          Nat.prime_three hker _
    _ = Open.pRank 3 X := pRank_subgroupOf_eq hXN
    _ ≤ 1 := hXrank

private lemma P_le_of_mem_calK8104 {D : Data G} {P K H : Subgroup G}
    (hH : H ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.calK8104 D P K) :
    P ≤ H := by
  intro p hp
  have hprod : p ∈ ((pCoreOf 2 H : Set G) * ((K ⊓ H : Subgroup G) : Set G)) * P := by
    refine ⟨1, ?_, p, hp, by simp⟩
    exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  change p ∈ (H : Set G)
  rw [hH.2.2.2]
  exact hprod

private lemma pRank_P_subgroupOf_le_three {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    Open.pRank 3 (P.subgroupOf N : Subgroup ↥N) ≤ 3 := by
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hPM : P ≤ D.M := hPH.trans c.memH.1
  have hPrank : Open.pRank 3 P ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hPM).trans
      (pRank_le_three_of_evenRank D c.evenRank Nat.prime_three (by norm_num))
  calc Open.pRank 3 (P.subgroupOf N : Subgroup ↥N)
      = Open.pRank 3 (⊤ : Subgroup ↥(P.subgroupOf N)) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
    _ = Open.pRank 3 (⊤ : Subgroup ↥P) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
          (Subgroup.subgroupOfEquivOfLe hPN)
    _ = Open.pRank 3 P := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup P).symm
    _ ≤ 3 := hPrank

private lemma pRank_ncl_of_normalClosure {D : Data G} {L P B B' D₀ H N Z : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) (hZN : Z ≤ N)
    (hres : Open.pRank 3
      (Subgroup.normalClosure ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)) = 1) :
    Open.pRank 3 (ncl N Z) = 1 := by
  rw [ncl_eq_normalClosure_map hZN]
  have hmap : Open.pRank 3
      ((Subgroup.normalClosure ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype) =
      Open.pRank 3 (Subgroup.normalClosure
        ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)) := by
    calc Open.pRank 3
          ((Subgroup.normalClosure ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype)
        = Open.pRank 3 (⊤ : Subgroup ↥((Subgroup.normalClosure
            ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype)) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
      _ = Open.pRank 3 (⊤ : Subgroup ↥(Subgroup.normalClosure
            ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N))) :=
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num)
            (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).symm
      _ = Open.pRank 3 (Subgroup.normalClosure
            ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)) :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
  rw [hmap]
  exact hres

private lemma isSylowOf_P_subgroupOf {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf N) (⊤ : Subgroup ↥N) := by
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N]
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN,
    Subgroup.map_top, Subgroup.range_subtype] using
    (CFSG.ABGLocalTools.IsSylowOf.of_le c.sylow3 hPN le_top)

private lemma pRank_ncl_aux (h332 : UCK.K332ThreeAb) {D : Data G}
    {L P B B' D₀ H N Z : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (hZ : Z = B ∨ Z = B') : Open.pRank 3 (ncl N Z) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZP : Z ≤ P := by
    rcases hZ with h | h
    · rw [h]; exact c.notB.2.1
    · rw [h]; exact c.notB'.2.1
  have hZcard : Nat.card Z = 3 := by
    rcases hZ with h | h
    · rw [h]; exact c.notB.1
    · rw [h]; exact c.notB'.1
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hZN : Z ≤ N := hZP.trans hPN
  have hNtop : N ≠ ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.isTwoLocal_ne_top D.standing.simple D.standing.nonab
      c.memN.1.1
  have hNK : CFSG.Open.IsKGroup ↥N := D.standing.kProper.isKGroup N hNtop
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf N) (⊤ : Subgroup ↥N) :=
    isSylowOf_P_subgroupOf c
  have hΩ : ∀ x ∈ (P.subgroupOf N : Subgroup ↥N), x ^ 3 = 1 →
      ∀ y ∈ (P.subgroupOf N : Subgroup ↥N), y ^ 3 = 1 → x * y = y * x := by
    intro x hx _ y hy _
    apply Subtype.ext
    simpa using c.abelian (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy)
  have hSrank : Open.pRank 3 (P.subgroupOf N : Subgroup ↥N) ≤ 3 :=
    pRank_P_subgroupOf_le_three c
  have hZsub : (Z.subgroupOf N : Subgroup ↥N) ≤ P.subgroupOf N :=
    Subgroup.subgroupOf_mono N hZP
  have hZcard' : Nat.card (Z.subgroupOf N : Subgroup ↥N) = 3 := by
    rw [← hZcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv
  have hwc : CFSG.ASVolI.ChIJK.IsWeaklyClosedIn (Z.subgroupOf N) (P.subgroupOf N) := by
    intro g hle
    let y : G := ((g⁻¹ : ↥N) : G)
    have hy : y ∈ N := (g⁻¹).2
    have hleG : Z.map (MulAut.conj y).toMonoidHom ≤ P := by
      have hm := Subgroup.map_mono (f := N.subtype) hle
      rw [CFSG.conjugate] at hm
      rwa [CFSG.map_subgroupOf_map_conj_eq hZN g⁻¹,
        Subgroup.map_subgroupOf_eq_of_le hPN] at hm
    have hweak := weaklyClosed c hZ hy hleG
    exact Subgroup.map_injective N.subtype_injective (by
      rw [CFSG.conjugate, CFSG.map_subgroupOf_map_conj_eq hZN g⁻¹, hweak,
        Subgroup.map_subgroupOf_eq_of_le hZN])
  have hres : Open.pRank 3
      (Subgroup.normalClosure ((Z.subgroupOf N : Subgroup ↥N) : Set ↥N)) = 1 :=
    h332 (↥N) hNK (P.subgroupOf N) hS hΩ hSrank (Z.subgroupOf N) hZsub hZcard' hwc
  exact pRank_ncl_of_normalClosure c hZN hres

theorem pRank_ncl (h332 : UCK.K332ThreeAb) {D : Data G} {L P B B' D₀ H N Z : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) (hZ : Z = B ∨ Z = B') :
    Open.pRank 3 (ncl N Z) = 1 :=
  pRank_ncl_aux h332 c hZ


private lemma false_of_three_dvd_card_inf_ncl (h332 : UCK.K332ThreeAb) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    (h3dvd : 3 ∣ Nat.card ↥(ncl N B ⊓ ncl N B')) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hBN : B ≤ N := c.notB.2.1.trans hPN
  have hB'N : B' ≤ N := c.notB'.2.1.trans hPN
  have hN1N : ncl N B ≤ N := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.nclIn_le_self N B
  have hN2N : ncl N B' ≤ N := by
    rw [ncl_eq_nclIn hB'N]
    exact CFSG.AGLEmbedding.nclIn_le_self N B'
  have hN1rank : Open.pRank 3 (ncl N B) = 1 := pRank_ncl h332 c (Or.inl rfl)
  have hN2rank : Open.pRank 3 (ncl N B') = 1 := pRank_ncl h332 c (Or.inr rfl)
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ncl N B ⊓ ncl N B')) 3 h3dvd
  let E : Subgroup G := Subgroup.zpowers (e : G)
  have hEcard : Nat.card E = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, he]
  have hEint : E ≤ ncl N B ⊓ ncl N B' := Subgroup.zpowers_le.mpr e.2
  have hEN1 : E ≤ ncl N B := hEint.trans inf_le_left
  have hEN2 : E ≤ ncl N B' := hEint.trans inf_le_right
  have hBN1 : B ≤ ncl N B := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.le_nclIn hBN
  have hB'N2 : B' ≤ ncl N B' := by
    rw [ncl_eq_nclIn hB'N]
    exact CFSG.AGLEmbedding.le_nclIn hB'N
  obtain ⟨h, hhN1, hEh⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime
      (p := 3) (H := ncl N B) (A := E) (B := B) hN1rank.le hEN1 hBN1 hEcard c.notB.1
  obtain ⟨k, hkN2, hEk⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime
      (p := 3) (H := ncl N B') (A := E) (B := B') hN2rank.le hEN2 hB'N2 hEcard c.notB'.1
  let y : G := k * h⁻¹
  have hyN : y ∈ N := N.mul_mem (hN2N hkN2) (N.inv_mem (hN1N hhN1))
  have hmap : (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      E.map (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext z
    change (k * h⁻¹) * (h * z * h⁻¹) * (k * h⁻¹)⁻¹ = k * z * k⁻¹
    group
  have hB'eq : B' = B.map (MulAut.conj y).toMonoidHom := by
    rw [← hEk, ← hEh]
    exact hmap.symm
  have hweak := weaklyClosed c (Or.inl rfl) hyN (hB'eq.symm ▸ c.notB'.2.1)
  exact c.ne (hB'eq.trans hweak)

private lemma not_three_dvd_card_inf_ncl (h332 : UCK.K332ThreeAb) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ¬ 3 ∣ Nat.card ↥(ncl N B ⊓ ncl N B') := by
  intro h3dvd
  exact false_of_three_dvd_card_inf_ncl h332 c h3dvd

private theorem commutator_ncl_le (h332 : UCK.K332ThreeAb) {D : Data G}
    {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ⁅ncl N B, ncl N B'⁆ ≤ relPPrimeCore 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hBN : B ≤ N := c.notB.2.1.trans hPN
  have hB'N : B' ≤ N := c.notB'.2.1.trans hPN
  have hN1N : ncl N B ≤ N := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.nclIn_le_self N B
  have hN2N : ncl N B' ≤ N := by
    rw [ncl_eq_nclIn hB'N]
    exact CFSG.AGLEmbedding.nclIn_le_self N B'
  have hN1norm : N ≤ normalizer (ncl N B : Set G) := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.le_normalizer_nclIn N B
  have hN2norm : N ≤ normalizer (ncl N B' : Set G) := by
    rw [ncl_eq_nclIn hB'N]
    exact CFSG.AGLEmbedding.le_normalizer_nclIn N B'
  have hcomm : ⁅ncl N B, ncl N B'⁆ ≤ ncl N B ⊓ ncl N B' :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.commutator_le_inf_of_le_normalizer
      (K := ncl N B) (S := ncl N B') (hN2N.trans hN1norm) (hN1N.trans hN2norm)
  have h3not : ¬ 3 ∣ Nat.card ↥(ncl N B ⊓ ncl N B') :=
    not_three_dvd_card_inf_ncl h332 c
  have hNormal : ((ncl N B ⊓ ncl N B').subgroupOf N).Normal := by
    have hNnorm : N ≤ normalizer ((ncl N B ⊓ ncl N B' : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hN1norm hx, hN2norm hx⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := ncl N B ⊓ ncl N B') (K := N) (inf_le_left.trans hN1N)).mpr hNnorm
  have hcop : Nat.Coprime 3 (Nat.card ↥(ncl N B ⊓ ncl N B')) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3not
  exact hcomm.trans
    (CFSG.GroupTheory.le_relPPrimeCore_of_normal_coprime (p := 3)
      (N := ncl N B ⊓ ncl N B') (H := N) Nat.prime_three
      (inf_le_left.trans hN1N) hNormal hcop)

private lemma le_normalizer_sup_relPPrimeCore_of_commutator_le {N K A : Subgroup G}
    (hAN : A ≤ N) (hcomm : ⁅A, K⁆ ≤ relPPrimeCore 3 N) :
    A ≤ normalizer ((K ⊔ relPPrimeCore 3 N : Subgroup G) : Set G) := by
  let I : Subgroup G := relPPrimeCore 3 N
  have hIN : I ≤ N := by
    change relPPrimeCore 3 N ≤ N
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hInorm : N ≤ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIN).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three N)
  intro g hg
  have hgN : g ∈ N := hAN hg
  have hgI : I.map (MulAut.conj g).toMonoidHom = I :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hInorm hgN)
  have hgK : K.map (MulAut.conj g).toMonoidHom ≤ K ⊔ I := by
    rintro y ⟨k, hk, rfl⟩
    have hc : ⁅g, k⁆ ∈ I := hcomm (Subgroup.commutator_mem_commutator hg hk)
    change g * k * g⁻¹ ∈ K ⊔ I
    have hgk : g * k * g⁻¹ = ⁅g, k⁆ * k := by
      rw [commutatorElement_def]
      group
    rw [hgk]
    exact (K ⊔ I).mul_mem ((le_sup_right : I ≤ K ⊔ I) hc)
      ((le_sup_left : K ≤ K ⊔ I) hk)
  have hmap : (K ⊔ I).map (MulAut.conj g).toMonoidHom ≤ K ⊔ I := by
    rw [Subgroup.map_sup, hgI]
    exact sup_le hgK le_sup_right
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]))

private lemma sup_ncl_relPPrimeCore_le_normalizer (h332 : UCK.K332ThreeAb) {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    ncl N B ⊔ relPPrimeCore 3 N ≤
      normalizer ((F08.KOf8103 L B ⊔ relPPrimeCore 3 N : Subgroup G) : Set G) := by
  let K : Subgroup G := F08.KOf8103 L B
  let I : Subgroup G := relPPrimeCore 3 N
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hBN : B ≤ N := c.notB.2.1.trans hPN
  have hB'N : B' ≤ N := c.notB'.2.1.trans hPN
  have hN1N : ncl N B ≤ N := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.nclIn_le_self N B
  have hN2N : ncl N B' ≤ N := by
    rw [ncl_eq_nclIn hB'N]
    exact CFSG.AGLEmbedding.nclIn_le_self N B'
  have hIN : I ≤ N := by
    change relPPrimeCore 3 N ≤ N
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hK_N2 : K ≤ ncl N B' := kOf8103_le_ncl c
  have hKN : K ≤ N := hK_N2.trans hN2N
  have hN1norm : N ≤ normalizer (ncl N B : Set G) := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.le_normalizer_nclIn N B
  have hInorm : N ≤ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIN).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three N)
  have hcommN1K : ⁅ncl N B, K⁆ ≤ I :=
    (Subgroup.commutator_mono le_rfl hK_N2).trans (commutator_ncl_le h332 c)
  have hcommIN1 : ⁅I, ncl N B⁆ ≤ I :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.commutator_le_of_le_normalizer
      (K := I) (S := ncl N B) (hN1N.trans hInorm)
  have hcommIK : ⁅I, K⁆ ≤ I :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.commutator_le_of_le_normalizer
      (K := I) (S := K) (hKN.trans hInorm)
  exact sup_le
    (le_normalizer_sup_relPPrimeCore_of_commutator_le hN1N hcommN1K)
    (le_normalizer_sup_relPPrimeCore_of_commutator_le hIN hcommIK)

private lemma mem_normalizer_sup_of_mem_normalizer_B {D : Data G}
    {L P B B' D₀ H N : Subgroup G} {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n)
    {u : G} (huM : u ∈ D.M) (huN : u ∈ N) (huB : u ∈ normalizer (B : Set G)) :
    u ∈ normalizer ((F08.KOf8103 L B ⊔ relPPrimeCore 3 N : Subgroup G) : Set G) := by
  let K : Subgroup G := F08.KOf8103 L B
  let I : Subgroup G := relPPrimeCore 3 N
  have hIN : I ≤ N := by
    change relPPrimeCore 3 N ≤ N
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have huL : u ∈ normalizer (L : Set G) := c.normal huM
  have huC : u ∈ normalizer (centralizer (B : Set G) : Set G) :=
    CFSG.Walter.Huppert.normalizer_le_normalizer_centralizer B huB
  have huLC : u ∈ normalizer ((L ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨huL, huC⟩
  have huK : u ∈ normalizer (K : Set G) := by
    have h :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
        (L ⊓ centralizer (B : Set G)) huLC
    simpa only [K, F08.KOf8103, F08.DerInf8, CFSG.perfectResidual] using h
  have huI : u ∈ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIN).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three N) huN
  exact CFSG.Walter.Huppert.mem_normalizer_sup huK huI

private lemma mem_normalizer_sup_of_mem_inf {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) {W : Subgroup G} {x : G}
    (hxM : x ∈ D.M) (hxN : x ∈ N) (hWM : W ≤ D.M ⊓ N)
    (hxW : x ∈ normalizer (W : Set G))
    (hWnorm : W ≤ normalizer
      ((F08.KOf8103 L B ⊔ relPPrimeCore 3 N : Subgroup G) : Set G))
    (hWrank : Open.pRank 3 W ≤ 1) (hBW : B ≤ W) :
    x ∈ normalizer ((F08.KOf8103 L B ⊔ relPPrimeCore 3 N : Subgroup G) : Set G) := by
  let K : Subgroup G := F08.KOf8103 L B
  let I : Subgroup G := relPPrimeCore 3 N
  have hxBW : B.map (MulAut.conj x).toMonoidHom ≤ W := by
    rintro y ⟨b, hb, rfl⟩
    change x * b * x⁻¹ ∈ W
    exact (Subgroup.mem_normalizer_iff.mp hxW b).mp (hBW hb)
  have hAcard : Nat.card (B.map (MulAut.conj x).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, c.notB.1]
  obtain ⟨w, hwW, hwx⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime
      (p := 3) (H := W) (A := B.map (MulAut.conj x).toMonoidHom) (B := B)
      hWrank hxBW hBW hAcard c.notB.1
  let u : G := w * x
  have huH : u ∈ D.M ⊓ N := (D.M ⊓ N).mul_mem (hWM hwW) ⟨hxM, hxN⟩
  have huB : u ∈ normalizer (B : Set G) := by
    have hcomp : (MulAut.conj u).toMonoidHom =
        (MulAut.conj w).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
      ext z
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply]
      dsimp [u]
      group
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change B.map (MulAut.conj u).toMonoidHom = B
    rw [hcomp, ← Subgroup.map_map]
    exact hwx
  have huNorm : u ∈ normalizer ((K ⊔ I : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_normalizer_B c huH.1 huH.2 huB
  have hwNorm : w⁻¹ ∈ normalizer ((K ⊔ I : Subgroup G) : Set G) :=
    hWnorm (W.inv_mem hwW)
  have hxeq : x = w⁻¹ * u := by
    dsimp [u]
    group
  rw [hxeq]
  exact (normalizer ((K ⊔ I : Subgroup G) : Set G)).mul_mem hwNorm huNorm

theorem inf_le_normalizer (h332 : UCK.K332ThreeAb) {D : Data G} {L P B B' D₀ H N : Subgroup G}
    {p n : ℕ} (c : Ctx8105 D L P B B' D₀ H N p n) :
    D.M ⊓ N ≤ normalizer ((F08.KOf8103 L B ⊔ relPPrimeCore 3 N : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := F08.KOf8103 L B
  let I : Subgroup G := relPPrimeCore 3 N
  let McapN : Subgroup G := D.M ⊓ N
  let W : Subgroup G := McapN ⊓ (ncl N B ⊔ I)
  have hPH : P ≤ H := P_le_of_mem_calK8104 c.memH
  have hPN : P ≤ N := hPH.trans c.memN.2
  have hBM : B ≤ D.M := c.notB.2.1.trans (hPH.trans c.memH.1)
  have hBN : B ≤ N := c.notB.2.1.trans hPN
  have hN1N : ncl N B ≤ N := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.nclIn_le_self N B
  have hIN : I ≤ N := by
    change relPPrimeCore 3 N ≤ N
    exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le N
  have hN1norm : N ≤ normalizer (ncl N B : Set G) := by
    rw [ncl_eq_nclIn hBN]
    exact CFSG.AGLEmbedding.le_normalizer_nclIn N B
  have hInorm : N ≤ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIN).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three N)
  have hJoinNorm : ncl N B ⊔ I ≤ normalizer ((K ⊔ I : Subgroup G) : Set G) :=
    sup_ncl_relPPrimeCore_le_normalizer h332 c
  have hN1rank : Open.pRank 3 (ncl N B) = 1 := pRank_ncl h332 c (Or.inl rfl)
  have hJoinRank : Open.pRank 3 (ncl N B ⊔ I) ≤ 1 :=
    pRank_sup_relPPrimeCore_le_one hN1N hN1rank.le
  have hWle : W ≤ ncl N B ⊔ I := inf_le_right
  have hWrank : Open.pRank 3 W ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hWle).trans hJoinRank
  have hWnorm : W ≤ normalizer ((K ⊔ I : Subgroup G) : Set G) := hWle.trans hJoinNorm
  have hBW : B ≤ W := by
    refine le_inf (le_inf hBM hBN) ?_
    exact (show B ≤ ncl N B from by
      rw [ncl_eq_nclIn hBN]
      exact CFSG.AGLEmbedding.le_nclIn hBN).trans le_sup_left
  intro x hxMcapN
  have hxM : x ∈ D.M := hxMcapN.1
  have hxN : x ∈ N := hxMcapN.2
  have hxJoin : x ∈ normalizer ((ncl N B ⊔ I : Subgroup G) : Set G) :=
    CFSG.Walter.Huppert.mem_normalizer_sup (hN1norm hxN) (hInorm hxN)
  have hxW : x ∈ normalizer (W : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := McapN) (K := ncl N B ⊔ I)
      ⟨Subgroup.le_normalizer hxMcapN, hxJoin⟩
  exact mem_normalizer_sup_of_mem_inf c hxMcapN.1 hxMcapN.2
    (by exact inf_le_left) hxW hWnorm hWrank hBW

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

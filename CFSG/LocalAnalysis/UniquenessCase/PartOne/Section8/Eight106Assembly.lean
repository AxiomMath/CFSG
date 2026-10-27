module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Fitting
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Normalize
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Inner
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65FrattiniWeak
public import CFSG.GH74.GLS.Balance.Bender.T59
public import CFSG.GH74.GLS.Balance.Bender.ExtSylow
public import CFSG.Quasithin.Background.I4Basic
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.GroupTheory.PRankLeOfSylowLe
public import CFSG.GroupTheory.Fitting.LayerProjection
import CFSG.LocalAnalysis.UniquenessCase.UC6M591Da

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

private lemma X_le_normalizer_fittingSubgroupOf (X : Subgroup G) :
    X ≤ normalizer (CFSG.fittingSubgroupOf X : Set G) := by
  have hR : (CFSG.fittingSubgroupOf X).subgroupOf X = fittingSubgroup ↥X := by
    dsimp only [CFSG.fittingSubgroupOf]
    exact comap_map_eq_self_of_injective X.subtype_injective (fittingSubgroup ↥X)
  have hRsub : ((CFSG.fittingSubgroupOf X).subgroupOf X).Normal := by
    rw [hR]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hRsub

private lemma V_inf_fittingSubgroupOf_eq_bot {X V : Subgroup G}
    (hX2 : pCoreOf 2 X = ⊥) (hV2 : IsPGroup 2 V) :
    V ⊓ CFSG.fittingSubgroupOf X = ⊥ := by
  have hF_odd : Odd (Nat.card (CFSG.fittingSubgroupOf X)) := odd_card_fittingSubgroupOf hX2
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card V) (Nat.card (CFSG.fittingSubgroupOf X)) := by
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hF_odd)
  exact Subgroup.inf_eq_bot_of_coprime hcop

private lemma X_inf_DM_le_normalizer_inf {D : Data G} (X : Subgroup G) :
    X ⊓ D.M ≤ normalizer (pCoreOf 2 D.M ⊓ X : Subgroup G) := by
  intro x hx
  have hxX : x ∈ X := hx.1
  have hxM : x ∈ D.M := hx.2
  have hxNormPCore : x ∈ normalizer (pCoreOf 2 D.M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)).1
      (CFSG.Quasithin.normal_pCoreOf_subgroupOf D.M) hxM
  have hxNormX : x ∈ normalizer (X : Set G) := by
    exact Subgroup.le_normalizer hxX
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxNormPCore, hxNormX⟩

private lemma X_inf_DM_le_normalizer_K {D : Data G} (B : Subgroup G) {L : Subgroup G}
    (hN : D.M ≤ normalizer (L : Set G)) :
    centralizer (B : Set G) ⊓ D.M ≤ normalizer (F08.KOf8103 L B : Set G) := by
  intro x hx
  have hxX : x ∈ centralizer (B : Set G) := hx.1
  have hxM : x ∈ D.M := hx.2
  have hxNL : x ∈ normalizer (L : Set G) := hN hxM
  have hxNX : x ∈ normalizer (centralizer (B : Set G) : Set G) := Subgroup.le_normalizer hxX
  have hxNLX : x ∈ normalizer ((L ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hxNL hxNX ⊢
    intro y
    exact ⟨fun h => ⟨(hxNL y).1 h.1, (hxNX y).1 h.2⟩,
           fun h => ⟨(hxNL y).2 h.1, (hxNX y).2 h.2⟩⟩
  have h :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
      (L ⊓ centralizer (B : Set G))
  simpa only [F08.KOf8103, F08.DerInf8, CFSG.perfectResidual] using h hxNLX

private lemma K_ne_bot_of_prime_dvd_card {K : Subgroup G} {p : ℕ}
    (hpK : p ∣ Nat.card K) (hp : p.Prime) : K ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hpK
  exact hp.ne_one (Nat.dvd_one.mp hpK)

private lemma ne_zero_of_two_pow_modEq_neg_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hMod : (2 : ℤ) ^ n ≡ -1 [ZMOD p]) : n ≠ 0 := by
  rintro rfl
  simp only [pow_zero] at hMod
  have h2 : ((p : ℤ) ∣ 2) := by
    have h := hMod.dvd
    rw [show (-1 : ℤ) - 1 = -2 by ring] at h
    exact dvd_neg.mp h
  have h2' : p ∣ 2 := by exact_mod_cast h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2')

private lemma two_le_of_even_of_ne_zero {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) : 2 ≤ n := by
  obtain ⟨k, rfl⟩ := hn
  omega

private lemma centralizer_ne_top_of_card_eq_three {D : Data G} {B : Subgroup G}
    (hB : Nat.card B = 3) : centralizer (B : Set G) ≠ ⊤ := by
  haveI : IsSimpleGroup G := D.standing.simple
  intro hX
  have hBZ : B ≤ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.mp hX
  have hZ : Subgroup.center G = ⊥ := by
    apply TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
    intro hcomm
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    exact hab (hcomm.is_comm.comm a b)
  rw [hZ, le_bot_iff] at hBZ
  rw [hBZ, Subgroup.card_bot] at hB
  omega

private lemma rank_bound_of_evenRank_eq_three (he : evenRank G = 3) :
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 → ∀ r : ℕ, r.Prime → r ≠ 2 →
      Open.pRank r (centralizer ({t} : Set G)) ≤ 3 := by
  intro t ht1 ht2 r hr hr2
  have ht : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1
    · exact h2
  have hloc : IsTwoLocal (centralizer ({t} : Set G)) :=
    CFSG.Quasithin.I4.isTwoLocal_centralizer ht
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 _ hloc).trans
    (le_of_eq he)

private lemma isMulCommutative_of_isSylowOf_three (hK1 : KU45Lines) {L P : Subgroup G}
    {n : ℕ} (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) :
    IsMulCommutative ↥P := by
  obtain ⟨hPbar, hPidx⟩ := isPGroup_barImage_of_isSylowOf Nat.prime_three hP
  have hcomm := (hK1 (Bar2 L) n hX (barImage L P) hPbar hPidx).1
  have hdisj : P ⊓ pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP.isPGroup
      (UC6S846.isPGroup_pCoreOf L)).eq_bot
  refine IsMulCommutative.of_comm fun x y => Subtype.ext ?_
  have hxL : (x : G) ∈ L := hP.le x.2
  have hyL : (y : G) ∈ L := hP.le y.2
  have hxb : uc22p21cPi L ⟨(x : G), hxL⟩ ∈ barImage L P :=
    uc22p21c_mem_barImage.2 ⟨⟨(x : G), hxL⟩, x.2, rfl⟩
  have hyb : uc22p21cPi L ⟨(y : G), hyL⟩ ∈ barImage L P :=
    uc22p21c_mem_barImage.2 ⟨⟨(y : G), hyL⟩, y.2, rfl⟩
  set c : G := (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ with hc
  have hcP : c ∈ P := by
    rw [hc]
    exact P.mul_mem (P.mul_mem (P.mul_mem x.2 y.2) (P.inv_mem x.2)) (P.inv_mem y.2)
  have hcL : c ∈ L := hP.le hcP
  have hker : (⟨c, hcL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change uc22p21cPi L ⟨c, hcL⟩ = 1
    have heq : uc22p21cPi L ⟨c, hcL⟩ = uc22p21cPi L (⟨(x : G), hxL⟩ * ⟨(y : G), hyL⟩ *
        ⟨(x : G), hxL⟩⁻¹ * ⟨(y : G), hyL⟩⁻¹) := by
      congr 1
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ hxb _ hyb]
    group
  have hc1 : c = 1 := by
    have hbot : c ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨hcP, ⟨⟨c, hcL⟩, hker, rfl⟩⟩
    exact Subgroup.mem_bot.1 hbot
  rw [hc] at hc1
  calc (x : G) * (y : G) =
        ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) * ((y : G) * (x : G)) := by group
    _ = (y : G) * (x : G) := by rw [hc1]; simp

private lemma isMulCommutative_of_isPGroup_le_centralizer {C P Q : Subgroup G}
    (hP : IsSylowOf 3 P C) (hPab : IsMulCommutative ↥P) (hQC : Q ≤ C) (hQ3 : IsPGroup 3 Q) :
    IsMulCommutative ↥Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQsub : IsPGroup 3 (Q.subgroupOf C) := hQ3.comap_subtype
  obtain ⟨P', hQP'⟩ := hQsub.exists_le_sylow
  have hP'syl : IsSylowOf 3 ((P' : Subgroup ↥C).map C.subtype) C := ⟨P', rfl⟩
  obtain ⟨k, -, hconj⟩ := hP.exists_mem_conj hP'syl
  have hP'ab : IsMulCommutative ↥((P' : Subgroup ↥C).map C.subtype) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    have ha : k⁻¹ * (a : G) * k ∈ P := (hconj (a : G)).1 a.2
    have hb : k⁻¹ * (b : G) * k ∈ P := (hconj (b : G)).1 b.2
    have h := congrArg (fun z : ↥P => (z : G))
      (hPab.is_comm.comm (⟨_, ha⟩ : ↥P) (⟨_, hb⟩ : ↥P))
    simp only [Subgroup.coe_mul] at h
    calc (a : G) * (b : G) =
          k * (k⁻¹ * (a : G) * k * (k⁻¹ * (b : G) * k)) * k⁻¹ := by group
      _ = k * (k⁻¹ * (b : G) * k * (k⁻¹ * (a : G) * k)) * k⁻¹ := by rw [h]
      _ = (b : G) * (a : G) := by group
  have hQP : Q ≤ (P' : Subgroup ↥C).map C.subtype := by
    intro x hx
    exact Subgroup.mem_map.2 ⟨⟨x, hQC hx⟩, hQP' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  refine IsMulCommutative.of_comm fun a b => ?_
  apply Subtype.ext
  have h := congrArg (fun z : ↥((P' : Subgroup ↥C).map C.subtype) => (z : G))
    (hP'ab.is_comm.comm (⟨(a : G), hQP a.2⟩ : _) (⟨(b : G), hQP b.2⟩ : _))
  simpa only [Subgroup.coe_mul] using h

private lemma inf_notationB8103_eq_bot {L P B Y : Subgroup G} {n : ℕ}
    (hB : F08.NotationB8103 L P n B) (hY : CFSG.Open.IsComponentOf Y (centralizer (B : Set G)))
    (hC3 : ∀ Q : Subgroup G, Q ≤ centralizer (B : Set G) → IsPGroup 3 Q →
      IsMulCommutative ↥Q) :
    B ⊓ Y = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbB, hbY⟩ := Subgroup.mem_inf.1 hb
  by_contra hbne
  have hb3 : b ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := B) (x := ⟨b, hbB⟩)
    rw [hB.1] at h
    simpa using congrArg Subtype.val h
  have hord : orderOf b = 3 := by
    have hdvd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hbne
    · exact h3
  have hcent : (⟨b, hbY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hyC : (y : G) ∈ centralizer (B : Set G) := hY.1 y.2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hyC) b hbB).symm
  have hordY : orderOf (⟨b, hbY⟩ : ↥Y) = 3 :=
    ((Subgroup.orderOf_coe (⟨b, hbY⟩ : ↥Y)).symm).trans hord
  have hz3 : IsPGroup 3 (Subgroup.zpowers (⟨b, hbY⟩ : ↥Y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordY]; norm_num)
  obtain ⟨S, hS⟩ := hz3.exists_le_sylow
  have hSimg : (S : Subgroup ↥Y).map Y.subtype ≤ centralizer (B : Set G) := by
    rintro - ⟨s, -, rfl⟩
    exact hY.1 s.2
  have hScomm_img : IsMulCommutative ↥((S : Subgroup ↥Y).map Y.subtype) :=
    hC3 _ hSimg (S.isPGroup'.map Y.subtype)
  let e := Subgroup.equivMapOfInjective (S : Subgroup ↥Y) Y.subtype Y.subtype_injective
  haveI hScomm : IsMulCommutative ↥(S : Subgroup ↥Y) := by
    refine IsMulCommutative.of_comm fun a c => e.injective ?_
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := ↥((S : Subgroup ↥Y).map Y.subtype))).comm (e a) (e c)
  have hmem : (⟨b, hbY⟩ : ↥Y) ∈ (S : Subgroup ↥Y) ⊓ Subgroup.center ↥Y :=
    ⟨hS (Subgroup.mem_zpowers _), hcent⟩
  rw [CFSG.LocalAnalysis.UniquenessCase.UCK.M591D.sylow_inf_center_eq_bot hY.2.2.1 S] at hmem
  exact hbne (Subgroup.mem_bot.mpr (Subtype.ext_iff.1 (Subgroup.mem_bot.1 hmem)))

private lemma card_le_three_of_isElemAbelian_le_component {L P B Y : Subgroup G} {n : ℕ}
    (hB : F08.NotationB8103 L P n B) (hPab : IsMulCommutative ↥P)
    (hPC : P ≤ centralizer (B : Set G))
    (hY : CFSG.Open.IsComponentOf Y (centralizer (B : Set G))) (hinf : B ⊓ Y = ⊥)
    (hRankC : Open.pRank 3 (centralizer (B : Set G)) ≤ 2) {E : Subgroup G} (hEY : E ≤ Y)
    (hEea : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 := by
  have hBC : B ≤ centralizer (B : Set G) := hB.2.1.trans hPC
  have hEC : E ≤ centralizer (B : Set G) := hEY.trans hY.1
  have hBmul : IsMulCommutative ↥B := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    have h := congrArg (fun z : ↥P => (z : G))
      (hPab.is_comm.comm (⟨(a : G), hB.2.1 a.2⟩ : ↥P) (⟨(b : G), hB.2.1 b.2⟩ : ↥P))
    simpa only [Subgroup.coe_mul] using h
  have hBpow : ∀ x ∈ B, x ^ 3 = 1 := by
    intro x hx
    have h := pow_card_eq_one' (G := B) (x := ⟨x, hx⟩)
    rw [hB.1] at h
    simpa using congrArg Subtype.val h
  have hFea : IsElemAbelian 3 (E ⊔ B) :=
    hEea.sup_of_commute ⟨hBmul, hBpow⟩
      (fun a ha b hb => ((Subgroup.mem_centralizer_iff.1 (hEC ha)) b hb).symm)
  have hdisj : Disjoint E B := by
    rw [disjoint_iff, eq_bot_iff]
    calc E ⊓ B ≤ Y ⊓ B := inf_le_inf hEY le_rfl
      _ = B ⊓ Y := inf_comm Y B
      _ = ⊥ := hinf
  have hBcent : B ≤ Subgroup.centralizer (E : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.1 (hEC hx)) b hb).symm
  have hnorm : B ≤ Subgroup.normalizer (E : Set G) :=
    hBcent.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  obtain ⟨k, hk⟩ := hEea.isPGroup.exists_card_eq
  have hFcard : Nat.card (E ⊔ B : Subgroup G) = 3 ^ (k + 1) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E B hnorm hdisj,
      hk, hB.1, pow_succ]
  have hle : k + 1 ≤ Open.pRank 3 (centralizer (B : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (sup_le hEC hBC) hFea hFcard
  have hk1 : k ≤ 1 := by omega
  calc Nat.card E = 3 ^ k := hk
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := by norm_num

private theorem pRank_three_le_one_of_r8103 (hK1 : KU45Lines) (hK2 : KU45Syl3) {D : Data G}
    {L P B Y : Subgroup G} {p n : ℕ} (h8103 : R8103At D L P p n)
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B)
    (hX : IsU45 (Bar2 L) n) (hY : CFSG.Open.IsComponentOf Y (centralizer (B : Set G))) :
    Open.pRank 3 Y ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSyl : IsSylowOf 3 P ⊤ := h8103.2.2.2.2.2.2.2
  have hPsylowM : IsSylowOf 3 P D.M :=
    hSyl.of_le (hH.2.2.2.2.le.trans (CFSG.Open.IsSubnormal.le hH.1.1)) le_top
  obtain ⟨A, hA⟩ := h8103.2.2.2.1
  have hAmem : A ∈ uniqueSet D.M := h8103.2.2.2.2.2.1 A hA
  have hPB : P ≤ centralizer (B : Set G) :=
    le_centralizer_of_notationB8103 hK2 hX hH.2.2.2.2 hB
  have hPsylowX : IsSylowOf 3 P (centralizer (B : Set G)) :=
    isSylowOf_three_centralizer_of_mem_uniqueSet hAmem hPsylowM hA.2.1 hPB
  obtain ⟨E9, hE9P, hE9ea, hE9card, hE9all⟩ :=
    exists_elemAbelian_nine hK2 hX hH.2.2.2.2
  have hboundP : ∀ F : Subgroup G, F ≤ P → CFSG.Open.IsElemAbelian 3 F → Nat.card F ≤ 9 := by
    intro F hFP hFea
    have hFE9 : F ≤ E9 := by
      intro x hx
      exact hE9all x (hFP hx) (hFea.2 x hx)
    exact (Subgroup.card_le_of_le hFE9).trans (le_of_eq hE9card)
  have hRankP : Open.pRank 3 P ≤ 2 := CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) hboundP
  have hRankX : Open.pRank 3 (centralizer (B : Set G)) ≤ 2 :=
    (CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hPB hPsylowX le_rfl).trans hRankP
  have hPab : IsMulCommutative ↥P := isMulCommutative_of_isSylowOf_three hK1 hX hH.2.2.2.2
  have hC3 : ∀ Q : Subgroup G, Q ≤ centralizer (B : Set G) → IsPGroup 3 Q →
      IsMulCommutative ↥Q :=
    fun Q hQC hQ => isMulCommutative_of_isPGroup_le_centralizer hPsylowX hPab hQC hQ
  have hinf : B ⊓ Y = ⊥ := inf_notationB8103_eq_bot hB hY hC3
  refine CFSG.SectionRank.pRank_le (by norm_num : 1 < 3) (k := 1) fun E hEY hEea => ?_
  have h3 := card_le_three_of_isElemAbelian_le_component hB hPab hPB hY hinf hRankX hEY hEea
  simpa using h3

private lemma dataFromR8103 {D : Data G} (hK2 : KU45Syl3) (hSg : SigmaStd D)
    {L P B : Subgroup G} {p n : ℕ} (h8103 : R8103At D L P p n)
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B) :
    Even n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD p] ∧ evenRank G = 3 ∧
    (∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M) ∧
    (¬ centralizer (B : Set G) ≤ D.M) ∧ IsU45 (Bar2 L) n ∧
    D.M ≤ normalizer (L : Set G) ∧ (p.Prime ∧ p ≠ 2 ∧ p ≠ 3) ∧ p ∣ 2 ^ n + 1 ∧
    IsStronglyPEmbedded p D.M := by
  have hEven : Even n := h8103.1
  have hMod : (2 : ℤ) ^ n ≡ -1 [ZMOD p] := h8103.2.1.1
  have he : evenRank G = 3 := h8103.2.1.2
  have hStr : ∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M :=
    h8103.2.2.1
  have hBM : ¬ centralizer (B : Set G) ≤ D.M :=
    h8103.2.2.2.2.2.2.1 B hB
  have hX : IsU45 (Bar2 L) n := isU45_of_hyp8102 hH hEven
  have hN : D.M ≤ normalizer (L : Set G) := le_normalizer_of_hyp8102 hSg hK2 hH hX
  have hp := prime_of_hyp8102 hSg hH
  have hpn : p ∣ 2 ^ n + 1 := by
    rw [Int.modEq_iff_dvd] at hMod
    have h := hMod
    rw [show -1 - (2 : ℤ) ^ n = -((2 : ℤ) ^ n + 1) by ring] at h
    have h' : ((p : ℤ) ∣ ((2 : ℤ) ^ n + 1)) := dvd_neg.mp h
    exact_mod_cast h'
  have hMp : IsStronglyPEmbedded p D.M := hStr p hp.1 hpn
  exact ⟨hEven, hMod, he, hStr, hBM, hX, hN, hp, hpn, hMp⟩

private lemma normalizerK_le_DM {D : Data G} {p : ℕ} [Fact p.Prime]
    (hMp : IsStronglyPEmbedded p D.M) {K : Subgroup G} (hKleM : K ≤ D.M)
    (hpK : p ∣ Nat.card K) (hp : p.Prime) :
    normalizer (K : Set G) ≤ D.M := by
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf p K
  have hQne : Q ≠ ⊥ := by
    intro h
    have hc := hQ.card_eq
    rw [h, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card K).factorization p :=
      hp.factorization_pos_of_dvd Nat.card_pos.ne' hpK
    exact (Nat.one_lt_pow hpos.ne' hp.one_lt).ne' hc.symm
  have hNQ : normalizer (Q : Set G) ≤ D.M :=
    hMp.normalizer_le hQne hQ.isPGroup (hQ.le.trans hKleM)
  have hNX : K ≤ normalizer (K : Set G) := Subgroup.le_normalizer
  have hNn : (K.subgroupOf (normalizer (K : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr le_rfl
  have hQin : CFSG.GH74.GLS.Balance.IsSylowIn p Q K :=
    CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_iff_isSylowOf.mpr hQ
  have hFr := CFSG.GH74.GLS.Balance.t59_frattini hNX hNn hQin
  exact hFr.trans (sup_le hKleM (inf_le_right.trans hNQ))

private lemma commutator_le_inf_of_mutual_normalizer {A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) _).mp (inv_mem ha))
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) _).mp hb) (inv_mem hb)

private lemma V_le_centralizer_F {D : Data G} {X V : Subgroup G}
    (hX2 : pCoreOf 2 X = ⊥) (hV2 : IsPGroup 2 V)
    (hV_le_X : V ≤ X) (hXinfM_norm_V : X ⊓ D.M ≤ normalizer (V : Set G))
    (hF_le_M : CFSG.fittingSubgroupOf X ≤ D.M) :
    V ≤ centralizer (CFSG.fittingSubgroupOf X : Set G) := by
  have hF_le_X : CFSG.fittingSubgroupOf X ≤ X := Subgroup.map_subtype_le (fittingSubgroup ↥X)
  have hF_le_inf : CFSG.fittingSubgroupOf X ≤ X ⊓ D.M := le_inf hF_le_X hF_le_M
  have hV_norm_F : V ≤ normalizer (CFSG.fittingSubgroupOf X : Set G) := by
    exact hV_le_X.trans (X_le_normalizer_fittingSubgroupOf X)
  have hF_norm_V : CFSG.fittingSubgroupOf X ≤ normalizer (V : Set G) := by
    exact hF_le_inf.trans hXinfM_norm_V
  have hcomm : ⁅V, CFSG.fittingSubgroupOf X⁆ ≤ V ⊓ CFSG.fittingSubgroupOf X :=
    commutator_le_inf_of_mutual_normalizer hV_norm_F hF_norm_V
  have hVinfF : V ⊓ CFSG.fittingSubgroupOf X = ⊥ := by
    exact V_inf_fittingSubgroupOf_eq_bot hX2 hV2
  rw [hVinfF] at hcomm
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (by simpa using hcomm)

private lemma kOf8103_facts {D : Data G} {L P B : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B) (hn0 : n ≠ 0)
    (hpn : p ∣ 2 ^ n + 1) (hMp : IsStronglyPEmbedded p D.M) (hp : p.Prime) :
    F08.KOf8103 L B ≤ centralizer (B : Set G) ∧ F08.KOf8103 L B ≤ D.M ∧
      ⁅F08.KOf8103 L B, F08.KOf8103 L B⁆ = F08.KOf8103 L B ∧
      p ∣ Nat.card (F08.KOf8103 L B) ∧ normalizer (F08.KOf8103 L B : Set G) ≤ D.M := by
  have hKleM : F08.KOf8103 L B ≤ D.M :=
    ((Subgroup.map_subtype_le _).trans inf_le_left).trans (CFSG.Open.IsSubnormal.le hH.1.1)
  haveI : Group.IsPerfect ↥(F08.KOf8103 L B) :=
    isPerfect_derInf8 (L ⊓ centralizer (B : Set G))
  have hpK : p ∣ Nat.card (F08.KOf8103 L B) := dvd_card_of_isL2 hn0 hB.2.2 hpn
  exact ⟨(Subgroup.map_subtype_le _).trans inf_le_right, hKleM,
    CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup, hpK,
    normalizerK_le_DM hMp hKleM hpK hp⟩

private lemma false_of_component {D : Data G} (hK1 : KU45Lines) (hK2 : KU45Syl3)
    (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch) (hKC : KComp8106)
    {L P B Y : Subgroup G} {p n : ℕ} (h8103 : R8103At D L P p n) [Fact p.Prime]
    (hH : F08.Hyp8102 D L P p n)
    (hB : F08.NotationB8103 L P n B) (hX : IsU45 (Bar2 L) n) (hEven : Even n) (hn0 : n ≠ 0)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) (hMp : IsStronglyPEmbedded p D.M)
    (hN : D.M ≤ normalizer (L : Set G)) (he : evenRank G = 3)
    (hX2 : pCoreOf 2 (centralizer (B : Set G)) = ⊥)
    (hKf : F08.KOf8103 L B ≤ centralizer (B : Set G) ∧ F08.KOf8103 L B ≤ D.M ∧
      ⁅F08.KOf8103 L B, F08.KOf8103 L B⁆ = F08.KOf8103 L B ∧
      p ∣ Nat.card (F08.KOf8103 L B) ∧ normalizer (F08.KOf8103 L B : Set G) ≤ D.M)
    (hY : CFSG.Open.IsComponentOf Y (centralizer (B : Set G))) (hYM : ¬ Y ≤ D.M)
    (hV2 : IsPGroup 2 (pCoreOf 2 D.M ⊓ centralizer (B : Set G) : Subgroup G))
    (hVY : ¬ pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≤ centralizer (Y : Set G)) : False := by
  obtain ⟨hKleX, hKleM, hKperf, hpK, hN_le_M⟩ := hKf
  have hVM : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≤ D.M :=
    inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hXV := X_inf_DM_le_normalizer_inf (D := D) (centralizer (B : Set G))
  have hXK := X_inf_DM_le_normalizer_K B hN
  have hXne := centralizer_ne_top_of_card_eq_three (D := D) hB.1
  have hXk : CFSG.Open.IsKGroup ↥(centralizer (B : Set G)) :=
    CFSG.Open.IsKProper.isKGroup D.standing.kProper _ hXne
  have hKY : F08.KOf8103 L B ≤ Y :=
    le_of_le_normalizer_isComponentOf hSch hXk hY hKleX hKperf
      (CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hB.2.2) hp2 hpK hMp hKleM hYM
      (le_normalizer_of_isComponentOf (rank_bound_of_evenRank_eq_three he) hXk hKleX hKperf hY)
  have hVK : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≤
      normalizer (F08.KOf8103 L B : Set G) := fun x hx => hXK ⟨hx.2, hVM hx⟩
  have hYne : Y ≠ ⊤ := fun h => hXne (top_le_iff.mp (by rw [← h]; exact hY.1))
  have hY3 : Open.pRank 3 Y ≤ 1 := pRank_three_le_one_of_r8103 hK1 hK2 h8103 hH hB hX hY
  have hY3' : CFSG.pRank 3 ↥Y ≤ 1 :=
    ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 Y).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y).symm).le.trans hY3
  exact false_of_kComp8106 hKC (CFSG.Open.IsKProper.isKGroup D.standing.kProper Y hYne) hY.2.2
    (odd_card_center_of_isComponentOf hX2 hY) hY3' (two_le_of_even_of_ne_zero hEven hn0) hEven
    hpn hKY hKperf hB.2.2 hMp hYM hpK hKleM (fun x hx => hXK ⟨hY.1 hx.1, hx.2⟩) hN_le_M hV2
    (le_normalizer_of_le_isComponentOf hY hKY hKperf
      (K_ne_bot_of_prime_dvd_card hpK Fact.out) inf_le_right hVK)
    hVK (fun x hx => hXV ⟨hY.1 hx.1, hx.2⟩) hVY

theorem r8106_at_of_inputs (hK1 : KU45Lines) (hK2 : KU45Syl3) (hK462 : UCK.K462)
    (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch) (hKC : KComp8106) {D : Data G}
    (hSg : SigmaStd D) {L P : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n)
    (h8103 : R8103At D L P p n) (h8105 : R8105.R8105At D L P n) :
    R8106At D L P n := by
  intro B hB
  by_contra hV
  obtain ⟨hEven, hMod, he, -, hBM, hX, hN, hp, hpn, hMp⟩ :=
    dataFromR8103 hK2 hSg h8103 hH hB
  haveI : Fact p.Prime := ⟨hp.1⟩
  have hn0 : n ≠ 0 := ne_zero_of_two_pow_modEq_neg_one hp.1 hp.2.1 hMod
  have hKf := kOf8103_facts hH hB hn0 hpn hMp hp.1
  have hX2 := pCoreOf_two_centralizer_eq_bot_at hK2 h8105 hH hX hB hBM hV
  have hV2 : IsPGroup 2 (pCoreOf 2 D.M ⊓ centralizer (B : Set G) : Subgroup G) :=
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 D.M).to_inf_left
  have hF_le_M : CFSG.fittingSubgroupOf (centralizer (B : Set G)) ≤ D.M :=
    (fittingSubgroupOf_le_centralizer_at hK2 hK462 hSg h8103 hH hB hX2).trans
      ((Subgroup.centralizer_le_normalizer _).trans hKf.2.2.2.2)
  have hXV := X_inf_DM_le_normalizer_inf (D := D) (centralizer (B : Set G))
  obtain ⟨Y, hY, hVY⟩ := exists_isComponentOf_not_le_centralizer hX2 inf_le_right hV2 hV
    (V_le_centralizer_F hX2 hV2 inf_le_right hXV hF_le_M)
  have hYM : ¬ Y ≤ D.M := fun h => hVY (le_centralizer_of_isComponentOf_le hX2 inf_le_right
    (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) hV2 hXV hY h)
  exact false_of_component hK1 hK2 hSch hKC h8103 hH hB hX hEven hn0 hp.2.1 hpn hMp hN he hX2 hKf
    hY hYM hV2 hVY

theorem r8106_of_inputs (hK1 : KU45Lines) (hK2 : KU45Syl3) (hK462 : UCK.K462)
    (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch) (hKC : KComp8106) {D : Data G}
    (hSg : SigmaStd D) (h8103 : F08.R8103 D) (h8105 : PartTwo.Inputs1719.PartOne.R8_105 D) :
    F08.R8106 D := by
  intro L P p n hH B hB
  exact r8106_at_of_inputs hK1 hK2 hK462 hSch hKC hSg hH (h8103 L P p n hH)
    (h8105 L P p n hH) B hB

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

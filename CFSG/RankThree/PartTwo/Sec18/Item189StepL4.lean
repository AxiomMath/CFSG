module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Omega
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step189MKOddL4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Case189iii M H c → Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 2)) →
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
      ¬ 2 ∣ (normalClosureIn M c ⊔ (M ⊓ n189 H)).relIndex M

variable {G : Type} [Group G] [Finite G]

theorem relIndex_inf_eq_mul189 {M K N : Subgroup G} (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G)) :
    (M ⊓ N).relIndex M = (K ⊔ (M ⊓ N)).relIndex M * (K ⊓ N).relIndex K := by
  have hle : K ⊔ (M ⊓ N) ≤ M := sup_le hKM inf_le_left
  have h1 := Subgroup.relIndex_mul_relIndex (M ⊓ N) (K ⊔ (M ⊓ N)) M le_sup_right hle
  have hn : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK
  have h2 := ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (K.subgroupOf M)
    ((M ⊓ N).subgroupOf M)
  rw [← Subgroup.subgroupOf_sup hKM inf_le_left, Subgroup.relIndex_subgroupOf hle,
    Subgroup.relIndex_subgroupOf hKM] at h2
  have h3 : (M ⊓ N).relIndex K = (K ⊓ N).relIndex K := by
    rw [← Subgroup.inf_relIndex_right (M ⊓ N) K]
    congr 1
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨⟨_, hN⟩, hK⟩ => ⟨hK, hN⟩, fun ⟨hK, hN⟩ => ⟨⟨hKM hK, hN⟩, hK⟩⟩
  rw [← h1, h2, h3, mul_comm]

theorem relIndex_inf_n189_eq_index189 {M H : Subgroup G} {c : G}
    (hθ : theta189 M H c ≤ n189 H) :
    (normalClosureIn M c ⊓ n189 H).relIndex (normalClosureIn M c) =
      ((((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map
        (alpha189 M H c)).subgroupOf (kAlpha189 M H c)).index := by
  have hker : (kToKAlpha189 M H c).ker ≤
      (normalClosureIn M c ⊓ n189 H).subgroupOf (normalClosureIn M c) := fun k hk => by
    rw [mem_ker_kToKAlpha189] at hk
    exact ⟨k.2, hθ hk⟩
  have hmap : ((normalClosureIn M c ⊓ n189 H).subgroupOf (normalClosureIn M c)).map
      (kToKAlpha189 M H c) =
      (((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map
        (alpha189 M H c)).subgroupOf (kAlpha189 M H c) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, (le_sup_right : normalClosureIn M c ≤ sk189 M H c) k.2⟩, hk, rfl⟩
    · rintro ⟨s, hs, hsy⟩
      refine ⟨⟨s, hs.1⟩, hs, Subtype.ext ?_⟩
      rw [coe_kToKAlpha189]
      exact hsy
  rw [Subgroup.relIndex, ← hmap, Subgroup.index_map_eq _ kToKAlpha189_surjective hker]

theorem le_sup_inf_n189_of_normalizer_le189 {A M H : Subgroup G} {c : G}
    (h : Sec18H G A M H c) (hrank : CFSG.Open.pRank 3 (normalClosureIn M c) = 1)
    (hcN : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ n189 H) :
    M ≤ normalClosureIn M c ⊔ (M ⊓ n189 H) := by
  intro m hm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 := pow_three_of_sec18H189 h
  have hc1 : c ≠ 1 := ne_one_of_pRank_eq_one189 hrank
  obtain ⟨P, hP, hcP⟩ := Sec20.exists_isSylowOf_le (Sec20.isPGroup_zpowers_of_pow_three hc3)
    (Subgroup.zpowers_le.mpr (Sec20.self_mem_normalClosureIn M c))
  obtain ⟨k, hk, n, hn, rfl⟩ :=
    exists_mul_of_isSylowOf hP (Sec20.le_normalizer_normalClosureIn M c) hm
  have hcPm : c ∈ P := hcP (Subgroup.mem_zpowers c)
  have hnc := conj_mem_zpowers_of_isSylowOf189 hrank.le hP hcPm hc3 hc1 hn
  have hnc' := conj_mem_zpowers_of_isSylowOf189 hrank.le hP hcPm hc3 hc1
    (Subgroup.inv_mem _ hn)
  rw [inv_inv] at hnc'
  have hnN : n ∈ n189 H := hcN (mem_normalizer_zpowers189 hnc hnc')
  have hkM : k ∈ M := normalClosureIn_le_of_sec18H189 h hk
  have hnM : n ∈ M := by
    have he : n = k⁻¹ * (k * n) := by group
    rw [he]
    exact M.mul_mem (M.inv_mem hkM) hm
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨hnM, hnN⟩)

theorem exists_orderOf_two_mem_kAlpha_normalizer189 {M H : Subgroup G} {c : G}
    (h2 : 2 ∣ Nat.card (kAlpha189 M H c)) :
    ∃ z ∈ kAlpha189 M H c ⊓
      Subgroup.normalizer (sAlpha189 M H c : Set (SKAlpha189 M H c)), orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := kAlpha189_normal M H c
  obtain ⟨P, hSP⟩ := (isPGroup_sAlpha189 M H c).exists_le_sylow
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup (SKAlpha189 M H c)) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hTsyl := hPsyl.inf_of_le_normalizer le_top
    (Subgroup.normalizer_eq_top_iff.mpr (kAlpha189_normal M H c)).ge
  have hTne : (P : Subgroup (SKAlpha189 M H c)) ⊓ kAlpha189 M H c ≠ ⊥ := by
    intro hbot
    have hc := hTsyl.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card (kAlpha189 M H c)).factorization 2 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2)
    have : 1 < 2 ^ (Nat.card (kAlpha189 M H c)).factorization 2 :=
      Nat.one_lt_two_pow hpos.ne'
    omega
  set T' : Subgroup P := (kAlpha189 M H c).subgroupOf P with hT'def
  have hT'n : T'.Normal := Subgroup.Normal.subgroupOf inferInstance _
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    apply hTne
    rw [eq_bot_iff]
    rintro y ⟨hyP, hyK⟩
    have : (⟨y, hyP⟩ : P) ∈ T' := hyK
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hnil : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hT'ne
  have hZ2 : IsPGroup 2 ↥(T' ⊓ Subgroup.center P) := P.isPGroup'.to_subgroup _
  have : Nontrivial ↥(T' ⊓ Subgroup.center P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr this).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T' ⊓ Subgroup.center P)) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((z : P) : SKAlpha189 M H c), ⟨(z.2.1 : (z : P) ∈ T'), ?_⟩, ?_⟩
  · refine mem_normalizer_of_mem_centralizer189 (Z := (P : Subgroup _)) hSP ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2.2 ⟨y, hy⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem card_kAlpha_of_l4_189 {M H : Subgroup G} {c : G}
    (e : ↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 2)) :
    Nat.card (kAlpha189 M H c) = 60 := by
  rw [Nat.card_congr e.toEquiv,
    Nat.card_congr (Sec4.projSLEquivPSL (GaloisField 2 2)).toEquiv,
    CFSG.Walter.psl2_even_card (by norm_num)]
  norm_num

theorem not_four_dvd_relIndex_of_l4_189 (h186 : Item186H) (h187 : Item187)
    {A M H : Subgroup G} {c : G} (h : Sec18H G A M H c) (h7 : Hyp187 A M H c)
    (e : ↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 2)) :
    ¬ 4 ∣ (normalClosureIn M c ⊓ n189 H).relIndex (normalClosureIn M c) := by
  rw [relIndex_inf_n189_eq_index189 (theta189_le_n189 h187 h h7)]
  set J := ((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map (alpha189 M H c)
  have hcard := card_kAlpha_of_l4_189 e
  obtain ⟨z, hz, hz2⟩ := exists_orderOf_two_mem_kAlpha_normalizer189 (M := M) (H := H) (c := c)
    (by rw [hcard]; norm_num)
  have hzJ : z ∈ J := kAlpha_inf_normalizer_le189
    (fun x hx => mem_n189_of_mem_normalizer_sAlpha h186 h187 h h7 hx) hz
  have h2 : 2 ∣ Nat.card (J.subgroupOf (kAlpha189 M H c)) := by
    have hw : orderOf (⟨⟨z, hz.1⟩, hzJ⟩ : ↥(J.subgroupOf (kAlpha189 M H c))) = 2 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact hz2
    rw [← hw]
    exact orderOf_dvd_natCard _
  have hmul := (J.subgroupOf (kAlpha189 M H c)).card_mul_index
  rw [hcard] at hmul
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := h2
  rw [ha, hb] at hmul
  have h8 : (8 : ℕ) ∣ 60 := Dvd.intro (b * a) (by rw [← hmul]; ring)
  norm_num at h8

theorem step189L4_of (h186 : Item186H) (h187 : Item187) (hMK : Step189MKOddL4) :
    Step189L4 := by
  intro G _ _ A M H c hset hiii ⟨e⟩
  have h := hset.toSec18H
  have h7 := hset.hyp187
  rw [relIndex_inf_eq_mul189 (normalClosureIn_le_of_sec18H189 h)
    (Sec20.le_normalizer_normalClosureIn M c)]
  have hodd : ¬ 2 ∣ (normalClosureIn M c ⊔ (M ⊓ n189 H)).relIndex M := by
    by_cases hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥
    · exact hMK G A M H c hset hiii ⟨e⟩ hO
    · rw [Subgroup.relIndex_eq_one.mpr (le_sup_inf_n189_of_normalizer_le189 h hset.pRank_eq
        (normalizer_zpowers_le189 h7 hO))]
      norm_num
  have hK4 := not_four_dvd_relIndex_of_l4_189 h186 h187 h h7 e
  intro h4
  have hcop : Nat.Coprime 4 ((normalClosureIn M c ⊔ (M ⊓ n189 H)).relIndex M) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact hK4 (hcop.dvd_of_dvd_mul_left h4)

end CFSG.RankThree.PartTwo.Sec18

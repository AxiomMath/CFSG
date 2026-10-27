module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

open scoped commutatorElement

private theorem k89o2_not_dvd_1080 {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) : ¬ q ∣ 1080 := by
  intro h
  have h' : q ∣ 2 ^ 3 * 3 ^ 3 * 5 := by simpa using h
  rcases hq.dvd_mul.mp h' with h1 | h5
  · rcases hq.dvd_mul.mp h1 with h2 | h3
    · have : q ≤ 2 := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
      omega
    · have : q ≤ 3 := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h3)
      omega
  · have : q ≤ 5 := Nat.le_of_dvd (by norm_num) h5
    omega

private theorem k89o2_card_Bar2_K {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    {ω : G} (hFacts : AllFacts889 D) (hω : Set889 D L P ω) :
    Nat.card (Bar2 (K889 L ω)) = 1080 := by
  obtain ⟨-, hZ, hAlt⟩ := (hFacts L P ω hω).alt6
  have hcard_quot :
      Nat.card (Bar2 (K889 L ω) ⧸ Subgroup.center (Bar2 (K889 L ω))) = 360 := by
    obtain ⟨e⟩ := hAlt
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Bar2 (K889 L ω)))
  rw [hZ, hcard_quot] at h
  norm_num at h
  exact h

private theorem k89o2_not_dvd_card_K {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} {ω : G} (hFacts : AllFacts889 D) (hω : Set889 D L P ω)
    {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q) : ¬ q ∣ Nat.card (K889 L ω) := by
  intro hqK
  have hcardK : Nat.card (K889 L ω) =
      Nat.card (Bar2 (K889 L ω)) * Nat.card (CFSG.pCore 2 ↥(K889 L ω)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcardK, k89o2_card_Bar2_K hFacts hω] at hqK
  have hqm : q ∣ Nat.card (CFSG.pCore 2 ↥(K889 L ω)) := by
    rcases hq.dvd_mul.mp hqK with h | h
    · exact (k89o2_not_dvd_1080 hq hq7 h).elim
    · exact h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(K889 L ω)))
  rw [hn] at hqm
  have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow hqm
  have : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
  omega

private theorem k89o2_pCoreOf_le_of_le_normal {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {I N : Subgroup G} (hIN : I ≤ N)
    (hInorm : N ≤ Subgroup.normalizer (I : Set G)) : pCoreOf p I ≤ pCoreOf p N := by
  have hpc_le_N : pCoreOf p I ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le p I).trans hIN
  refine CFSG.LieType.BorelTits.le_pCoreOf p hpc_le_N ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p I)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hpc_le_N]
  exact hInorm.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pCore p ↥I))

private theorem k89o2_centralizer_fitting_le {G : Type} [Group G] [Finite G] {I : Subgroup G}
    (hIsolv : Group.IsSolvable ↥I) :
    I ⊓ Subgroup.centralizer ((fittingSubgroup ↥I).map I.subtype : Set G) ≤
      (fittingSubgroup ↥I).map I.subtype := by
  intro x hx
  obtain ⟨hxI, hxcent⟩ := hx
  have hxcent' : (⟨x, hxI⟩ : ↥I) ∈
      Subgroup.centralizer (fittingSubgroup ↥I : Set ↥I) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxcent) y.val (Subgroup.mem_map_of_mem I.subtype hy)
  have hmem := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
    (G := ↥I) hIsolv hxcent'
  simpa using Subgroup.mem_map_of_mem I.subtype hmem

private theorem k89o2_pCoreOf_eq_bot_of_not_dvd {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {I : Subgroup G} (h : ¬ p ∣ Nat.card ↥I) : pCoreOf p I = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p (pCoreOf p I) := CFSG.LieType.BorelTits.pCoreOf_isPGroup p I
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hdvd : p ^ n ∣ Nat.card ↥I := by
    rw [← hn]
    exact Subgroup.card_dvd_of_le (CFSG.LieType.BorelTits.pCoreOf_le p I)
  have hn0 : n = 0 := by
    by_contra hn0
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    exact h ((dvd_pow_self p (Nat.pos_iff_ne_zero.mp hpos)).trans hdvd)
  rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]

private theorem k89o2_le_normalizer_fitting {G : Type} [Group G] [Finite G] {I : Subgroup G} :
    I ≤ Subgroup.normalizer ((fittingSubgroup ↥I).map I.subtype : Set G) := by
  have hle : (fittingSubgroup ↥I).map I.subtype ≤ I := Subgroup.map_subtype_le _
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  have hsub : ((fittingSubgroup ↥I).map I.subtype).subgroupOf I = fittingSubgroup ↥I := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective I.subtype_injective]
  rw [hsub]
  infer_instance

private theorem k89o2_commutator_le_left_of_le_normalizer {G : Type} [Group G]
    {I K : Subgroup G} (hK : K ≤ Subgroup.normalizer (I : Set G)) : ⁅I, K⁆ ≤ I := by
  refine Subgroup.commutator_le.mpr fun i hi k hk => ?_
  have hconj : k * i⁻¹ * k⁻¹ ∈ I :=
    (Subgroup.mem_normalizer_iff.mp (hK hk) i⁻¹).1 (I.inv_mem hi)
  have hcomm : ⁅i, k⁆ = i * (k * i⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hcomm]
  exact Subgroup.mul_mem _ hi hconj

private theorem k89o2_pCoreOf_eq_bot_of_prime_le_five {G : Type} [Group G] [Finite G]
    {I : Subgroup G} (hO2 : pCoreOf 2 I = ⊥) (h3 : ¬ 3 ∣ Nat.card ↥I)
    (h5 : ¬ 5 ∣ Nat.card ↥I) {p : ℕ} (hp : p.Prime) (hp5 : p ≤ 5) :
    pCoreOf p I = ⊥ := by
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p
  · exact hO2
  · exact k89o2_pCoreOf_eq_bot_of_not_dvd Nat.prime_three h3
  · exact absurd hp (by norm_num)
  · exact k89o2_pCoreOf_eq_bot_of_not_dvd Nat.prime_five h5

private theorem k89o2_eq_one_of_two_three {G : Type} [Group G] {x : G} {i j : ℕ}
    (h2 : x ^ (2 ^ i) = 1) (h3 : x ^ (3 ^ j) = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one h2
  have h1' : orderOf x ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ i) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h1')

private theorem k89o2_exists_z {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    {ω : G} (hF : Facts889 D L P ω) (hP : IsPGroup 3 P) :
    ∃ z : ↥(K889 L ω), orderOf z = 3 ∧ ZOf (P ⊓ L) = Subgroup.zpowers (z : G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥(K889 L ω)) z ∈ Subgroup.center (Bar2 (K889 L ω)) := by
  have hZP : IsPGroup 3 (ZOf (P ⊓ L)) :=
    hP.to_le ((inf_le_left : ZOf (P ⊓ L) ≤ P ⊓ L).trans inf_le_left)
  have hZK : ZOf (P ⊓ L) ≤ K889 L ω := (inf_le_left : ZOf (P ⊓ L) ≤ P ⊓ L).trans hF.qLe
  let π : ↥(K889 L ω) →* Bar2 (K889 L ω) := QuotientGroup.mk' (CFSG.pCore 2 ↥(K889 L ω))
  have hinj : ∀ w : ↥(K889 L ω), (w : G) ∈ ZOf (P ⊓ L) → π w = 1 → w = 1 := by
    intro w hw hπ
    obtain ⟨j, hj⟩ := hZP ⟨(w : G), hw⟩
    have hw2 : w ∈ CFSG.pCore 2 ↥(K889 L ω) := (QuotientGroup.eq_one_iff w).mp hπ
    obtain ⟨i, hi⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥(K889 L ω)) ⟨w, hw2⟩
    refine k89o2_eq_one_of_two_three (i := i) (j := j) ?_ ?_
    · simpa using congrArg Subtype.val hi
    · exact Subtype.ext (by simpa using congrArg Subtype.val hj)
  have hcen : ((ZOf (P ⊓ L)).subgroupOf (K889 L ω)).map π = Subgroup.center (Bar2 (K889 L ω)) :=
    hF.centerEq
  have hcard : Nat.card (Subgroup.center (Bar2 (K889 L ω))) = 3 := hF.alt6.2.1
  obtain ⟨c, hc⟩ : ∃ c : Subgroup.center (Bar2 (K889 L ω)), c ≠ 1 := by
    refine (Subgroup.ne_bot_iff_exists_ne_one).mp ?_
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hcmem : (c : Bar2 (K889 L ω)) ∈ ((ZOf (P ⊓ L)).subgroupOf (K889 L ω)).map π := by
    rw [hcen]; exact c.2
  obtain ⟨z, hzZ, hzc⟩ := Subgroup.mem_map.mp hcmem
  have hzZ' : (z : G) ∈ ZOf (P ⊓ L) := Subgroup.mem_subgroupOf.mp hzZ
  have hc1 : (c : Bar2 (K889 L ω)) ≠ 1 := fun h => hc (Subtype.ext h)
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hc1 (by rw [← hzc, map_one])
  have hc3 : (c : Bar2 (K889 L ω)) ^ 3 = 1 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center (Bar2 (K889 L ω))) c.2
    rw [hcard] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hz3 : z ^ 3 = 1 := by
    apply hinj
    · have : (z : G) ^ 3 ∈ ZOf (P ⊓ L) := Subgroup.pow_mem _ hzZ' 3
      simpa using this
    · rw [map_pow, hzc, hc3]
  have hord : orderOf z = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hz3 hz1
  refine ⟨z, hord, ?_, by show π z ∈ _; rw [hzc]; exact c.2⟩
  apply le_antisymm
  · intro w hw
    have hwK : w ∈ K889 L ω := hZK hw
    have hπw : π ⟨w, hwK⟩ ∈ Subgroup.center (Bar2 (K889 L ω)) := by
      rw [← hcen]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hw)
    have hgen : Subgroup.zpowers (c : Bar2 (K889 L ω)) = Subgroup.center (Bar2 (K889 L ω)) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcord : orderOf (c : Bar2 (K889 L ω)) = 3 := orderOf_eq_prime hc3 hc1
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.zpowers_le]; exact c.2
      · rw [Nat.card_zpowers, hcord, hcard]
    rw [← hgen] at hπw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hπw
    have hmem : (⟨w, hwK⟩ : ↥(K889 L ω)) * (z ^ j)⁻¹ = 1 := by
      apply hinj
      · have : w * ((z : G) ^ j)⁻¹ ∈ ZOf (P ⊓ L) :=
          Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hzZ' j))
        simpa using this
      · rw [map_mul, map_inv, map_zpow, hzc, hj]; simp
    have hw' : (⟨w, hwK⟩ : ↥(K889 L ω)) = z ^ j := mul_inv_eq_one.mp hmem
    have := congrArg Subtype.val hw'
    simp only [Subgroup.coe_zpow] at this
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
  · rw [Subgroup.zpowers_le]; exact hzZ'

private theorem k89o2_exists_e {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    {ω : G} (hFacts : AllFacts889 D) (hω : Set889 D L P ω) :
    ∃ e : ↥(K889 L ω), orderOf e = 5 := by
  have h5 : 5 ∣ Nat.card ↥(K889 L ω) := by
    have hcardK : Nat.card (K889 L ω) =
        Nat.card (Bar2 (K889 L ω)) * Nat.card (CFSG.pCore 2 ↥(K889 L ω)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hcardK, k89o2_card_Bar2_K hFacts hω]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact exists_prime_orderOf_dvd_card' 5 h5

private theorem k89o2_centralizer_le_normalizer_zpowers {G : Type} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro g hg
  have hg' : g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    have hc : Commute x g := Subgroup.mem_centralizer_iff.mp hg x rfl
    exact (hc.zpow_left n).eq
  exact Subgroup.centralizer_le_normalizer _ hg'

private theorem k89o2_commutator_le_self {G : Type} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

private theorem k89o2_fixed_lift {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {D : Subgroup G} (hDq : IsPGroup q D) {f : G} (hf : f ∈ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (orderOf f) q) {d : G} (hfix : d⁻¹ * (f * d * f⁻¹) ∈ ⁅D, D⁆) :
    ∃ n ∈ ⁅D, D⁆, f * (d * n) * f⁻¹ = d * n := by
  have hN : ∀ n ∈ ⁅D, D⁆, f * n * f⁻¹ ∈ ⁅D, D⁆ := by
    have hle : ⁅D, D⁆ ≤ ⁅D, D⁆.comap (MulAut.conj f).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj f).toMonoidHom ⁅a, b⁆ ∈ ⁅D, D⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hf a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hf b).mp hb)
    intro n hn
    exact hle hn
  have hcard : Nat.Coprime (orderOf f) (Nat.card (⁅D, D⁆ : Subgroup G)) := by
    obtain ⟨m, hm⟩ := hDq.exists_card_eq
    have hdvd : Nat.card (⁅D, D⁆ : Subgroup G) ∣ q ^ m := by
      rw [← hm]; exact Subgroup.card_dvd_of_le (k89o2_commutator_le_self D)
    exact (Nat.Coprime.pow_right m hcop).coprime_dvd_right hdvd
  exact CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime ⁅D, D⁆ hN hfix hcard

private theorem k89o2_mem_of_fixed {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {D : Subgroup G} (hDq : IsPGroup q D) {f : G} (hf : f ∈ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (orderOf f) q) (hC : D ⊓ Subgroup.centralizer ({f} : Set G) ≤ ⁅D, D⁆)
    {d : G} (hd : d ∈ D) (hfix : d⁻¹ * (f * d * f⁻¹) ∈ ⁅D, D⁆) : d ∈ ⁅D, D⁆ := by
  obtain ⟨n, hn, hfn⟩ := k89o2_fixed_lift hDq hf hcop hfix
  have hdn : d * n ∈ D ⊓ Subgroup.centralizer ({f} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨D.mul_mem hd (k89o2_commutator_le_self D hn), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact mul_inv_eq_iff_eq_mul.mp hfn
  have h1 := hC hdn
  have h2 : d = d * n * n⁻¹ := by group
  rw [h2]
  exact ⁅D, D⁆.mul_mem h1 (⁅D, D⁆.inv_mem hn)

private theorem k89o2_rank_centralizer_le {G : Type} [Group G] [Finite G] {D : Data G}
    (hrank : Rank889 D) {L P : Subgroup G} (hS : Set880 D L P) {q : ℕ} (hq : q.Prime)
    (hq7 : 7 ≤ q) {x : G} {a : ℕ} (ha : 0 < a) (hx : orderOf x = 2 ^ a) {H : Subgroup G}
    (hH : H ≤ Subgroup.centralizer ({x} : Set G)) : CFSG.Open.pRank q H ≤ 2 := by
  have hU : Subgroup.zpowers x ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hx
    have : 1 < 2 ^ a := Nat.one_lt_two_pow ha.ne'
    omega
  have hUp : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hx])
  have hloc := r889_isTwoLocal_normalizer hU hUp
  have hle : H ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    hH.trans (k89o2_centralizer_le_normalizer_zpowers x)
  have h1 : CFSG.Open.pRank q H ≤ CFSG.Open.pRank q (Subgroup.normalizer
      (Subgroup.zpowers x : Set G)) := CFSG.SectionRank.pRank_mono hq.one_lt hle
  have h2 := (hrank L P hS _ hloc).2 q hq hq7
  omega

private theorem k89o2_card_image_le {G : Type} [Group G] [Finite G] (hQRank : S889QRank) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {D H : Subgroup G} [(⁅D, D⁆.subgroupOf D).Normal] (hHD : H ≤ D)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDclass : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hHrank : CFSG.Open.pRank q H ≤ 2) :
    Nat.card ((H.subgroupOf D).map (QuotientGroup.mk' (⁅D, D⁆.subgroupOf D))) ≤ q ^ 2 := by
  have hHexp : ∀ x ∈ H, x ^ q = 1 := fun x hx => hDexp x (hHD hx)
  have hHclass : ⁅⁅H, H⁆, H⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono (Subgroup.commutator_mono hHD hHD) hHD).trans
      (le_of_eq hDclass))
  have hHindex : (⁅H, H⁆.subgroupOf H).index ≤ q ^ 2 := hQRank G q hq hq2 H hHexp hHclass hHrank
  let HS : Subgroup ↥D := H.subgroupOf D
  let f : ↥D →* (↥D ⧸ ⁅D, D⁆.subgroupOf D) := QuotientGroup.mk' _
  have hJ_le_H : ⁅H, H⁆ ≤ H := k89o2_commutator_le_self H
  have hJ_le_DD : ⁅H, H⁆ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hHD hHD
  have hker : (f.subgroupMap HS).ker = (HS ⊓ f.ker).subgroupOf HS := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      rw [MonoidHom.mem_ker]
      have h1 : ((f.subgroupMap HS) x : ↥D ⧸ ⁅D, D⁆.subgroupOf D) = 1 := by rw [hx]; rfl
      simpa using h1
    · rintro ⟨-, hx⟩
      rw [MonoidHom.mem_ker] at hx
      exact Subtype.ext (by simpa using hx)
  have hcard : Nat.card (HS.map f) = ((f.subgroupMap HS).ker).index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr ((QuotientGroup.quotientKerEquivRange (f.subgroupMap HS)).trans
      ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr
        (f.subgroupMap_surjective HS))).trans Subgroup.topEquiv))).symm
  have hrel : ((f.subgroupMap HS).ker).index = (HS ⊓ f.ker).relIndex HS := by
    rw [hker, Subgroup.relIndex]
  have hK'' : (⁅H, H⁆).subgroupOf D ≤ HS ⊓ f.ker := by
    refine le_inf (Subgroup.subgroupOf_mono D hJ_le_H) ?_
    intro x hx
    rw [show f.ker = ⁅D, D⁆.subgroupOf D from QuotientGroup.ker_mk' _]
    exact Subgroup.mem_subgroupOf.mpr (hJ_le_DD hx)
  have hmono : (HS ⊓ f.ker).relIndex HS ≤ ((⁅H, H⁆).subgroupOf D).relIndex HS :=
    Subgroup.relIndex_le_of_le_left hK''
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hsub : ((⁅H, H⁆).subgroupOf D).relIndex HS = (⁅H, H⁆).relIndex H :=
    Subgroup.relIndex_subgroupOf hHD
  have hbd : (⁅H, H⁆).relIndex H ≤ q ^ 2 := by
    show ((⁅H, H⁆).subgroupOf H).index ≤ q ^ 2
    exact hHindex
  rw [hcard, hrel]
  exact hmono.trans (hsub ▸ hbd)

private theorem k89o2_finrank_le_two {q : ℕ} [Fact q.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod q) V] [Finite V] (S : Submodule (ZMod q) V) (h : Nat.card S ≤ q ^ 2) :
    Module.finrank (ZMod q) S ≤ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := S), Nat.card_zmod] at h
  exact (Nat.pow_le_pow_iff_right (Fact.out : q.Prime).one_lt).mp h

private theorem k89o2_isA6Z3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsA6Z3 X) : IsA6Z3 Y := by
  obtain ⟨⟨hperf, hsimple, a, b, hab⟩, hcard, ⟨hAlt⟩⟩ := h
  have hcen : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y :=
    Subgroup.map_center_eq e
  let eq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e hcen
  refine ⟨⟨Group.IsPerfect.ofSurjective (f := (e : X →* Y)) e.surjective,
    (MulEquiv.isSimpleGroup_congr eq).mp hsimple, eq a, eq b, ?_⟩, ?_, ⟨eq.symm.trans hAlt⟩⟩
  · intro hc
    exact hab (eq.injective (by rw [map_mul, map_mul]; exact hc))
  · rw [← hcard]
    exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm

private theorem k89o2_perfect_map {K H : Type} [Group K] [Group H] (φ : K →* H)
    (hφ : Function.Surjective φ) (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) :
    ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ := by
  have h := Subgroup.map_commutator (⊤ : Subgroup K) ⊤ φ
  rw [hperf, Subgroup.map_top_of_surjective φ hφ] at h
  exact h.symm

private theorem k89o2_isA6Z3_quot {K : Type} [Group K] [Finite K]
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) (R : Subgroup K) [R.Normal]
    (hnot2 : ¬ IsPGroup 2 (K ⧸ R)) {z : K} (hz3 : orderOf z = 3)
    (hzc : QuotientGroup.mk' (CFSG.pCore 2 K) z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K))
    (hzR : (QuotientGroup.mk' R z : K ⧸ R) ≠ 1) :
    IsA6Z3 ((K ⧸ R) ⧸ CFSG.pCore 2 (K ⧸ R)) ∧
      QuotientGroup.mk' (CFSG.pCore 2 (K ⧸ R)) (QuotientGroup.mk' R z) ∈
        Subgroup.center ((K ⧸ R) ⧸ CFSG.pCore 2 (K ⧸ R)) := by
  classical
  let π : K →* K ⧸ R := QuotientGroup.mk' R
  let ψ : K →* (K ⧸ R) ⧸ CFSG.pCore 2 (K ⧸ R) :=
    (QuotientGroup.mk' (CFSG.pCore 2 (K ⧸ R))).comp π
  have hψsurj : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hO2 : CFSG.pCore 2 K ≤ ψ.ker := by
    intro x hx
    have hnorm : ((CFSG.pCore 2 K).map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R)
    have hp : IsPGroup 2 ((CFSG.pCore 2 K).map π) := (CFSG.pCore_isPGroup).map π
    have hle : (CFSG.pCore 2 K).map π ≤ CFSG.pCore 2 (K ⧸ R) := le_sSup ⟨hnorm, hp⟩
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr (hle (Subgroup.mem_map_of_mem π hx))
  let ψb : (K ⧸ CFSG.pCore 2 K) →* (K ⧸ R) ⧸ CFSG.pCore 2 (K ⧸ R) :=
    QuotientGroup.lift (CFSG.pCore 2 K) ψ hO2
  have hψb : ∀ x : K, ψb (QuotientGroup.mk' (CFSG.pCore 2 K) x) = ψ x := fun x => rfl
  have hψbsurj : Function.Surjective ψb := by
    intro y
    obtain ⟨x, rfl⟩ := hψsurj y
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 K) x, hψb x⟩
  have hcen : QuotientGroup.mk' (CFSG.pCore 2 (K ⧸ R)) (QuotientGroup.mk' R z) ∈
      Subgroup.center ((K ⧸ R) ⧸ CFSG.pCore 2 (K ⧸ R)) :=
    Subgroup.map_center_le_center hψbsurj (Subgroup.mem_map_of_mem ψb hzc)
  refine ⟨?_, hcen⟩
  have hqs : CFSG.Open.IsQuasisimple (K ⧸ CFSG.pCore 2 K) := ⟨hA6.1.1.commutator_eq_top, hA6.1.2.1⟩
  rcases GL83.I243.normal_le_center_or_eq_top hqs ψb.ker with hle | htop
  · have hcard3 : Nat.card (Subgroup.center (K ⧸ CFSG.pCore 2 K)) = 3 := hA6.2.1
    have hdvd : Nat.card ψb.ker ∣ 3 := hcard3 ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · have hker : ψb.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hinj : Function.Injective ψb := (MonoidHom.ker_eq_bot_iff ψb).mp hker
      exact k89o2_isA6Z3_of_mulEquiv (MulEquiv.ofBijective ψb ⟨hinj, hψbsurj⟩) hA6
    · exfalso
      have hker : ψb.ker = Subgroup.center (K ⧸ CFSG.pCore 2 K) :=
        Subgroup.eq_of_le_of_card_ge hle (by omega)
      have hz1 : ψb (QuotientGroup.mk' (CFSG.pCore 2 K) z) = 1 := by
        rw [← MonoidHom.mem_ker, hker]; exact hzc
      have hmem : π z ∈ CFSG.pCore 2 (K ⧸ R) := (QuotientGroup.eq_one_iff _).mp hz1
      obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := K ⧸ R) ⟨π z, hmem⟩
      have hn' : (π z) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
      have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
      have h3' : (π z) ^ (3 ^ 1) = 1 := by rw [pow_one, ← map_pow, hz3', map_one]
      exact hzR (k89o2_eq_one_of_two_three hn' h3')
  · exfalso
    apply hnot2
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    have hx1 : ψb (QuotientGroup.mk' (CFSG.pCore 2 K) x) = 1 := by
      rw [← MonoidHom.mem_ker, htop]; exact Subgroup.mem_top _
    have hmem : π x ∈ CFSG.pCore 2 (K ⧸ R) := (QuotientGroup.eq_one_iff _).mp hx1
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := K ⧸ R) ⟨π x, hmem⟩
    have hn' : (π x) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, hn'⟩

private theorem k89o2_apply_hMod (hMod : S889Module) {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q)
    {K : Type} [Group K] [Finite K] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hA6 : IsA6Z3 (K ⧸ CFSG.pCore 2 K)) {V : Type} [AddCommGroup V] [Module (ZMod q) V]
    [Finite V] (ρ : K →* Module.End (ZMod q) V) (hntriv : ∃ k, ρ k ≠ 1)
    (hirr : ∀ W : Submodule (ZMod q) V, (∀ k : K, ∀ w ∈ W, ρ k w ∈ W) → W = ⊥ ∨ W = ⊤)
    {z : K} (hz3 : orderOf z = 3)
    (hzc : QuotientGroup.mk' (CFSG.pCore 2 K) z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K))
    (hzfix : ∀ v : V, ρ z v = v → v = 0) {e : K} (he5 : orderOf e = 5)
    (hefix : ∀ v : V, ρ e v = v → v = 0)
    (h2 : ∀ k : K, ∀ a : ℕ, 0 < a → orderOf k = 2 ^ a →
      Module.finrank (ZMod q) (LinearMap.ker (ρ k - 1)) ≤ 2) : False := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨k0, hk0⟩ := hntriv
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact hk0 (LinearMap.ext fun v => Subsingleton.elim _ _)
  let R : Subgroup K := ρ.ker
  have hR : ∀ x : K, x ∈ R ↔ ρ x = 1 := fun x => MonoidHom.mem_ker
  have : R.Normal := inferInstance
  let ρ' : K ⧸ R →* Module.End (ZMod q) V := QuotientGroup.lift R ρ le_rfl
  have hρ' : ∀ x : K, ρ' (QuotientGroup.mk x) = ρ x := fun x => rfl
  have hinj : Function.Injective ρ' := by
    intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hρ', hρ'] at hab
    have h1 : ρ (a⁻¹ * b) = 1 := by
      rw [map_mul, ← hab, ← map_mul, inv_mul_cancel, map_one]
    exact QuotientGroup.eq.mpr ((hR _).mpr h1)
  have hne1 : ∀ x : K, (∀ v : V, ρ x v = v → v = 0) → ρ x ≠ 1 := by
    intro x hx h1
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hx v (by rw [h1]; rfl))
  have hzR : (QuotientGroup.mk' R z : K ⧸ R) ≠ 1 := fun h =>
    hne1 z hzfix ((hR z).mp ((QuotientGroup.eq_one_iff z).mp h))
  have heR : (QuotientGroup.mk' R e : K ⧸ R) ≠ 1 := fun h =>
    hne1 e hefix ((hR e).mp ((QuotientGroup.eq_one_iff e).mp h))
  have hperf' : ⁅(⊤ : Subgroup (K ⧸ R)), (⊤ : Subgroup (K ⧸ R))⁆ = ⊤ :=
    k89o2_perfect_map (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R) hperf
  have hnot2 : ¬ IsPGroup 2 (K ⧸ R) := by
    intro hp
    have : Group.IsNilpotent (K ⧸ R) := hp.isNilpotent
    by_cases hnt : Nontrivial (K ⧸ R)
    · exact (IsSolvable.commutator_lt_top_of_nontrivial (K ⧸ R)).ne hperf'
    · rw [not_nontrivial_iff_subsingleton] at hnt
      have h1 : (QuotientGroup.mk k0 : K ⧸ R) = 1 := Subsingleton.elim _ _
      exact hk0 ((hR k0).mp ((QuotientGroup.eq_one_iff k0).mp h1))
  obtain ⟨hA6', hzc'⟩ := k89o2_isA6Z3_quot hA6 R hnot2 hz3 hzc hzR
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hz3' : orderOf (QuotientGroup.mk' R z : K ⧸ R) = 3 := by
    refine orderOf_eq_prime ?_ hzR
    rw [← map_pow, ← hz3, pow_orderOf_eq_one, map_one]
  have he5' : orderOf (QuotientGroup.mk' R e : K ⧸ R) = 5 := by
    refine orderOf_eq_prime ?_ heR
    rw [← map_pow, ← he5, pow_orderOf_eq_one, map_one]
  refine hMod q hq hq7 (K ⧸ R) hperf' hA6' V ρ' hinj ?_ (QuotientGroup.mk' R z) hz3' hzc'
    ?_ (QuotientGroup.mk' R e) he5' ?_ ?_
  · intro W hW
    exact hirr W fun k w hw => hW (QuotientGroup.mk k) w hw
  · intro v hv
    exact hzfix v hv
  · intro v hv
    exact hefix v hv
  · intro t ht
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
    have hmpos : 0 < m := hm.pos
    have hdvd : m ∣ orderOf k := ⟨2 ^ a, by rw [hkm, mul_comm]⟩
    have hk' : orderOf (k ^ m) = 2 ^ a := by
      rw [orderOf_pow_of_dvd hmpos.ne' hdvd, hkm, Nat.mul_div_cancel _ hmpos]
    have ht2 : (QuotientGroup.mk k : K ⧸ R) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (QuotientGroup.mk k : K ⧸ R)
      rwa [ht] at this
    have hmk : (QuotientGroup.mk (k ^ m) : K ⧸ R) = QuotientGroup.mk k := by
      obtain ⟨j, hj⟩ := hm
      rw [QuotientGroup.mk_pow, hj, pow_succ, pow_mul, ht2, one_pow, one_mul]
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha0 | ha
      · exfalso
        rw [ha0, pow_zero, orderOf_eq_one_iff] at hk'
        have h1 : (QuotientGroup.mk k : K ⧸ R) = 1 := by rw [← hmk, hk', QuotientGroup.mk_one]
        rw [h1, orderOf_one] at ht
        omega
      · exact ha
    have := h2 (k ^ m) a ha hk'
    rwa [← hρ' (k ^ m), hmk] at this

theorem s889_o2_of_parts {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h885 : R885 D) (h887 : R887 D) (hrank : Rank889 D) (hFacts : AllFacts889 D)
    (hSplit : S889Split D) (hOdd : S889OddCore D) (hMod : S889Module) (hQMin : S889QMin)
    (hQRank : S889QRank) (hDick : S889Dickson) : S889O2 D := by
  classical
  intro L P ω hω N hN
  by_contra hO2N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Set880 D L P := hω.set880
  have hFacts' : Facts889 D L P ω := hFacts L P ω hω
  have hKcent : K889 L ω ≤ centralizer ({ω} : Set G) := r889_K889_le_centralizer L ω
  have hHleN : centralizer ({ω} : Set G) ≤ N := hN.2
  have hKleN : K889 L ω ≤ N := hKcent.trans hHleN
  have hNne : N ≠ ⊤ := hN.1.ne_top
  have hNnotM : ¬ N ≤ D.M := fun h => hω.notM (hHleN.trans h)
  let I := PPrimeCoreIn 3 N
  have hIleN : I ≤ N := Subgroup.map_subtype_le _
  have hInorm : N ≤ Subgroup.normalizer (I : Set G) := by
    have hsub : (I.subgroupOf N).Normal := by
      have hIeq : I.subgroupOf N = CFSG.pPrimeCore 3 ↥N := by
        show (PPrimeCoreIn 3 N).subgroupOf N = CFSG.pPrimeCore 3 ↥N
        rw [PPrimeCoreIn, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
      rw [hIeq]; infer_instance
    rwa [Subgroup.normal_subgroupOf_iff_le_normalizer hIleN] at hsub
  have hIcop : Nat.Coprime 3 (Nat.card ↥I) := by
    have hcard : Nat.card ↥I = Nat.card ↥(CFSG.pPrimeCore 3 ↥N) := by
      show Nat.card ↥(PPrimeCoreIn 3 N) = Nat.card ↥(CFSG.pPrimeCore 3 ↥N)
      exact Subgroup.card_map_of_injective (K := CFSG.pPrimeCore 3 ↥N) N.subtype_injective
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have hOddI := hOdd L P ω hω N hNne hKleN hNnotM
  have h5I : ¬ 5 ∣ Nat.card ↥I := hOddI.1
  have h3I : ¬ 3 ∣ Nat.card ↥I := (Nat.prime_three.coprime_iff_not_dvd).mp hIcop
  have hIsolv : Group.IsSolvable ↥I := hOddI.2
  have hSplitN : N ≤ I ⊔ (N ⊓ D.M) := hSplit L P ω hω N hNne hKleN hNnotM
  have hO2I : pCoreOf 2 I = ⊥ := by
    have hle := k89o2_pCoreOf_le_of_le_normal (p := 2) hIleN hInorm
    rw [hO2N] at hle
    exact le_bot_iff.mp hle
  have hKF : ¬ K889 L ω ≤
      Subgroup.centralizer (((fittingSubgroup ↥I).map I.subtype : Subgroup G) : Set G) := by
    intro hcent
    have hcommKF : ⁅K889 L ω, (fittingSubgroup ↥I).map I.subtype⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    have hcommFK : ⁅(fittingSubgroup ↥I).map I.subtype, K889 L ω⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcommKF
    have h1 : ⁅⁅K889 L ω, (fittingSubgroup ↥I).map I.subtype⁆, I⁆ = ⊥ := by
      rw [hcommKF]; simp
    have hFamb_le : ⁅(fittingSubgroup ↥I).map I.subtype, I⁆ ≤ (fittingSubgroup ↥I).map I.subtype :=
      k89o2_commutator_le_left_of_le_normalizer (k89o2_le_normalizer_fitting (I := I))
    have h2 : ⁅⁅(fittingSubgroup ↥I).map I.subtype, I⁆, K889 L ω⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono_left hFamb_le).trans (le_of_eq hcommFK))
    have h3 : ⁅⁅I, K889 L ω⁆, (fittingSubgroup ↥I).map I.subtype⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate
        (H₁ := I) (H₂ := K889 L ω) (H₃ := (fittingSubgroup ↥I).map I.subtype) h1 h2
    have hIcomm_le : ⁅I, K889 L ω⁆ ≤ I :=
      k89o2_commutator_le_left_of_le_normalizer (hKleN.trans hInorm)
    have hIK_le : ⁅I, K889 L ω⁆ ≤ (fittingSubgroup ↥I).map I.subtype :=
      (le_inf hIcomm_le
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)).trans
        (k89o2_centralizer_fitting_le hIsolv)
    have h4 : ⁅⁅I, K889 L ω⁆, K889 L ω⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono_left hIK_le).trans (le_of_eq hcommFK))
    have h4' : ⁅⁅K889 L ω, I⁆, K889 L ω⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (K889 L ω) I]; exact h4
    have h5 : ⁅⁅K889 L ω, K889 L ω⁆, I⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate
        (H₁ := K889 L ω) (H₂ := K889 L ω) (H₃ := I) h4' h4
    have hKI : ⁅K889 L ω, I⁆ = ⊥ := by rwa [hFacts'.perfect] at h5
    have hIK : ⁅I, K889 L ω⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hKI
    have hIcentK : I ≤ Subgroup.centralizer (K889 L ω : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hIK
    have hIcentZ : I ≤ Subgroup.centralizer (ZOf (P ⊓ L) : Set G) :=
      hIcentK.trans (Subgroup.centralizer_le (show (ZOf (P ⊓ L) : Set G) ⊆
        (K889 L ω : Set G) from (inf_le_left : ZOf (P ⊓ L) ≤ P ⊓ L).trans hFacts'.qLe))
    have hIleM : I ≤ D.M :=
      hIcentZ.trans ((Subgroup.centralizer_le_normalizer _).trans (h887 L P hS))
    exact hNnotM (hSplitN.trans (sup_le hIleM inf_le_right))
  have hqexists : ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧
      ¬ K889 L ω ≤ Subgroup.centralizer (pCoreOf q I : Set G) := by
    by_contra hcon
    have hcon' : ∀ q : ℕ, q.Prime → 7 ≤ q →
        K889 L ω ≤ Subgroup.centralizer (pCoreOf q I : Set G) := by
      intro q hq hq7
      by_contra hqnot
      exact hcon ⟨q, hq, hq7, hqnot⟩
    have hFamb_eq : (fittingSubgroup ↥I).map I.subtype =
        ⨆ p : (Nat.card ↥I).primeFactors.attach, pCoreOf p.1.1 I := by
      rw [CFSG.fitting_eq_sup_pCore ↥I, Subgroup.map_iSup]
      rfl
    refine hKF ?_
    rw [hFamb_eq]
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ (fun p => ?_)
    have hpp : p.1.1.Prime := (Nat.mem_primeFactors.mp p.1.2).1
    by_cases hp7 : 7 ≤ p.1.1
    · exact hcon' p.1.1 hpp hp7
    · have hp5 : p.1.1 ≤ 5 := by
        by_contra hle
        have hlt : p.1.1 < 7 := Nat.lt_of_not_le hp7
        have h6 : p.1.1 = 6 := by omega
        rw [h6] at hpp
        exact absurd hpp (by decide)
      rw [k89o2_pCoreOf_eq_bot_of_prime_le_five hO2I h3I h5I hpp hp5]
      have htop : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
        Subgroup.centralizer_eq_top_iff_subset.mpr (by
          intro x hx
          simp only [SetLike.mem_coe, Subgroup.mem_bot] at hx
          subst hx
          exact Subgroup.one_mem _)
      rw [htop]
      exact le_top
  obtain ⟨q, hq, hq7, hqD0⟩ := hqexists
  have hq2 : q ≠ 2 := by omega
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hqK : ¬ q ∣ Nat.card (K889 L ω) := k89o2_not_dvd_card_K hFacts hω hq hq7
  have hD0norm : K889 L ω ≤ Subgroup.normalizer (pCoreOf q I : Set G) :=
    (hKleN.trans hInorm).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pCore q ↥I))
  have hD0K_ne : ⁅pCoreOf q I, K889 L ω⁆ ≠ ⊥ := by
    intro h
    rw [Subgroup.commutator_comm] at h
    exact hqD0 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  let M : Subgroup G := D.M
  have hMmax : rankThreeIsMaxTwoLocal M := D.maxLocal
  have hKleM : K889 L ω ≤ M := (r889_K889_le_left L ω).trans (r889_le_M hS)
  have hsp5 : IsStronglyPEmbedded 5 D.M := by
    refine UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hS.mem) ?_
    rw [(h885 L P hS).2.1]
    exact Set.mem_singleton 5
  obtain ⟨z, hz3, hZz, hzc⟩ := k89o2_exists_z hFacts' hω.sylow3.isPGroup
  obtain ⟨e, he5⟩ := k89o2_exists_e hFacts hω
  have hCzM : Subgroup.centralizer ({(z : G)} : Set G) ≤ M := by
    refine (k89o2_centralizer_le_normalizer_zpowers (z : G)).trans ?_
    rw [← hZz]
    exact h887 L P hS
  have hCeM : Subgroup.centralizer ({(e : G)} : Set G) ≤ M :=
    r889_centralizer_le_of_five hsp5 (hKleM e.2) (by rw [Subgroup.orderOf_coe]; exact he5)
  obtain ⟨D, hDleD0, hKDnorm, hDexp, hDclass, hDnontriv, hDirr⟩ :=
    hQMin G q hq hq2 (K889 L ω) (pCoreOf q I)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup q I) hqK hD0norm hD0K_ne
  have hN0n : (⁅D, D⁆.subgroupOf D).Normal := by
    have h := Subgroup.normal_subgroupOf_commutator_sup (H₁ := D) (H₂ := D)
    rwa [sup_idem] at h
  have hQcomm : ∀ a b : ↥D ⧸ ⁅D, D⁆.subgroupOf D, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
    have hxy : x * y / (y * x) = ⁅x, y⁆ := by
      rw [div_eq_mul_inv, mul_inv_rev, commutatorElement_def]; group
    rw [hxy]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.commutator_mem_commutator x.2 y.2)
  let _ : CommGroup (↥D ⧸ ⁅D, D⁆.subgroupOf D) :=
    { (inferInstance : Group (↥D ⧸ ⁅D, D⁆.subgroupOf D)) with mul_comm := hQcomm }
  have : NeZero q := ⟨hq.ne_zero⟩
  have hq0 : ∀ v : Additive (↥D ⧸ ⁅D, D⁆.subgroupOf D), q • v = 0 := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hvm : v = Additive.ofMul (Additive.toMul v) := rfl
    have hv : v = Additive.ofMul (x : ↥D ⧸ ⁅D, D⁆.subgroupOf D) := by
      rw [hvm, hx]
    rw [hv, ← ofMul_pow]
    have hxq : (x : ↥D ⧸ ⁅D, D⁆.subgroupOf D) ^ q = 1 := by
      rw [← QuotientGroup.mk_pow, show x ^ q = 1 from Subtype.ext (hDexp x.val x.2)]
      rfl
    rw [hxq]
    rfl
  let _ : Module (ZMod q) (Additive (↥D ⧸ ⁅D, D⁆.subgroupOf D)) :=
    AddCommGroup.zmodModule (n := q) hq0
  let cD : ↥(K889 L ω) →* MulAut ↥D :=
    (Subgroup.normalizerMonoidHom (H := D)).comp (Subgroup.inclusion hKDnorm)
  have htop : (⊤ : Subgroup ↥D).map D.subtype = D := by
    have h := Subgroup.subgroupOf_map_subtype (H := ⊤) (K := D)
    simpa using h
  have hN0_eq : (⁅D, D⁆.subgroupOf D) = ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ := by
    have hmap : (⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆).map D.subtype = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator]
      simp only [htop]
    rw [Subgroup.subgroupOf, ← hmap]
    exact Subgroup.comap_map_eq_self_of_injective (H := ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆)
      D.subtype_injective
  have hN0_map (k : ↥(K889 L ω)) : (⁅D, D⁆.subgroupOf D).map (cD k) = ⁅D, D⁆.subgroupOf D := by
    rw [hN0_eq, Subgroup.map_commutator]
    rw [Subgroup.map_top_of_surjective (↑(cD k) : ↥D →* ↥D) (cD k).surjective]
  let cQ (k : ↥(K889 L ω)) : (↥D ⧸ ⁅D, D⁆.subgroupOf D) →* (↥D ⧸ ⁅D, D⁆.subgroupOf D) :=
    QuotientGroup.map (N := ⁅D, D⁆.subgroupOf D) (M := ⁅D, D⁆.subgroupOf D) (cD k)
      (Subgroup.map_le_iff_le_comap.mp (le_of_eq (hN0_map k)))
  have cQ_mk (k : ↥(K889 L ω)) (d : ↥D) :
      cQ k (d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) = (cD k d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) := rfl
  have cQ_one : cQ 1 = MonoidHom.id (↥D ⧸ ⁅D, D⁆.subgroupOf D) := by
    apply MonoidHom.ext
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    rw [cQ_mk]
    apply congrArg (fun z : ↥D => (z : ↥D ⧸ ⁅D, D⁆.subgroupOf D))
    have h1 : cD 1 = 1 := map_one cD
    rw [h1]
    rfl
  have cQ_mul : ∀ k l : ↥(K889 L ω), cQ (k * l) = (cQ k).comp (cQ l) := by
    intro k l
    apply MonoidHom.ext
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [cQ_mk, MonoidHom.comp_apply]
    apply congrArg (fun z : ↥D => (z : ↥D ⧸ ⁅D, D⁆.subgroupOf D))
    rw [map_mul cD]
    rfl
  let ρ0 : ↥(K889 L ω) →* Module.End (ZMod q) (Additive (↥D ⧸ ⁅D, D⁆.subgroupOf D)) :=
    { toFun := fun k => AddMonoidHom.toZModLinearMap q (MonoidHom.toAdditive (cQ k))
      map_one' := by
        ext v
        change (MonoidHom.toAdditive (cQ 1)) v = v
        rw [cQ_one]
        rfl
      map_mul' := by
        intro k l
        ext v
        change (MonoidHom.toAdditive (cQ (k * l))) v =
          (MonoidHom.toAdditive (cQ k)) ((MonoidHom.toAdditive (cQ l)) v)
        rw [cQ_mul]
        rfl }
  let V := Additive (↥D ⧸ ⁅D, D⁆.subgroupOf D)
  let π : ↥D →* Multiplicative V :=
    { toFun := fun d => Multiplicative.ofAdd (Additive.ofMul (d : ↥D ⧸ ⁅D, D⁆.subgroupOf D))
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let vec (d : ↥D) : V := Multiplicative.toAdd (π d)
  have vec_mk (d : ↥D) : vec d = Additive.ofMul (d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) := rfl
  let preW (S : Submodule (ZMod q) V) : Subgroup G :=
    (S.toAddSubgroup.toSubgroup.comap π).map D.subtype
  have mem_preW {S : Submodule (ZMod q) V} {g : G} :
      g ∈ preW S ↔ ∃ h : g ∈ D, vec ⟨g, h⟩ ∈ S := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, (Multiplicative.mem_toSubgroup S.toAddSubgroup (π u)).mp hu⟩
    · rintro ⟨h, hv⟩
      exact ⟨⟨g, h⟩, (Multiplicative.mem_toSubgroup S.toAddSubgroup (π ⟨g, h⟩)).mpr hv, rfl⟩
  have hDD_le_D : ⁅D, D⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)
  have hle_preW (S : Submodule (ZMod q) V) : ⁅D, D⁆ ≤ preW S := by
    intro g hg
    refine mem_preW.mpr ⟨hDD_le_D hg, ?_⟩
    have hgQ : vec ⟨g, hDD_le_D hg⟩ = 0 := by
      rw [vec_mk]
      rw [show ((⟨g, hDD_le_D hg⟩ : ↥D) : (↥D ⧸ ⁅D, D⁆.subgroupOf D)) = 1 from
        QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.mem_subgroupOf.mpr hg)]
      rfl
    rw [hgQ]
    exact S.zero_mem
  have preW_le (S : Submodule (ZMod q) V) : preW S ≤ D := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hInv (S : Submodule (ZMod q) V)
      (hS : ∀ k : ↥(K889 L ω), ∀ w ∈ S, ρ0 k w ∈ S) :
      K889 L ω ≤ Subgroup.normalizer (preW S : Set G) := by
    have key : ∀ j ∈ K889 L ω, ∀ g ∈ preW S, j * g * j⁻¹ ∈ preW S := by
      intro j hj g hg
      obtain ⟨hgD, hv⟩ := mem_preW.mp hg
      have hconjD : j * g * j⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hKDnorm hj) g).1 hgD
      refine mem_preW.mpr ⟨hconjD, ?_⟩
      have hspec : ρ0 ⟨j, hj⟩ (vec ⟨g, hgD⟩) = vec ⟨j * g * j⁻¹, hconjD⟩ := rfl
      rw [← hspec]
      exact hS ⟨j, hj⟩ _ hv
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key j hj g, fun h => ?_⟩
    have := key j⁻¹ ((K889 L ω).inv_mem hj) _ h
    simpa [mul_assoc] using this
  have hIrr : ∀ S : Submodule (ZMod q) V,
      (∀ k : ↥(K889 L ω), ∀ w ∈ S, ρ0 k w ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    rcases hDirr (preW S) (hle_preW S) (preW_le S) (hInv S hS) with h | h
    · left
      refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
      obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
      have hy' : y = vec d := by
        apply Additive.toMul.injective
        rw [← hd, vec_mk]
        rfl
      rw [hy'] at hy
      have hdmem : (d : G) ∈ preW S := mem_preW.mpr ⟨d.2, hy⟩
      rw [h] at hdmem
      have hd1 : (d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) = 1 :=
        QuotientGroup.eq_one_iff _ |>.mpr (Subgroup.mem_subgroupOf.mpr hdmem)
      rw [hy', vec_mk, hd1]
      rfl
    · right
      refine Submodule.eq_top_iff'.mpr fun y => ?_
      obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
      have hy' : y = vec d := by
        apply Additive.toMul.injective
        rw [← hd, vec_mk]
        rfl
      rw [hy']
      have hdmem : (d : G) ∈ preW S := by rw [h]; exact d.2
      simpa using (mem_preW.mp hdmem).2
  let f : ↥D →* (↥D ⧸ ⁅D, D⁆.subgroupOf D) := QuotientGroup.mk' _
  have mem_img : ∀ (H : Subgroup G) (g : G) (hg : g ∈ D), g ∈ H →
      vec ⟨g, hg⟩ ∈ AddSubgroup.toZModSubmodule q
        (Subgroup.toAddSubgroup ((H.subgroupOf D).map f)) := by
    intro H g hg hgH
    rw [vec_mk]
    show Additive.ofMul ((⟨g, hg⟩ : ↥D) : ↥D ⧸ ⁅D, D⁆.subgroupOf D) ∈
      AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup ((H.subgroupOf D).map f))
    rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
    simpa [f] using Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hgH)
  have hperfK : ⁅(⊤ : Subgroup ↥(K889 L ω)), (⊤ : Subgroup ↥(K889 L ω))⁆ = ⊤ := by
    have hKtop : (⊤ : Subgroup ↥(K889 L ω)).map (K889 L ω).subtype = K889 L ω := by
      have h := Subgroup.subgroupOf_map_subtype (H := ⊤) (K := K889 L ω)
      simpa using h
    apply Subgroup.map_injective (Subgroup.subtype_injective (K889 L ω))
    rw [Subgroup.map_commutator, hKtop]
    exact hFacts'.perfect
  have hKtriv : (∀ k : ↥(K889 L ω), ρ0 k = 1) → False := by
    intro h1
    apply hDnontriv
    rw [Subgroup.commutator_le]
    intro d hd k hk
    have hfix : vec (cD ⟨k, hk⟩ ⟨d, hd⟩) = vec ⟨d, hd⟩ := by
      have hf := congrArg (fun φ : Module.End (ZMod q) V => φ (vec ⟨d, hd⟩)) (h1 ⟨k, hk⟩)
      rw [show ρ0 ⟨k, hk⟩ (vec ⟨d, hd⟩) = vec (cD ⟨k, hk⟩ ⟨d, hd⟩) from rfl] at hf
      simpa using hf
    have hQeq : ((cD ⟨k, hk⟩ ⟨d, hd⟩ : ↥D) : ↥D ⧸ ⁅D, D⁆.subgroupOf D) =
        ((⟨d, hd⟩ : ↥D) : ↥D ⧸ ⁅D, D⁆.subgroupOf D) := by
      apply Additive.ofMul.injective
      simpa only [vec_mk] using hfix
    rw [QuotientGroup.eq_iff_div_mem] at hQeq
    have hmem := Subgroup.mem_subgroupOf.mp hQeq
    have hmem' : ((cD ⟨k, hk⟩ ⟨d, hd⟩ : ↥D) : G) / (d : G) ∈ ⁅D, D⁆ := by
      simpa using hmem
    have hcd : ((cD ⟨k, hk⟩ ⟨d, hd⟩ : ↥D) : G) = (k : G) * (d : G) * (k : G)⁻¹ := rfl
    rw [hcd] at hmem'
    have hdiv : (k : G) * (d : G) * (k : G)⁻¹ / (d : G) = ⁅(k : G), (d : G)⁆ := by
      rw [div_eq_mul_inv, commutatorElement_def]
    rw [hdiv] at hmem'
    have heq : ⁅d, k⁆ = ⁅(k : G), (d : G)⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [heq]
    exact (⁅D, D⁆).inv_mem hmem'
  have hK_norm_inf : K889 L ω ≤ Subgroup.normalizer ((D ⊓ M : Subgroup G) : Set G) := fun k hk =>
    r889_mem_normalizer_inf (hKDnorm hk) (Subgroup.le_normalizer (H := M) (hKleM hk))
  have hHrank : CFSG.Open.pRank q (D ⊓ M) ≤ 2 := by
    have h1 : CFSG.Open.pRank q (D ⊓ M) ≤ CFSG.Open.pRank q M :=
      CFSG.SectionRank.pRank_mono (by omega) inf_le_right
    have h2 : CFSG.Open.pRank q M ≤ 2 := (hrank L P hS M hMmax.1).2 q hq hq7
    omega
  let H : Subgroup G := D ⊓ M
  let HS : Subgroup ↥D := H.subgroupOf D
  let Ssub : Subgroup (↥D ⧸ ⁅D, D⁆.subgroupOf D) := HS.map f
  let S : Submodule (ZMod q) V := AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup Ssub)
  have hS_card : Nat.card S ≤ q ^ 2 :=
    k89o2_card_image_le hQRank hq hq2 (inf_le_left : D ⊓ M ≤ D) hDexp hDclass hHrank
  have hDM_le_preW : D ⊓ M ≤ preW S := fun d hd =>
    mem_preW.mpr ⟨hd.1, mem_img (D ⊓ M) d hd.1 hd⟩
  have hS_inv : ∀ k : ↥(K889 L ω), ∀ w ∈ S, ρ0 k w ∈ S := by
    intro k w hw
    show ρ0 k w ∈ AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup Ssub)
    rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup] at hw ⊢
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hw
    have hc : cD k a ∈ HS := by
      rw [Subgroup.mem_subgroupOf]
      change (k : G) * (a : G) * (k : G)⁻¹ ∈ H
      exact (Subgroup.mem_normalizer_iff.mp (hK_norm_inf k.2) (a : G)).1
        (Subgroup.mem_subgroupOf.mp ha)
    have hq : cQ k (f a) = f (cD k a) := by
      show cQ k (a : ↥D ⧸ ⁅D, D⁆.subgroupOf D) =
        ((cD k a : ↥D) : ↥D ⧸ ⁅D, D⁆.subgroupOf D)
      rw [cQ_mk]
    show Additive.ofMul (cQ k (f a)) ∈ AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup Ssub)
    rw [AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup, hq]
    exact Subgroup.mem_map_of_mem f hc
  have hS_inf : S = ⊥ ∨ S = ⊤ := hIrr S hS_inv
  have hpreW_bot : preW (⊥ : Submodule (ZMod q) V) = ⁅D, D⁆ := by
    apply le_antisymm
    · intro g hg
      have hv := (mem_preW.mp hg).2
      rw [Submodule.mem_bot] at hv
      rw [vec_mk] at hv
      have hg1 : ((⟨g, (mem_preW.mp hg).1⟩ : ↥D) : ↥D ⧸ ⁅D, D⁆.subgroupOf D) = 1 :=
        (ofMul_eq_zero).mp hv
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hg1)
    · exact hle_preW ⊥
  have hDM_le_DD : D ⊓ M ≤ ⁅D, D⁆ := by
    rcases hS_inf with hbot | htop
    · have h := hbot ▸ hDM_le_preW
      rwa [hpreW_bot] at h
    · exfalso
      have hcardV : Nat.card V ≤ q ^ 2 := by
        have h := hS_card
        rw [htop] at h
        rwa [Nat.card_congr (Submodule.topEquiv (R := ZMod q) (M := V)).toEquiv] at h
      have hfin : Module.finrank (ZMod q) V ≤ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := V), Nat.card_zmod] at hcardV
        exact (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp hcardV
      exact hKtriv (hDick q hq hq7 ↥(K889 L ω) hperfK hFacts'.alt6 V hfin ρ0)
  have hDq : IsPGroup q D := (CFSG.LieType.BorelTits.pCoreOf_isPGroup q I).to_le hDleD0
  have vec_surj : ∀ v : V, ∃ d : ↥D, vec d = v := by
    intro v
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    refine ⟨d, ?_⟩
    apply Additive.toMul.injective
    rw [← hd, vec_mk]
    rfl
  have hfixed : ∀ (g : ↥(K889 L ω)) (d : ↥D), ρ0 g (vec d) = vec d →
      (d : G)⁻¹ * ((g : G) * (d : G) * (g : G)⁻¹) ∈ ⁅D, D⁆ := by
    intro g d hg
    have hv' : vec (cD g d) = vec d := hg
    have hQeq : (d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) = (cD g d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) := by
      apply Additive.ofMul.injective
      simpa only [vec_mk] using hv'.symm
    rw [QuotientGroup.eq] at hQeq
    exact Subgroup.mem_subgroupOf.mp hQeq
  have hfixV : ∀ g : ↥(K889 L ω), Nat.Coprime (orderOf g) q →
      Subgroup.centralizer ({(g : G)} : Set G) ≤ M → ∀ v : V, ρ0 g v = v → v = 0 := by
    intro g hcop hcent v hv
    obtain ⟨d, rfl⟩ := vec_surj v
    have hC : D ⊓ Subgroup.centralizer ({(g : G)} : Set G) ≤ ⁅D, D⁆ :=
      fun x hx => hDM_le_DD ⟨hx.1, hcent hx.2⟩
    have hd : (d : G) ∈ ⁅D, D⁆ :=
      k89o2_mem_of_fixed hDq (hKDnorm g.2) (by rwa [Subgroup.orderOf_coe]) hC d.2 (hfixed g d hv)
    have hd1 : (d : ↥D ⧸ ⁅D, D⁆.subgroupOf D) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hd)
    rw [vec_mk, hd1]
    rfl
  have hfix2 : ∀ (k : ↥(K889 L ω)) (a : ℕ), 0 < a → orderOf k = 2 ^ a →
      Module.finrank (ZMod q) (LinearMap.ker (ρ0 k - 1)) ≤ 2 := by
    intro k a ha hka
    have hx : orderOf (k : G) = 2 ^ a := by rw [Subgroup.orderOf_coe]; exact hka
    have hCrank : CFSG.Open.pRank q (D ⊓ Subgroup.centralizer ({(k : G)} : Set G)) ≤ 2 :=
      k89o2_rank_centralizer_le hrank hS hq hq7 ha hx inf_le_right
    have hcardC := k89o2_card_image_le hQRank hq hq2
      (inf_le_left : D ⊓ Subgroup.centralizer ({(k : G)} : Set G) ≤ D) hDexp hDclass hCrank
    let Sk : Submodule (ZMod q) V := AddSubgroup.toZModSubmodule q (Subgroup.toAddSubgroup
      (((D ⊓ Subgroup.centralizer ({(k : G)} : Set G)).subgroupOf D).map f))
    have hker_le : LinearMap.ker (ρ0 k - 1) ≤ Sk := by
      intro v hv
      have hv' : ρ0 k v = v := by
        have := LinearMap.mem_ker.mp hv
        rw [LinearMap.sub_apply, sub_eq_zero] at this
        exact this
      obtain ⟨d, rfl⟩ := vec_surj v
      have hcop : Nat.Coprime (orderOf (k : G)) q := by
        rw [hx]
        exact Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
      obtain ⟨n, hn, hkn⟩ := k89o2_fixed_lift hDq (hKDnorm k.2) hcop (hfixed k d hv')
      have hdn : (d : G) * n ∈ D := D.mul_mem d.2 (k89o2_commutator_le_self D hn)
      have hdnC : (d : G) * n ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact mul_inv_eq_iff_eq_mul.mp hkn
      have hmem := mem_img (D ⊓ Subgroup.centralizer ({(k : G)} : Set G)) ((d : G) * n) hdn
        (Subgroup.mem_inf.mpr ⟨hdn, hdnC⟩)
      have hvec : vec ⟨(d : G) * n, hdn⟩ = vec d := by
        rw [vec_mk, vec_mk]
        congr 1
        symm
        rw [QuotientGroup.eq]
        refine Subgroup.mem_subgroupOf.mpr ?_
        show (d : G)⁻¹ * ((d : G) * n) ∈ ⁅D, D⁆
        rwa [inv_mul_cancel_left]
      rw [← hvec]
      exact hmem
    exact (Submodule.finrank_mono hker_le).trans (k89o2_finrank_le_two Sk hcardC)
  have hntriv : ∃ k : ↥(K889 L ω), ρ0 k ≠ 1 := by
    by_contra hcon
    exact hKtriv fun k => by_contra fun hk => hcon ⟨k, hk⟩
  have hcop3 : Nat.Coprime (orderOf z) q := by
    rw [hz3]; exact (Nat.coprime_primes Nat.prime_three hq).mpr (by omega)
  have hcop5 : Nat.Coprime (orderOf e) q := by
    rw [he5]; exact (Nat.coprime_primes Nat.prime_five hq).mpr (by omega)
  exact k89o2_apply_hMod hMod hq hq7 hperfK hFacts'.alt6 ρ0 hntriv hIrr hz3 hzc
    (hfixV z hcop3 hCzM) he5 (hfixV e hcop5 hCeM) hfix2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

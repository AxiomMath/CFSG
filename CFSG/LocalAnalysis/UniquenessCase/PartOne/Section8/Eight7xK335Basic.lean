module

import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

theorem k335_card_L {G : Type} [Group G] {L : Subgroup G} (hL : LieModel ↥L .PSL 3 2 2) :
    Nat.card L = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
    (hL.statedClassicalModel (by decide))

theorem k335_simple_L {G : Type} [Group G] {L : Subgroup G} (hL : LieModel ↥L .PSL 3 2 2) :
    IsSimpleGroup ↥L :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL

theorem k335_card_dvd {G : Type} [Group G] {L : Subgroup G} (hL : LieModel ↥L .PSL 3 2 2) :
    20160 ∣ Nat.card G :=
  k335_card_L hL ▸ Subgroup.card_subgroup_dvd_card L

private theorem k335syl_factorization_20160 : (20160).factorization 3 = 2 := by
  have h : 20160 = 3 ^ 2 * 2240 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem k335syl_card_sylow_eq_nine {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) :
    Nat.card P = 9 := by
  rw [hP.card_eq, k335_card_L hL, k335syl_factorization_20160]
  norm_num

private theorem k335syl_exists_eNine {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 2) :
    ∃ E : Subgroup X, Nat.card E = 9 ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ 3 = 1 := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have hk : Nat.card k = 4 := by rw [hcard]; norm_num
  refine ⟨(CFSG.RankThree.PartTwo.KFacts.L34.eZero k).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_eZero hk
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, CFSG.RankThree.PartTwo.KFacts.L34.commute_of_mem_eZero hk ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, CFSG.RankThree.PartTwo.KFacts.L34.pow_three_of_mem_eZero hk ha, map_one]

private theorem k335syl_isMulCommutative_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hA : IsMulCommutative A) : IsMulCommutative B :=
  IsMulCommutative.of_comm fun b₁ b₂ => by
    calc b₁ * b₂ = e (e.symm b₁ * e.symm b₂) := by simp
      _ = e (e.symm b₂ * e.symm b₁) := by rw [hA.is_comm.comm]
      _ = b₂ * b₁ := by simp

private theorem k335syl_pow_of_mulEquiv {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hA : ∀ a : A, a ^ p = 1) (b : B) : b ^ p = 1 := by
  have h := congrArg e (hA (e.symm b))
  rwa [map_pow, e.apply_symm_apply, map_one] at h

private theorem k335syl_isElemAbelian_iff_type {p : ℕ} {G : Type*} [Group G] (S : Subgroup G) :
    CFSG.Open.IsElemAbelian p S ↔ IsMulCommutative S ∧ ∀ y : S, y ^ p = 1 := by
  constructor
  · intro h
    exact ⟨h.1, fun y => Subtype.ext (by simpa using h.2 y.1 y.2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x hx => by
      have := congrArg Subtype.val (h2 ⟨x, hx⟩)
      simpa using this⟩

theorem k335_sylowL {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) :
    CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  obtain ⟨E, hEcard, hEcomm, hEpow⟩ := k335syl_exists_eNine (X := ↥L) hL
  have hEel : CFSG.Open.IsElemAbelian 3 E :=
    ⟨isMulCommutative_iff_of_setLike.mpr hEcomm, hEpow⟩
  have hLfac : (Nat.card ↥L).factorization 3 = 2 := by
    rw [k335_card_L hL, k335syl_factorization_20160]
  have hcardE : Nat.card E = 3 ^ (Nat.card ↥L).factorization 3 := by
    rw [hEcard, hLfac]
    norm_num
  have hcardP : Nat.card (P.subgroupOf L) = 3 ^ (Nat.card ↥L).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv, hP.card_eq]
  let SE : Sylow 3 ↥L := Sylow.ofCard E hcardE
  let SP : Sylow 3 ↥L := Sylow.ofCard (P.subgroupOf L) hcardP
  have hiso : E ≃* (P.subgroupOf L) := Sylow.equiv SE SP
  have hsubC : IsMulCommutative (P.subgroupOf L) :=
    k335syl_isMulCommutative_of_mulEquiv hiso hEel.1
  have hsubP : ∀ y : P.subgroupOf L, y ^ 3 = 1 :=
    k335syl_pow_of_mulEquiv hiso fun a : E => Subtype.ext (by simpa using hEel.2 a.1 a.2)
  refine ⟨?_, k335syl_card_sylow_eq_nine hL hP⟩
  exact (k335syl_isElemAbelian_iff_type P).mpr
    ⟨k335syl_isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.le) hsubC,
     k335syl_pow_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.le) hsubP⟩

private theorem k335bas_factorization_20160 : (20160).factorization 3 = 2 := by
  have h : 20160 = 3 ^ 2 * 2240 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem k335bas_card_sylow_eq_nine {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) :
    Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [hP.card_eq, k335_card_L hL, k335bas_factorization_20160]
  norm_num

private theorem k335bas_subgroupOf_eq_bot_or_top {G : Type} [Group G] {L N : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hN : N.Normal) :
    N.subgroupOf L = ⊥ ∨ N.subgroupOf L = ⊤ := by
  have : IsSimpleGroup ↥L := k335_simple_L hL
  have : (N.subgroupOf L).Normal := hN.subgroupOf L
  exact IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf L)

theorem k335_le_of_normal {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) {N : Subgroup G}
    (hN : N.Normal) (hPN : P ≤ N) : L ≤ N := by
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h9 := k335bas_card_sylow_eq_nine hL hP
    rw [hbot, Subgroup.card_bot] at h9
    omega
  rcases k335bas_subgroupOf_eq_bot_or_top hL hN with h | h
  · exfalso
    have hdisj : Disjoint N L := Subgroup.subgroupOf_eq_bot.mp h
    have hsub : P ⊓ N ≤ L ⊓ N := fun x hx => ⟨hP.le hx.1, hx.2⟩
    have hbot : P ⊓ N = ⊥ := le_bot_iff.mp (hsub.trans_eq (disjoint_iff.mp hdisj.symm))
    rw [inf_eq_left.mpr hPN] at hbot
    exact hPne hbot
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem k335_inf_normal {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P L) {N : Subgroup G}
    (hN : N.Normal) : P ⊓ N = ⊥ ∨ P ≤ N := by
  rcases k335bas_subgroupOf_eq_bot_or_top hL hN with h | h
  · left
    have hdisj : Disjoint N L := Subgroup.subgroupOf_eq_bot.mp h
    have hsub : P ⊓ N ≤ L ⊓ N := fun x hx => ⟨hP.le hx.1, hx.2⟩
    exact le_bot_iff.mp (hsub.trans_eq (disjoint_iff.mp hdisj.symm))
  · right
    exact hP.le.trans ((Subgroup.subgroupOf_eq_top (H := N) (K := L)).mp h)

private theorem k335exs_isSylowOf_top {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) : CFSG.ABGLocalTools.IsSylowOf p (S : Subgroup G) ⊤ :=
  CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩

private theorem k335exs_mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G]
    {V : Subgroup G} {b : G} (h : ∀ v ∈ V, b * v * b⁻¹ ∈ V) :
    b ∈ Subgroup.normalizer (V : Set G) := by
  have hle : V.map (MulAut.conj b).toMonoidHom ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj b).injective).ge)

theorem k335_exists_sylow {G : Type} [Group G] [Finite G] {P : Subgroup G} (hP : IsPGroup 3 P)
    (hcl : ∀ a ∈ P, ∀ g : G, g⁻¹ * a * g ∈ Subgroup.normalizer (P : Set G) → g⁻¹ * a * g ∈ P) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ P ≤ S ∧
      S ≤ Subgroup.normalizer (P : Set G) := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  let S : Subgroup G := (Q : Subgroup G)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ := k335exs_isSylowOf_top Q
  refine ⟨S, hSyl, hPQ, ?_⟩
  by_contra hnot
  let T : Subgroup G := S ⊓ Subgroup.normalizer (P : Set G)
  have hTS : T ≤ S := inf_le_left
  have hTN : T ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hPT : P ≤ T := fun x hx => ⟨hPQ hx, Subgroup.le_normalizer hx⟩
  have hnc : NormalizerCondition ↥S :=
    Group.normalizerCondition_of_isNilpotent (G := ↥S) (h := hSyl.isPGroup.isNilpotent)
  have hTsub_ne_top : T.subgroupOf S ≠ ⊤ := by
    intro htop
    exact hnot (le_trans (Subgroup.subgroupOf_eq_top.mp htop) hTN)
  have hTsub_lt : T.subgroupOf S < ⊤ := lt_top_iff_ne_top.mpr hTsub_ne_top
  obtain ⟨s, hsN, hsT⟩ := (SetLike.lt_iff_le_and_exists.mp (hnc _ hTsub_lt)).2
  have key : ∀ t ∈ T, (s : G) * t * (s : G)⁻¹ ∈ T := by
    intro t ht
    have htS : t ∈ S := hTS ht
    have hmem := (Subgroup.mem_normalizer_iff.mp hsN (⟨t, htS⟩ : ↥S)).mp ht
    exact hmem
  have hconj : ∀ a ∈ P, (s : G)⁻¹ * a * (s : G) ∈ P := by
    intro a ha
    have hsNrm : (s : G) ∈ Subgroup.normalizer (T : Set G) :=
      k335exs_mem_normalizer_of_conj_mem (V := T) (b := (s : G)) key
    have hsInvNrm : (s : G)⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).inv_mem hsNrm
    have hmem := (Subgroup.mem_normalizer_iff.mp hsInvNrm a).mp (hPT ha)
    exact hcl a ha (s : G) (hTN (by simpa using hmem))
  have hsNormP : (s : G) ∈ Subgroup.normalizer (P : Set G) := by
    have h := k335exs_mem_normalizer_of_conj_mem (V := P) (b := (s : G)⁻¹)
      fun v hv => by simpa using hconj v hv
    simpa using (Subgroup.normalizer (P : Set G)).inv_mem h
  exact hsT (show (s : G) ∈ T from ⟨s.2, hsNormP⟩)

private theorem k335exs_isElemAbelian_zpowers {G : Type} [Group G] {t : G} (ht : t ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers t) := by
  rw [Subgroup.zpowers_eq_closure]
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact ht

private theorem k335exs_disjoint_zpowers {G : Type} [Group G] {P : Subgroup G} {t : G}
    (ht : t ^ 3 = 1) (htP : t ∉ P) : Disjoint P (Subgroup.zpowers t) := by
  have ht1 : t ≠ 1 := fun h => htP (h ▸ P.one_mem)
  have hord : orderOf t = 3 := orderOf_eq_prime ht ht1
  have hcardz : Nat.card (Subgroup.zpowers t) = 3 := by rw [Nat.card_zpowers, hord]
  rw [Subgroup.disjoint_def]
  intro x hxP hxt
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    (H := (P ⊓ Subgroup.zpowers t).subgroupOf (Subgroup.zpowers t))
    (hp := ⟨by rw [hcardz]; exact Nat.prime_three⟩) with h | h
  · have hdisj : Disjoint (P ⊓ Subgroup.zpowers t) (Subgroup.zpowers t) :=
      Subgroup.subgroupOf_eq_bot.mp h
    exact Subgroup.disjoint_def.mp hdisj ⟨hxP, hxt⟩ hxt
  · have hle : Subgroup.zpowers t ≤ P ⊓ Subgroup.zpowers t := Subgroup.subgroupOf_eq_top.mp h
    exact (htP ((Subgroup.mem_inf.mp (hle (Subgroup.mem_zpowers t))).1)).elim

theorem k335_three_le_pRank {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : CFSG.Open.IsElemAbelian 3 P) (hcard : Nat.card P = 9) {t : G} (ht : t ^ 3 = 1)
    (htP : t ∉ P) (hc : ∀ x ∈ P, x * t = t * x) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have ht1 : t ≠ 1 := fun h => htP (h ▸ P.one_mem)
  have hcardz : Nat.card (Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht ht1]
  have hz : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers t) := k335exs_isElemAbelian_zpowers ht
  have hdisj : Disjoint P (Subgroup.zpowers t) := k335exs_disjoint_zpowers ht htP
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (P : Set G)
      (Subgroup.mem_centralizer_iff.mpr hc)
  have hcard_sup : Nat.card (P ⊔ Subgroup.zpowers t : Subgroup G) = 3 ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P
      (Subgroup.zpowers t) hnorm hdisj, hcard, hcardz]
    norm_num
  have hE : CFSG.Open.IsElemAbelian 3 (P ⊔ Subgroup.zpowers t) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hP hz fun a ha b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (hc a ha) k).eq
  exact CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num) le_top hE hcard_sup

theorem k335_exists_mem_center {G : Type} [Group G] [Finite G] {P S : Subgroup G}
    (hS : IsPGroup 3 S) (hPS : P ≤ S) (hSN : S ≤ Subgroup.normalizer (P : Set G)) (hP : P ≠ ⊥) :
    ∃ x ∈ P, x ≠ 1 ∧ ∀ y ∈ S, x * y = y * x := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hnil : Group.IsNilpotent ↥S := hS.isNilpotent
  have hnormal : (P.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPS).mpr hSN
  have hHne : P.subgroupOf S ≠ ⊥ := by
    intro hbot
    have hdisj : Disjoint P S := Subgroup.subgroupOf_eq_bot.mp hbot
    have hbot' : P ⊓ S = ⊥ := disjoint_iff.mp hdisj
    rw [inf_eq_left.mpr hPS] at hbot'
    exact hP hbot'
  have hcenter : P.subgroupOf S ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter
  refine ⟨(x.1 : G), x.2.1, ?_, ?_⟩
  · intro hx1
    exact hxne (Subtype.ext (Subtype.ext hx1))
  · intro y hy
    have hcomm := (Subgroup.mem_center_iff.mp x.2.2) ⟨y, hy⟩
    exact congrArg (fun z : ↥S => (z : G)) hcomm.symm

private theorem k335bas_not_isMulCommutative_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ¬ IsMulCommutative G := fun hc =>
  h ((@Group.is_simple_iff_prime_card G _ hc).1 inferInstance)

private theorem k335bas_commutator_eq_top {G : Type} [Group G] {L : Subgroup G}
    (hL : LieModel ↥L .PSL 3 2 2) : commutator ↥L = ⊤ := by
  have : IsSimpleGroup ↥L := k335_simple_L hL
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥L)).resolve_left fun hb =>
    k335bas_not_isMulCommutative_of_simple (by rw [k335_card_L hL]; norm_num)
      ((commutator_eq_bot_iff ↥L).1 hb)

theorem k335_le_commutator {G : Type} [Group G] {L : Subgroup G} (hL : LieModel ↥L .PSL 3 2 2) :
    L ≤ commutator G := by
  have htop : commutator ↥L = ⊤ := k335bas_commutator_eq_top hL
  calc
    L = (⊤ : Subgroup ↥L).map L.subtype := by rw [Subgroup.map_top, Subgroup.range_subtype]
    _ = (commutator ↥L).map L.subtype := by rw [htop]
    _ = ⁅L, L⁆ := Subgroup.map_subtype_commutator L
    _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator G := (commutator_def G).symm

theorem k335_two_le_pRank {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : CFSG.Open.IsElemAbelian 3 P) (hcard : Nat.card P = 9) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
  CFSG.SectionRank.le_pRank (by norm_num) le_top hP (by rw [hcard]; norm_num)

theorem k335_normalizer_le_gamma {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : CFSG.Open.IsElemAbelian 3 P) (hcard : Nat.card P = 9) :
    Subgroup.normalizer (P : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 P := by
  have h2 : 2 ≤ CFSG.Open.pRank 3 P :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hP (by rw [hcard]; norm_num)
  exact le_sSup ⟨P, le_rfl, by omega, rfl⟩

theorem k335_ne_bot {G : Type} [Group G] {P : Subgroup G} (hcard : Nat.card P = 9) : P ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at hcard
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

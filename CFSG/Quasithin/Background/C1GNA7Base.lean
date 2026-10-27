
module

public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.A3Structure318Quot
public import CFSG.Quasithin.Background.A3ComponentsAmbient

@[expose] public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.SectionRank

namespace C1GN

theorem two_le_pRank_alt7 :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 7))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsa : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2).sign = 1 :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).sign
  have hsb : (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 3 5).sign = 1 :=
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).sign
  let a : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 0 2,
    Equiv.Perm.mem_alternatingGroup.2 hsa⟩
  let b : alternatingGroup (Fin 7) := ⟨Equiv.swap 3 4 * Equiv.swap 3 5,
    Equiv.Perm.mem_alternatingGroup.2 hsb⟩
  have ha : orderOf a = 3 := by
    rw [← Subgroup.orderOf_coe a]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (0 : Fin 7)) (by decide) (by decide)
      (by decide)).orderOf
  have hb : orderOf b = 3 := by
    rw [← Subgroup.orderOf_coe b]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := (3 : Fin 7)) (by decide) (by decide)
      (by decide)).orderOf
  have hdisj : Equiv.Perm.Disjoint (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2)
      (Equiv.swap 3 4 * Equiv.swap 3 5) := by
    intro x
    fin_cases x <;> simp [Equiv.swap_apply_def]
  have hcomm : Commute a b := Subtype.ext hdisj.commute.eq
  have hb3 : (b : Equiv.Perm (Fin 7)) 3 ≠ 3 := by
    show (Equiv.swap (3 : Fin 7) 4 * Equiv.swap 3 5 : Equiv.Perm (Fin 7)) 3 ≠ 3
    decide
  have ha3' : (a : Equiv.Perm (Fin 7)) 3 = 3 := by
    show (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 0 2 : Equiv.Perm (Fin 7)) 3 = 3
    decide
  have ha3 : ∀ k : ℤ, ((a ^ k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) 3 = 3 := by
    intro k
    rw [SubgroupClass.coe_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ha3' k
  have hE0c : ∀ e ∈ (⊥ : Subgroup (alternatingGroup (Fin 7))), Commute e a := by
    intro e he
    rw [Subgroup.mem_bot.1 he]
    exact Commute.one_left a
  have ha1 : a ∉ (⊥ : Subgroup (alternatingGroup (Fin 7))) := by
    intro h
    have : a = 1 := Subgroup.mem_bot.1 h
    rw [this, orderOf_one] at ha
    omega
  obtain ⟨hE1, hc1⟩ := exists_elemAbelian_sup_zpowers (isElemAbelian_bot 3) ha hE0c ha1
  have hE1c : ∀ e ∈ (⊥ ⊔ Subgroup.zpowers a : Subgroup (alternatingGroup (Fin 7))),
      Commute e b := by
    intro e he
    rw [bot_sup_eq] at he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact hcomm.zpow_left k
  have hb1 : b ∉ (⊥ ⊔ Subgroup.zpowers a : Subgroup (alternatingGroup (Fin 7))) := by
    intro h
    rw [bot_sup_eq] at h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hb3
    rw [← hk]
    exact ha3 k
  obtain ⟨hE2, hc2⟩ := exists_elemAbelian_sup_zpowers hE1 hb hE1c hb1
  have hcard : Nat.card ↥((⊥ ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers b :
      Subgroup (alternatingGroup (Fin 7))) = 3 ^ 2 := by
    rw [hc2, hc1, Subgroup.card_bot]
    norm_num
  exact le_pRank (by norm_num) le_top hE2 hcard

theorem isSubnormal_of_isBlock2 {G : Type} [Group G] {X L : Subgroup G} (hL : IsBlock2 X L) :
    IsSubnormal L X := by
  have h1 : IsSubnormal (L.subgroupOf X) ⊤ := A3.subnormal_top_iff.2 hL.2.2
  have h2 := A3.subnormal_map X.subtype h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hL.2.1, Subgroup.map_top, Subgroup.range_subtype] at h2

section Normality

variable {G : Type} [Group G] [Finite G]

theorem isSQTKTC_iff_sqtkGroup {X : Subgroup G} : IsSQTKTC X ↔ SQTKGroup ↥X :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem mem_cComp_of_exceptionalA7 {X L : Subgroup G} (hL : IsBlock2 X L)
    (hexc : IsExcA7Block L) : L ∈ cComp X :=
  mem_cComp_of_short hL.1 (isQuasisimple_of_isExceptionalA7Block hexc) (isSubnormal_of_isBlock2 hL)

theorem le_pRank_three_of_alt_quotient {L : Subgroup G} {m k : ℕ}
    (α : ↥L →* alternatingGroup (Fin m)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L)
    (hk : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin m)))) :
    k ≤ CFSG.Open.pRank 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have h2 := pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
    rw [hj]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h3 := pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥L) hN
  have h4 := pRank_top_subtype (p := 3) L
  omega

theorem two_le_pRank_exceptionalA7 {L : Subgroup G} (hexc : IsExcA7Block L) :
    2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hexc
  exact le_pRank_three_of_alt_quotient α hα hker two_le_pRank_alt7

theorem three_le_pRank_of_isAltType {L : Subgroup G} {m : ℕ} (hm : 9 ≤ m) (h : IsAltType L m) :
    3 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨α, hα, hker, -⟩ := h
  exact le_pRank_three_of_alt_quotient α hα hker (three_le_pRank_alternating hm)

theorem le_normalizer_of_exceptionalA7 {X L : Subgroup G} (hSQ : IsSQTKTC X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hL : IsBlock2 X L)
    (hexc : IsExcA7Block L) : X ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLc : L ∈ cComp X := mem_cComp_of_exceptionalA7 hL hexc
  have hL' : L.subgroupOf X ∈ cComp (⊤ : Subgroup ↥X) := subgroupOf_mem_cComp hLc
  have hrank : 1 < CFSG.Open.pRank 3 (L.subgroupOf X) := by
    have e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.2.1
    have h1 := pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    have h2 := pRank_top_subtype (p := 3) (L.subgroupOf X)
    have h3 := pRank_top_subtype (p := 3) L
    have h4 := two_le_pRank_exceptionalA7 hexc
    omega
  have hnorm : (L.subgroupOf X).Normal :=
    A318.normal_of_pRank_gt_one (isSQTKTC_iff_sqtkGroup.1 hSQ) h38 hL' Nat.prime_three (by norm_num) hrank
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL.2.1).1 hnorm

end Normality

end C1GN

end CFSG.Quasithin

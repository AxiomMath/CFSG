module

import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1424

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

theorem le_pCore_two_of_commutator_action {Γ₀ : Type} [Group Γ₀] [Finite Γ₀]
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → localRank r Γ₀ < 3) (hs : Group.IsSolvable Γ₀)
    (h3 : ¬ 3 ∣ Nat.card Γ₀) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5)
    {U E : Subgroup Γ₀} (hU2 : IsPGroup 2 U) (hE : CFSG.Assembly.IsElemAbelian p E)
    (hEU : E ≤ Subgroup.normalizer (U : Set Γ₀)) (hUE : ⁅U, E⁆ = U) :
    U ≤ CFSG.pCore 2 Γ₀ := by
  by_contra hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set P₂ := CFSG.pCore 2 Γ₀ with hP₂
  set Γ := Γ₀ ⧸ P₂
  set π := QuotientGroup.mk' P₂ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective P₂
  have hP₂2 : IsPGroup 2 P₂ := CFSG.pCore_isPGroup
  have hlocΓ : ∀ r : ℕ, r.Prime → 3 < r → localRank r Γ < 3 := by
    intro r hr hr3
    have hr2 : r ≠ 2 := by omega
    have hrP : ¬ r ∣ Nat.card P₂ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₂2
      rw [hk]
      intro h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    exact (Classical2.localRank_quotient_le hr hr2 P₂ hrP).trans_lt (hloc r hr hr3)
  set U' := U.map π with hU'
  set E' := E.map π with hE'
  have hU'1 : U' ≠ ⊥ := by
    intro h
    apply hU
    rw [hU', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have hU'2 : IsPGroup 2 U' := hU2.map π
  have hU'E : ⁅U', E'⁆ = U' := by rw [hU', hE', ← Subgroup.map_commutator, hUE]
  have hE'U : E' ≤ Subgroup.normalizer (U' : Set Γ) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map π)
  have : Group.IsSolvable Γ := Group.isSolvable_of_surjective hπs
  have htop : Group.IsSolvable (⊤ : Subgroup Γ) :=
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := Γ)).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have htop3 : ¬ 3 ∣ Nat.card (⊤ : Subgroup Γ) := by
    rw [Subgroup.card_top]
    exact fun h => h3 (h.trans (Subgroup.card_quotient_dvd_card P₂))
  have htopO2 : CFSG.pCore 2 (⊤ : Subgroup Γ) = ⊥ := by
    have h1 := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := Γ))
    rw [ABGLocalTools.pCore_quotient_pCore_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h1
  obtain ⟨r, hr, hr3, hrU⟩ := Sec16.Proof169.exists_prime_not_le_centralizer_pCore htop htop3
    htopO2 le_top hU'2 hU'1
  have : Fact r.Prime := ⟨hr⟩
  set Q := (CFSG.pCore r (⊤ : Subgroup Γ)).map (⊤ : Subgroup Γ).subtype with hQ
  have hQr : IsPGroup r Q := CFSG.pCore_isPGroup.map _
  have hQn : Q.Normal := by
    refine (CFSG.pCore_normal (p := r) (G := (⊤ : Subgroup Γ))).map _ ?_
    intro g
    exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
  have hNQ : ∀ H : Subgroup Γ, H ≤ Subgroup.normalizer (Q : Set Γ) := fun H => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hQn]
    exact le_top
  obtain ⟨x, hxE, hxQ⟩ : ∃ x ∈ E', ¬ ⁅U', Subgroup.zpowers x⁆ ≤
      Subgroup.centralizer (Q : Set Γ) := by
    by_contra hall
    push Not at hall
    apply hrU
    rw [← hU'E, Subgroup.commutator_le]
    intro u hu x hx
    exact hall x hx (Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers x))
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hxQ
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    exact bot_le
  have hxp : x ^ p = 1 := by
    obtain ⟨y, hy, rfl⟩ := hxE
    rw [← map_pow, hE.2 y hy, map_one]
  have hXp : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp hx1
  have hXpg : IsPGroup p (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by rw [hXp, pow_one])
  have hXU : Subgroup.zpowers x ≤ Subgroup.normalizer (U' : Set Γ) :=
    Subgroup.zpowers_le.mpr (hE'U hxE)
  have hcop : p.Coprime (Nat.card U') := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU'2
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  set U'' := ⁅U', Subgroup.zpowers x⁆ with hU''
  have hU''U : U'' ≤ U' := Subgroup.le_normalizer_iff_commutator_le_right.mp hXU |>.trans'
    (by rw [Subgroup.commutator_comm])
  have hU''2 : IsPGroup 2 U'' := hU'2.to_le hU''U
  have hU''X : ⁅U'', Subgroup.zpowers x⁆ = U'' :=
    SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp _ U' hXpg hXU hcop
  have hXU'' : Subgroup.zpowers x ≤ Subgroup.normalizer (U'' : Set Γ) :=
    Sec6.le_normalizer_commutator_right U' (Subgroup.zpowers x)
  exact Sec16.Proof169.false_of_commutator_action hlocΓ hp hp3 hp5 hr hr3 hXp hU''2 hU''X hXU''
    hQr (hNQ _) (hNQ _) hxQ

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_two_of_commutator_action
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → localRank r G < 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hp5 : p ≠ 5) {N U E : Subgroup G} (hNs : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N)
    (hU2 : IsPGroup 2 U) (hUN : U ≤ N) (hEN : E ≤ N) (hE : CFSG.Assembly.IsElemAbelian p E)
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) (hUE : ⁅U, E⁆ = U) :
    U ≤ CFSG.Open.pCoreOf 2 N := by
  have hlocN : ∀ r : ℕ, r.Prime → 3 < r → localRank r N < 3 := fun r hr hr3 =>
    (localRank_subgroup_le hr N).trans_lt (hloc r hr hr3)
  have hU2' : IsPGroup 2 (U.subgroupOf N) := hU2.comap_subtype
  have hcomm : ∀ y ∈ E, ∀ z ∈ E, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hE' : CFSG.Assembly.IsElemAbelian p (E.subgroupOf N) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hy))
  have hEU' : E.subgroupOf N ≤ Subgroup.normalizer ((U.subgroupOf N : Subgroup N) : Set N) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hyE : (y : G) ∈ E := Subgroup.mem_subgroupOf.mp hy
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp (hEU hyE) (z : G)
  have hUE' : ⁅U.subgroupOf N, E.subgroupOf N⁆ = U.subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUN,
      Subgroup.map_subgroupOf_eq_of_le hEN]
    exact hUE
  have hle := le_pCore_two_of_commutator_action hlocN hNs (by simpa using hN3) hp hp3 hp5 hU2' hE'
    hEU' hUE'
  rw [← Subgroup.map_subgroupOf_eq_of_le hUN]
  have := Subgroup.map_mono (f := N.subtype) hle
  assumption

end CFSG.RankThree.PartTwo.Sec15.Proof1424

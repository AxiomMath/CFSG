module

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.RankThree.PartOne.K1214.PGroupCyclic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

private theorem exists_pow_three_mem_center_of_normal {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 3 P) {V : Subgroup P} [V.Normal] (hV : V ≠ ⊥) :
    ∃ w ∈ V, w ≠ 1 ∧ w ^ 3 = 1 ∧ w ∈ Subgroup.center P := by
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have h1 : V ⊓ Subgroup.center P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hV
  haveI : Nontrivial ↥(V ⊓ Subgroup.center P) := (Subgroup.nontrivial_iff_ne_bot _).mpr h1
  obtain ⟨n, hn, hcard⟩ :=
    (hP.to_subgroup (V ⊓ Subgroup.center P)).nontrivial_iff_card.mp inferInstance
  have h3 : 3 ∣ Nat.card ↥(V ⊓ Subgroup.center P) := hcard ▸ dvd_pow_self 3 hn.ne'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨(x : P), x.2.1, ?_, ?_, x.2.2⟩
  · intro h
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at hx
    omega
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Subtype.val this

theorem exists_isCyclic_sylow {Q : Type*} [Group Q] [Finite Q] {Y At : Subgroup Q} [Y.Normal]
    (hAt : IsPGroup 3 At) {x : Q} (hxA : x ∈ At) (hxY : x ∈ Y) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hR1 : ∀ y ∈ Y, y * x = x * y → y ^ 3 = 1 → y ∈ Subgroup.zpowers x) :
    ∃ P : Sylow 3 Y, IsCyclic (P : Subgroup Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hAS⟩ := hAt.exists_le_sylow
  obtain ⟨P, hP⟩ := CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq Y S
  have hxS : x ∈ (S : Subgroup Q) := hAS hxA
  have hV : Y.subgroupOf (S : Subgroup Q) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨⟨x, hxS⟩, hxY⟩, fun h => hx1 (congrArg
      (fun z : ↥(Y.subgroupOf (S : Subgroup Q)) => ((z : ↥S) : Q)) h)⟩
  haveI : (Y.subgroupOf (S : Subgroup Q)).Normal := inferInstance
  obtain ⟨w, hwV, hw1, hw3, hwc⟩ := exists_pow_three_mem_center_of_normal S.isPGroup' hV
  have hwY : ((w : ↥S) : Q) ∈ Y := hwV
  have hw3' : ((w : ↥S) : Q) ^ 3 = 1 := by simpa using congrArg (fun z : ↥S => (z : Q)) hw3
  have hw1' : ((w : ↥S) : Q) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hwx : ((w : ↥S) : Q) * x = x * ((w : ↥S) : Q) :=
    (congrArg (fun z : ↥S => (z : Q)) (Subgroup.mem_center_iff.mp hwc ⟨x, hxS⟩)).symm
  have hwmem : ((w : ↥S) : Q) ∈ Subgroup.zpowers x := hR1 _ hwY hwx hw3'
  have hzeq : Subgroup.zpowers ((w : ↥S) : Q) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwmem) (le_of_eq (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hw3' hw1',
        orderOf_eq_prime hx3 hx1]))
  have hxw : x ∈ Subgroup.zpowers ((w : ↥S) : Q) := hzeq ▸ Subgroup.mem_zpowers x
  have hxc : ∀ s ∈ (S : Subgroup Q), s * x = x * s := by
    intro s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxw
    have hsw : Commute s ((w : ↥S) : Q) :=
      congrArg (fun z : ↥S => (z : Q)) (Subgroup.mem_center_iff.mp hwc ⟨s, hs⟩)
    rw [← hk]
    exact (hsw.zpow_right k).eq
  refine ⟨P, ?_⟩
  have hmemP : ∀ g : Y, g ∈ (P : Subgroup Y) ↔ (g : Q) ∈ (S : Subgroup Q) := by
    intro g
    rw [hP]
    exact Subgroup.mem_subgroupOf
  let b : ↥(P : Subgroup Y) := ⟨⟨x, hxY⟩, (hmemP _).mpr hxS⟩
  have hb3 : b ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa using hx3))
  have hb1 : b ≠ 1 := fun h => hx1
    (congrArg (fun z : ↥(P : Subgroup Y) => ((z : ↥Y) : Q)) h)
  refine CFSG.RankThree.PartOne.K1214.isCyclic_of_pow_eq_one_subset Nat.prime_three
    (by norm_num) P.isPGroup' (b := b) (orderOf_eq_prime hb3 hb1) ?_
  intro g hg
  have hg3 : ((g : ↥Y) : Q) ^ 3 = 1 := by
    simpa using congrArg (fun z : ↥(P : Subgroup Y) => ((z : ↥Y) : Q)) hg
  have hgS : ((g : ↥Y) : Q) ∈ (S : Subgroup Q) := (hmemP _).mp g.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (hR1 _ (g : ↥Y).2 (hxc _ hgS) hg3)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (Subtype.ext (by simpa [b] using hk))⟩

theorem not_mem_center_of_unique_three {Y : Type*} [Group Y] {x : Y}
    (hR1 : ∀ y : Y, y * x = x * y → y ^ 3 = 1 → y ∈ Subgroup.zpowers x)
    (hI : ∃ u : Y, u ^ 3 = 1 ∧ ∃ y : Y, u * y ≠ y * u) : x ∉ Subgroup.center Y := by
  intro hx
  obtain ⟨u, hu3, y, huy⟩ := hI
  have hu : u ∈ Subgroup.center Y := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hR1 u (Subgroup.mem_center_iff.mp hx u) hu3)
    exact Subgroup.zpow_mem _ hx k
  exact huy (Subgroup.mem_center_iff.mp hu y).symm

theorem center_eq_bot_of_unique_three {Y : Type*} [Group Y] [Finite Y] {x : Y} (hx3 : x ^ 3 = 1)
    (hR1 : ∀ y : Y, y * x = x * y → y ^ 3 = 1 → y ∈ Subgroup.zpowers x)
    (hZ : IsPGroup 3 (Subgroup.center Y))
    (hI : ∃ u : Y, u ^ 3 = 1 ∧ ∃ y : Y, u * y ≠ y * u) : Subgroup.center Y = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx : x ∉ Subgroup.center Y := not_mem_center_of_unique_three hR1 hI
  have hx1 : x ≠ 1 := fun h => hx (h ▸ one_mem _)
  by_contra hne
  haveI : Nontrivial ↥(Subgroup.center Y) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have h3 : 3 ∣ Nat.card ↥(Subgroup.center Y) := hcard ▸ dvd_pow_self 3 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hzc : (z : Y) ∈ Subgroup.center Y := z.2
  have hz3 : (z : Y) ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg Subtype.val this
  have hz1 : (z : Y) ≠ 1 := fun h => by
    have hz' : z = 1 := Subtype.ext h
    rw [hz', orderOf_one] at hz
    omega
  have hzmem : (z : Y) ∈ Subgroup.zpowers x :=
    hR1 _ (Subgroup.mem_center_iff.mp hzc x).symm hz3
  have hzeq : Subgroup.zpowers (z : Y) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzmem) (le_of_eq (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hz3 hz1,
        orderOf_eq_prime hx3 hx1]))
  apply hx
  have hxz : x ∈ Subgroup.zpowers (z : Y) := hzeq ▸ Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
  rw [← hk]
  exact Subgroup.zpow_mem _ hzc k

theorem pRank_top_le_one_of_isCyclic_sylow {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p Y) (hP : IsCyclic (P : Subgroup Y)) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 1 := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (⊤ : Subgroup Y)
  obtain ⟨R, hER⟩ := hE.isPGroup.exists_le_sylow
  haveI : IsCyclic (R : Subgroup Y) := isCyclic_of_surjective (Sylow.equiv P R)
    (Sylow.equiv P R).surjective
  exact (CFSG.SectionRank.le_pRank hp.out.one_lt hER hE hcard).trans
    (CFSG.SectionRank.pRank_le_one_of_isCyclic hp.out inferInstance)

theorem one_le_pRank_top_of_pow_three {Y : Type*} [Group Y] [Finite Y] {u : Y} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  exact CFSG.SectionRank.le_pRank (by norm_num) (le_top : Subgroup.zpowers u ≤ ⊤)
    (CFSG.Open.isElemAbelian_zpowers hu3)
    (by rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1, pow_one])

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

module

public import CFSG.Timmesfeld.RootInvolutionConj
public import CFSG.Timmesfeld.Bridge.RootSetsSolv
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X]

abbrev dSet (S : Subgroup X) : Set X :=
  Group.conjugatesOfSet ((S : Set X) \ {1})

structure Hyp (X : Type) [Group X] (S : Subgroup X) : Prop where
  elem : IsElemAbelian 2 S
  card : 2 < Nat.card S
  ti : CFSG.CGT.Timmesfeld75.IsTI S
  normalClosure : Subgroup.normalClosure (S : Set X) = ⊤
  two : CFSG.pCore 2 X = ⊥
  odd : fusionOddCore X ≤ Subgroup.center X
  root : CFSG.Timmesfeld.IsRootInvolutionSet (dSet S)
  pair : ∀ g : X, IsPGroup 2 ↥(S ⊔ conjSubgroup S g) →
    ∀ a ∈ S, ∀ b ∈ conjSubgroup S g, a * b = b * a

variable {S : Subgroup X}

theorem mem_dSet_iff {y : X} : y ∈ dSet S ↔ ∃ x ∈ S, x ≠ 1 ∧ IsConj x y := by
  rw [dSet, Group.mem_conjugatesOfSet_iff]
  constructor
  · rintro ⟨x, ⟨hxS, hx1⟩, hxy⟩
    exact ⟨x, hxS, by simpa using hx1, hxy⟩
  · rintro ⟨x, hxS, hx1, hxy⟩
    exact ⟨x, ⟨hxS, by simpa using hx1⟩, hxy⟩

theorem mem_dSet_of_mem {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) : s ∈ dSet S := by
  apply Group.subset_conjugatesOfSet
  exact ⟨hs, by simpa using hs1⟩

theorem conj_mem_dSet (g : X) {y : X} (hy : y ∈ dSet S) : g * y * g⁻¹ ∈ dSet S :=
  Group.conj_mem_conjugatesOfSet (s := (S : Set X) \ {1}) (c := g) hy

namespace Hyp

theorem closure_dSet (h : Hyp X S) : Subgroup.closure (dSet S) = ⊤ := by
  have hsub : Group.conjugatesOfSet (S : Set X) ⊆ (dSet S ∪ {1} : Set X) := by
    intro y hy
    obtain ⟨x, hxS, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    by_cases hx1 : x = 1
    · right
      obtain ⟨c, hc⟩ := isConj_iff.mp hxy
      simpa [Set.mem_singleton_iff, hx1] using hc.symm
    · left
      rw [mem_dSet_iff]
      exact ⟨x, hxS, hx1, hxy⟩
  have hle : Subgroup.closure (Group.conjugatesOfSet (S : Set X)) ≤
      Subgroup.closure (dSet S) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hsub hy with hy' | hy'
    · exact Subgroup.subset_closure hy'
    · rw [Set.mem_singleton_iff] at hy'
      rw [hy']
      exact Subgroup.one_mem _
  rw [← h.normalClosure, Subgroup.normalClosure]
  exact le_antisymm (Subgroup.closure_mono (Group.conjugatesOfSet_mono (Set.sdiff_subset))) hle

theorem eq_bot_of_normal_isPGroup (h : Hyp X S) (N : Subgroup X) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have hle : N ≤ CFSG.pCore 2 X := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN h2
  rw [h.two] at hle
  exact le_bot_iff.mp hle

theorem odd_card_center [Finite X] (h : Hyp X S) : Odd (Nat.card (Subgroup.center X)) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center X)) 2 h2
  have hzX : orderOf (z : X) = 2 := (Subgroup.orderOf_coe z).trans hz
  have hzcenter : (z : X) ∈ Subgroup.center X := z.2
  have hNnorm : (Subgroup.zpowers (z : X)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  have hNp : IsPGroup 2 (Subgroup.zpowers (z : X)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hzX]
    norm_num
  have hNbot := h.eq_bot_of_normal_isPGroup _ hNnorm hNp
  have hz1 : (z : X) = 1 := by
    have hmem : (z : X) ∈ (⊥ : Subgroup X) := hNbot ▸ Subgroup.mem_zpowers (z : X)
    exact Subgroup.mem_bot.mp hmem
  rw [hz1, orderOf_one] at hzX
  exact absurd hzX (by norm_num)

theorem not_mem_center [Finite X] (h : Hyp X S) {d : X} (hd : d ∈ dSet S) :
    d ∉ Subgroup.center X := by
  intro hdc
  have h2 : 2 ∣ Nat.card (Subgroup.center X) := by
    have hdiv := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hdc
    rwa [h.root.orderOf_eq_two hd] at hdiv
  exact (Nat.not_even_iff_odd.mpr h.odd_card_center) (even_iff_two_dvd.mpr h2)

theorem inf_center_eq_bot [Finite X] (h : Hyp X S) : S ⊓ Subgroup.center X = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxS, hxC⟩ := hx
  have hx2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.elem.2 x hxS)
  have hxC' : orderOf x ∣ Nat.card (Subgroup.center X) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center X) hxC
  rcases (Nat.dvd_prime Nat.prime_two).mp hx2 with h1 | h1
  · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  · exfalso
    rw [h1] at hxC'
    exact (Nat.not_even_iff_odd.mpr h.odd_card_center) (even_iff_two_dvd.mpr hxC')

theorem exists_odd_partner [Finite X] (h : Hyp X S) {a : X} (ha : a ∈ dSet S) :
    ∃ c ∈ dSet S, Odd (orderOf (a * c)) ∧ a * c ≠ 1 := by
  by_contra hne
  rw [not_exists] at hne
  have hac1 : ∀ c ∈ dSet S, Odd (orderOf (a * c)) → a * c = 1 := by
    intro c hc ho
    by_contra h1
    exact hne c ⟨hc, ho, h1⟩
  have ha2 : a * a = 1 := h.root.mul_self_eq_one ha
  have hmem : a ∈ CFSG.pCore 2 X := by
    rw [CFSG.BaerSuzuki.baer_suzuki_iff]
    intro g
    have hcD : g * a * g⁻¹ ∈ dSet S := conj_mem_dSet g ha
    have hc2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := h.root.mul_self_eq_one hcD
    apply CFSG.Timmesfeld.isPGroup_two_closure_pair ha2 hc2
    rcases h.root.orderOf_mul ha hcD with h2 | h4 | hodd
    · rw [show (2 : ℕ) ^ 2 = 2 * 2 from by norm_num, pow_mul, ← h2, pow_orderOf_eq_one, one_pow]
    · rw [show (2 : ℕ) ^ 2 = 4 from by norm_num, ← h4, pow_orderOf_eq_one]
    · rw [hac1 _ hcD hodd, one_pow]
  rw [h.two] at hmem
  exact h.root.ne_one ha (Subgroup.mem_bot.mp hmem)

theorem isConj_of_mem [Finite X] (h : Hyp X S) {s t : X} (hs : s ∈ S) (ht : t ∈ S)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) : IsConj s t := by
  by_cases hst : s = t
  · rw [hst]
  · have hs2 : s * s = 1 := by simpa [pow_two] using h.elem.2 s hs
    have hstS : s * t ∈ S := S.mul_mem hs ht
    have hst1 : s * t ≠ 1 := by
      intro h1
      apply hst
      have ht_eq : t = s⁻¹ := by
        calc t = s⁻¹ * (s * t) := by group
          _ = s⁻¹ * 1 := by rw [h1]
          _ = s⁻¹ := by rw [mul_one]
      rw [ht_eq, inv_eq_of_mul_eq_one_right hs2]
    have hstD : s * t ∈ dSet S := mem_dSet_of_mem hstS hst1
    have hcomm : s * t = t * s := by
      have := h.elem.1.is_comm.comm (⟨s, hs⟩ : S) ⟨t, ht⟩
      simpa using this
    obtain ⟨g, hg⟩ := CFSG.Timmesfeld.exists_conj_of_commuting_pair h.root
      (fun g x hx => conj_mem_dSet g hx) (fun a ha => h.exists_odd_partner ha)
      (mem_dSet_of_mem hs hs1) (mem_dSet_of_mem ht ht1) hst hcomm hstD
    exact isConj_iff.2 ⟨g, hg⟩

theorem exists_ne_ne_one (h : Hyp X S) :
    ∃ s ∈ S, ∃ t ∈ S, s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t := by
  classical
  have hSfin : Finite S := (Nat.card_pos_iff.mp (lt_trans (by norm_num) h.card)).2
  haveI : Finite S := hSfin
  letI : Fintype S := Fintype.ofFinite S
  have h2lt : 2 < (Finset.univ : Finset S).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact h.card
  obtain ⟨a, _, b, _, c, _, hab, hac, hbc⟩ := Finset.two_lt_card.mp h2lt
  rcases eq_or_ne (a : X) 1 with ha1 | ha1
  · exact ⟨b, b.2, c, c.2, fun h => hab (Subtype.ext (by rw [h, ha1])),
      fun h => hac (Subtype.ext (by rw [h, ha1])), fun h => hbc (Subtype.ext h)⟩
  · rcases eq_or_ne (b : X) 1 with hb1 | hb1
    · exact ⟨a, a.2, c, c.2, ha1, fun h => hbc (Subtype.ext (by rw [h, hb1])),
        fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, ha1, hb1, fun h => hab (Subtype.ext h)⟩

theorem exists_isClass [Finite X] (h : Hyp X S) : ∃ d₀ : X, dSet S = {g | IsConj d₀ g} := by
  obtain ⟨s, hs, _, _, hs1, _, _⟩ := h.exists_ne_ne_one
  refine ⟨s, ?_⟩
  ext y
  rw [mem_dSet_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hxS, hx1, hxy⟩
    exact (h.isConj_of_mem hs hxS hs1 hx1).trans hxy
  · rintro hsy
    exact ⟨s, hs, hs1, hsy⟩

theorem meetsSq (h : Hyp X S) :
    ∃ u ∈ dSet S, ∃ v ∈ dSet S, u ≠ v ∧ Commute u v ∧ u * v ∈ dSet S := by
  obtain ⟨s, hs, t, ht, hs1, ht1, hst⟩ := h.exists_ne_ne_one
  have hs2 : s * s = 1 := by simpa [pow_two] using h.elem.2 s hs
  have hstS : s * t ∈ S := S.mul_mem hs ht
  have hst1 : s * t ≠ 1 := by
    intro h1
    apply hst
    have ht_eq : t = s⁻¹ := by
      calc t = s⁻¹ * (s * t) := by group
        _ = s⁻¹ * 1 := by rw [h1]
        _ = s⁻¹ := by rw [mul_one]
    rw [ht_eq, inv_eq_of_mul_eq_one_right hs2]
  have hcomm : Commute s t := by
    have h2 := h.elem.1.is_comm.comm (⟨s, hs⟩ : S) ⟨t, ht⟩
    exact congrArg Subtype.val h2
  exact ⟨s, mem_dSet_of_mem hs hs1, t, mem_dSet_of_mem ht ht1, hst, hcomm,
    mem_dSet_of_mem hstS hst1⟩

theorem le_center_of_isSolvable [Finite X] (h : Hyp X S) (N : Subgroup X) (hN : N.Normal)
    (hs : Group.IsSolvable N) : N ≤ Subgroup.center X := by
  obtain ⟨s, hsS, t, htS, hs1, ht1, hst⟩ := h.exists_ne_ne_one
  have hs2 : s * s = 1 := by simpa [pow_two] using h.elem.2 s hsS
  have hstS : s * t ∈ S := S.mul_mem hsS htS
  have hst1 : s * t ≠ 1 := by
    intro h1
    apply hst
    have ht_eq : t = s⁻¹ := by
      calc t = s⁻¹ * (s * t) := by group
        _ = s⁻¹ * 1 := by rw [h1]
        _ = s⁻¹ := by rw [mul_one]
    rw [ht_eq, inv_eq_of_mul_eq_one_right hs2]
  have hcomm : Commute s t := by
    have h2 := h.elem.1.is_comm.comm (⟨s, hsS⟩ : S) ⟨t, htS⟩
    exact congrArg Subtype.val h2
  exact CFSG.Timmesfeld.Bridge.le_center_of_isSolvable h.exists_isClass h.root h.closure_dSet
    (mem_dSet_of_mem hsS hs1) (mem_dSet_of_mem htS ht1) hst hcomm
    (mem_dSet_of_mem hstS hst1) h.eq_bot_of_normal_isPGroup hN hs

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI

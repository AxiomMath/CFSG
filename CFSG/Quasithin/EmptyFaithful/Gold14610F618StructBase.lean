module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Props

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace Gold14610

namespace Struct

@[expose] def Idx2Data (D : Type) [Group D] : Prop :=
  ∃ Kb : Subgroup D, Kb.Normal ∧ F618Core ↥Kb ∧ (∀ x : D, x ^ 2 ∈ Kb) ∧
    (IsSimpleGroup ↥Kb ∨ CFSG.IsQuasisimple ↥Kb)

variable {D : Type} [Group D] [Finite D]

theorem sq_mem_of_index_le_two {Kb : Subgroup D} [Kb.Normal] (h : Kb.index ≤ 2) (x : D) :
    x ^ 2 ∈ Kb := by
  have h0 : Kb.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : Kb.index = 1 ∨ Kb.index = 2 := by omega
  rcases h12 with h1 | h2
  · have hx : x ∈ Kb := by
      rw [Subgroup.index_eq_one] at h1
      rw [h1]
      trivial
    exact Kb.pow_mem hx 2
  · have := Subgroup.pow_index_mem Kb x
    rwa [h2] at this

theorem top_eq_sup_of_sq_mem {D₁ D₂ Kb : Subgroup D} [Kb.Normal]
    (hT : IsGoldschmidtTriple D₁ D₂) (hsq : ∀ x : D, x ^ 2 ∈ Kb) :
    (⊤ : Subgroup D) = Kb ⊔ (D₁ ⊓ D₂) ∧ twoResidual D₁ ≤ Kb ∧ twoResidual D₂ ≤ Kb := by
  obtain ⟨T, hTe⟩ := hT.sylow
  have hS : IsSylowTwoOf (D₁ ⊓ D₂) ⊤ := hTe ▸ isSylowTwoOf_top_of_sylow T
  have hKn : Subgroup.normalizer (Kb : Set D) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hle : ∀ {X : Subgroup D}, D₁ ⊓ D₂ ≤ X → X ≤ Kb ⊔ (D₁ ⊓ D₂) := fun {X} hX =>
    F7.isSylowTwoOf_le_sup_of_two_power (F7.isSylowTwoOf_mono_right hS hX le_top)
      (by rw [hKn]; exact le_top) fun x _ => ⟨1, by simpa using hsq x⟩
  have h1 := hle (X := D₁) inf_le_left
  have h2 := hle (X := D₂) inf_le_right
  have hres : ∀ X : Subgroup D, twoResidual X ≤ Kb := fun X => by
    refine (twoResidual_le_of_isTwoQuotient (N := Kb ⊓ X) (H := X) inf_le_right ?_ ?_).trans
      inf_le_left
    · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right,
        Subgroup.inf_subgroupOf_right]
      infer_instance
    · intro y hy
      exact ⟨1, by simpa using (⟨hsq y, X.pow_mem hy 2⟩ : y ^ 2 ∈ Kb ⊓ X)⟩
  refine ⟨?_, hres D₁, hres D₂⟩
  refine le_antisymm ?_ le_top
  intro g _
  have : g ∈ D₁ ⊔ D₂ := by rw [hT.gen]; trivial
  exact (sup_le h1 h2) this

theorem isQuasisimple_of_simple_nonab {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hnc : ∃ a b : Y, a * b ≠ b * a) : CFSG.IsQuasisimple Y := by
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hperf : Group.IsPerfect Y := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have : ⁅a, b⁆ ∈ commutator Y :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at this
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
    · exact h
  let e : Y ⧸ Subgroup.center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨hperf, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem exists_noncomm_of_simple {D₁ D₂ Kb : Subgroup D} [Kb.Normal]
    (hT : IsGoldschmidtTriple D₁ D₂) (hsq : ∀ x : D, x ^ 2 ∈ Kb) (hs : IsSimpleGroup ↥Kb) :
    ∃ a b : ↥Kb, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsMulCommutative ↥Kb := ⟨⟨fun a b => hc a b⟩⟩
  have hp : (Nat.card ↥Kb).Prime := Group.is_simple_iff_prime_card.mp hs
  have h3 : ∀ {X : Subgroup D}, Nonempty (↥X ⧸ Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3)) →
      ∃ g ∈ X, orderOf g = 3 ∧ g ∈ Kb := by
    intro X ⟨e⟩
    have hc6 : Nat.card (↥X ⧸ Open.pCore 2 ↥X) = 6 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hd : 3 ∣ Nat.card ↥X := by
      rw [(Open.pCore 2 ↥X).card_eq_card_quotient_mul_card_subgroup, hc6]
      exact Dvd.dvd.mul_right (by norm_num) _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
    refine ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx, ?_⟩
    have ho : (x : D) ^ 3 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx
      exact hx ▸ pow_orderOf_eq_one _
    have e1 : (x : D) = ((x : D) ^ 2)⁻¹ := by
      have : (x : D) ^ 2 * (x : D) = 1 := by rw [← pow_succ]; exact ho
      exact (inv_eq_of_mul_eq_one_right this).symm
    rw [e1]
    exact Kb.inv_mem (hsq x)
  obtain ⟨g₁, hg₁X, hg₁o, hg₁K⟩ := h3 (X := D₁) hT.quotient₁
  obtain ⟨g₂, hg₂X, hg₂o, hg₂K⟩ := h3 (X := D₂) hT.quotient₂
  have hr : Nat.card ↥Kb = 3 := by
    have hd : 3 ∣ Nat.card ↥Kb := by
      rw [← hg₁o]
      exact Subgroup.orderOf_dvd_natCard Kb hg₁K
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd).symm
  have hzK : ∀ g : D, orderOf g = 3 → g ∈ Kb → Subgroup.zpowers g = Kb := by
    intro g hg hgK
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgK) ?_
    rw [hr, Nat.card_zpowers, hg]
  have hK₁ : Kb ≤ D₁ := by
    rw [← hzK g₁ hg₁o hg₁K]
    exact (Subgroup.zpowers_le).mpr hg₁X
  have hg₂₁ : g₂ ∈ D₁ ⊓ D₂ := ⟨hK₁ hg₂K, hg₂X⟩
  have h2 := hT.isPGroup_inf ⟨g₂, hg₂₁⟩
  obtain ⟨k, hk⟩ := h2
  have hk' : g₂ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 3 ∣ 2 ^ k := by
    rw [← hg₂o]
    exact orderOf_dvd_of_pow_eq_one hk'
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem isComponent_of_simple {D₁ D₂ Kb : Subgroup D} [Kb.Normal]
    (hT : IsGoldschmidtTriple D₁ D₂) (hsq : ∀ x : D, x ^ 2 ∈ Kb) (hs : IsSimpleGroup ↥Kb) :
    CFSG.IsComponent Kb :=
  ⟨@isQuasisimple_of_simple_nonab _ _ hs (exists_noncomm_of_simple hT hsq hs),
    Subgroup.Normal.isSubnormal ‹_›⟩

theorem idx2Comp_of_data {D₁ D₂ : Subgroup D} (hT : IsGoldschmidtTriple D₁ D₂)
    (h : Idx2Data D) :
    ∃ Kb : Subgroup D, CFSG.IsComponent Kb ∧ Kb.Normal ∧ F618Core ↥Kb ∧
      (⊤ : Subgroup D) = Kb ⊔ (D₁ ⊓ D₂) ∧ twoResidual D₁ ≤ Kb ∧ twoResidual D₂ ≤ Kb := by
  obtain ⟨Kb, hKn, hcore, hsq, hq⟩ := h
  obtain ⟨hsup, h1, h2⟩ := top_eq_sup_of_sq_mem (Kb := Kb) hT hsq
  refine ⟨Kb, ⟨?_, Subgroup.Normal.isSubnormal hKn⟩, hKn, hcore, hsup, h1, h2⟩
  rcases hq with hs | hq
  · exact @isQuasisimple_of_simple_nonab _ _ hs (exists_noncomm_of_simple hT hsq hs)
  · exact hq

end Struct

end Gold14610

end CFSG.Quasithin

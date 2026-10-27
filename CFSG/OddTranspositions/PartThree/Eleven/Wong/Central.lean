module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.Hyp
public import CFSG.ClassicalInvolution.SL2Facts
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Open.Defs

public section

namespace CFSG.OddTranspositions.PartThree.Wong

variable {G : Type} [Group G] [Finite G] {t : G} {L₁ L₂ : Subgroup G}

namespace WongHyp

open CFSG.ClassicalInvolution

private instance instFactPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem odd_card_zmod_five : Odd (Nat.card (ZMod 5)) := by
  rw [Nat.card_zmod]; decide

private theorem four_le_card_zmod_five : 4 ≤ Nat.card (ZMod 5) := by
  rw [Nat.card_zmod]; norm_num

private theorem card_sl2_five : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
  rw [Matrix.card_SL_field 2, ZMod.card]
  norm_num

private theorem card_of_equiv_sl2 {P : Type*} [Group P]
    (e : P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) : Nat.card P = 120 := by
  rw [Nat.card_congr e.toEquiv, card_sl2_five]

private theorem center_eq_zpowers_of_equiv_sl2 {P : Type*} [Group P]
    (e : P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) {u : P} (hu : e u = -1) :
    Subgroup.center P = Subgroup.zpowers u := by
  apply le_antisymm
  · intro c hc
    rw [mem_center_iff_of_equiv_sl2 e] at hc
    rcases (mem_center_sl2_iff (e c)).mp hc with h1 | h1
    · have : c = 1 := by rw [← e.injective.eq_iff, h1, map_one]
      rw [this]; exact Subgroup.one_mem _
    · have : c = u := by rw [← e.injective.eq_iff, h1, hu]
      rw [this]; exact Subgroup.mem_zpowers u
  · rw [Subgroup.zpowers_le, mem_center_iff_of_equiv_sl2 e, hu]
    exact (mem_center_sl2_iff _).mpr (Or.inr rfl)

private theorem t_mem_left (h : WongHyp t L₁ L₂) : t ∈ L₁ := by
  have : t ∈ L₁ ⊓ L₂ := by rw [h.inf_eq]; exact Subgroup.mem_zpowers t
  exact this.1

private theorem t_mem_right (h : WongHyp t L₁ L₂) : t ∈ L₂ := by
  have : t ∈ L₁ ⊓ L₂ := by rw [h.inf_eq]; exact Subgroup.mem_zpowers t
  exact this.2

private theorem mem_zpowers_of_mem_center_left (h : WongHyp t L₁ L₂) {a : G} (ha : a ∈ L₁)
    (hc : ∀ y ∈ L₁, a * y = y * a) : a ∈ Subgroup.zpowers t := by
  obtain ⟨e⟩ := h.equiv₁
  have htL₁ := t_mem_left h
  have hu : e (⟨t, htL₁⟩ : L₁) = -1 := by
    have h1 : (⟨t, htL₁⟩ : L₁) = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 odd_card_zmod_five e (⟨t, htL₁⟩ : L₁)).mp
        (by rw [Subgroup.orderOf_mk]; exact h.orderOf_t)
    rw [h1, MulEquiv.apply_symm_apply]
  have hcenter : Subgroup.center L₁ = Subgroup.zpowers (⟨t, htL₁⟩ : L₁) :=
    center_eq_zpowers_of_equiv_sl2 e hu
  have hmem : (⟨a, ha⟩ : L₁) ∈ Subgroup.center L₁ := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [hcenter, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨n, ?_⟩
  simpa using congrArg (fun z : L₁ => (z : G)) hn

private theorem mem_zpowers_of_mem_center_right (h : WongHyp t L₁ L₂) {a : G} (ha : a ∈ L₂)
    (hc : ∀ y ∈ L₂, a * y = y * a) : a ∈ Subgroup.zpowers t := by
  obtain ⟨e⟩ := h.equiv₂
  have htL₂ := t_mem_right h
  have hu : e (⟨t, htL₂⟩ : L₂) = -1 := by
    have h1 : (⟨t, htL₂⟩ : L₂) = e.symm (-1) :=
      (orderOf_eq_two_iff_of_equiv_sl2 odd_card_zmod_five e (⟨t, htL₂⟩ : L₂)).mp
        (by rw [Subgroup.orderOf_mk]; exact h.orderOf_t)
    rw [h1, MulEquiv.apply_symm_apply]
  have hcenter : Subgroup.center L₂ = Subgroup.zpowers (⟨t, htL₂⟩ : L₂) :=
    center_eq_zpowers_of_equiv_sl2 e hu
  have hmem : (⟨a, ha⟩ : L₂) ∈ Subgroup.center L₂ := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  rw [hcenter, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨n, ?_⟩
  simpa using congrArg (fun z : L₂ => (z : G)) hn

private theorem le_normalizer_of_commute (h : WongHyp t L₁ L₂) :
    L₁ ≤ Subgroup.normalizer (L₂ : Set G) := by
  have hcent : L₁ ≤ Subgroup.centralizer (L₂ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (h.commute a ha b hb).symm
  exact hcent.trans (Subgroup.centralizer_le_normalizer (L₂ : Set G))

private theorem card_sup_mul_card_inf {G : Type*} [Group G] (H K : Subgroup G)
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  haveI : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  haveI : (K.subgroupOf (H ⊔ K)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have quotient_card := Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K h).toEquiv
  have first_card := (K.subgroupOf H).card_mul_index
  have product_card := (K.subgroupOf (H ⊔ K)).card_mul_index
  rw [Subgroup.index_eq_card] at first_card
  rw [Subgroup.index_eq_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toEquiv,
    ← quotient_card] at product_card
  rw [← product_card]
  have hinter : Nat.card (K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_left K H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc
    Nat.card K * Nat.card (H ⧸ K.subgroupOf H) * Nat.card ↥(H ⊓ K) =
        Nat.card K * (Nat.card ↥(H ⊓ K) * Nat.card (H ⧸ K.subgroupOf H)) := by ac_rfl
    _ = Nat.card K * Nat.card H := by rw [← hinter, first_card]
    _ = Nat.card H * Nat.card K := mul_comm _ _

theorem sup_le_centralizer (h : WongHyp t L₁ L₂) :
    L₁ ⊔ L₂ ≤ Subgroup.centralizer ({t} : Set G) := by
  have htL₁ := t_mem_left h
  have htL₂ := t_mem_right h
  refine sup_le ?_ ?_
  · intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h.commute a ha t htL₂
  · intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.commute t htL₁ b hb).symm

theorem card_sup (h : WongHyp t L₁ L₂) : Nat.card (L₁ ⊔ L₂ : Subgroup G) = 7200 := by
  have hcard := card_sup_mul_card_inf L₁ L₂ (le_normalizer_of_commute h)
  have hcard₁ : Nat.card L₁ = 120 := by
    obtain ⟨e⟩ := h.equiv₁
    exact card_of_equiv_sl2 e
  have hcard₂ : Nat.card L₂ = 120 := by
    obtain ⟨e⟩ := h.equiv₂
    exact card_of_equiv_sl2 e
  have hzt : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]; exact h.orderOf_t
  rw [hcard₁, hcard₂, h.inf_eq, hzt] at hcard
  omega

theorem card_centralizer (h : WongHyp t L₁ L₂) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = 14400 := by
  have hle := sup_le_centralizer h
  have hindex : ((L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G))).index = 2 := by
    simpa only [Subgroup.relIndex] using h.relIndex_eq
  have hcard := Subgroup.card_mul_index ((L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G)))
  rw [hindex] at hcard
  have hsub : Nat.card ((L₁ ⊔ L₂).subgroupOf (Subgroup.centralizer ({t} : Set G))) =
      Nat.card (L₁ ⊔ L₂ : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [hsub, card_sup h] at hcard
  omega

theorem commutator_sup (h : WongHyp t L₁ L₂) : ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ = L₁ ⊔ L₂ := by
  obtain ⟨e₁⟩ := h.equiv₁
  haveI : Group.IsPerfect L₁ := isPerfect_of_equiv_sl2 four_le_card_zmod_five e₁
  obtain ⟨e₂⟩ := h.equiv₂
  haveI : Group.IsPerfect L₂ := isPerfect_of_equiv_sl2 four_le_card_zmod_five e₂
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  have h1 : ⁅L₁, L₁⁆ = L₁ := Subgroup.commutator_eq_self
  have h2 : ⁅L₂, L₂⁆ = L₂ := Subgroup.commutator_eq_self
  calc L₁ ⊔ L₂ = ⁅L₁, L₁⁆ ⊔ ⁅L₂, L₂⁆ := by rw [h1, h2]
    _ ≤ ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ :=
      sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem sup_inf_centralizer (h : WongHyp t L₁ L₂) :
    (L₁ ⊔ L₂) ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) = Subgroup.zpowers t := by
  have htL₁ := t_mem_left h
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxK, hxcen⟩ := hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L₁ L₂
      (le_normalizer_of_commute h), Set.mem_mul] at hxK
    obtain ⟨a, ha, b, hb, rfl⟩ := hxK
    have ha_comm : ∀ y ∈ L₁, a * y = y * a := by
      intro y hy
      have hxy : (a * b) * y = y * (a * b) :=
        (Subgroup.mem_centralizer_iff.mp hxcen y ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hy)).symm
      have hby : b * y = y * b := (h.commute y hy b hb).symm
      have h : (a * y) * b = (y * a) * b := by
        rw [mul_assoc, ← hby, ← mul_assoc, hxy, ← mul_assoc]
      exact mul_right_cancel h
    have hb_comm : ∀ y ∈ L₂, b * y = y * b := by
      intro y hy
      have hxy : (a * b) * y = y * (a * b) :=
        (Subgroup.mem_centralizer_iff.mp hxcen y ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hy)).symm
      have hay : a * y = y * a := (h.commute a ha y hy).eq
      have h : a * (b * y) = a * (y * b) := by
        calc a * (b * y) = (a * b) * y := (mul_assoc a b y).symm
          _ = y * (a * b) := hxy
          _ = (y * a) * b := (mul_assoc y a b).symm
          _ = (a * y) * b := by rw [← hay]
          _ = a * (y * b) := mul_assoc a y b
      exact mul_left_cancel h
    exact Subgroup.mul_mem _ (mem_zpowers_of_mem_center_left h ha ha_comm)
      (mem_zpowers_of_mem_center_right h hb hb_comm)
  · rw [Subgroup.zpowers_le]
    refine ⟨(le_sup_left : L₁ ≤ L₁ ⊔ L₂) htL₁, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (sup_le_centralizer h hy)

theorem commutator_centralizer (h : WongHyp t L₁ L₂) :
    ⁅Subgroup.centralizer ({t} : Set G), Subgroup.centralizer ({t} : Set G)⁆ = L₁ ⊔ L₂ := by
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let K : Subgroup G := L₁ ⊔ L₂
  change ⁅C, C⁆ = K
  have hKC : K ≤ C := sup_le_centralizer h
  let N : Subgroup C := K.subgroupOf C
  have hindex : N.index = 2 := by
    simpa only [N, Subgroup.relIndex] using h.relIndex_eq
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hindex
  have hcomm : _root_.commutator C ≤ N := by
    have hquot : Nat.card (C ⧸ N) = 2 := by
      rw [← Subgroup.index_eq_card, hindex]
    haveI : IsCyclic (C ⧸ N) := isCyclic_of_prime_card hquot
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.map_subtype_commutator C]
    rw [← Subgroup.map_subgroupOf_eq_of_le hKC]
    exact Subgroup.map_mono hcomm
  · have hK : ⁅K, K⁆ = K := commutator_sup h
    rw [← hK]
    exact Subgroup.commutator_mono hKC hKC

end WongHyp

end CFSG.OddTranspositions.PartThree.Wong

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Single

public section

namespace CFSG.QuasithinUnique.C56W

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

structure WSet1 {G : Type} [Group G] [Finite G] (H S L : Subgroup G) : Prop where
  charTwo : CharTwo H
  block : IsChi0Block H L
  thompson : ⁅L, thompsonJ S⁆ = L
  eq_join : H = L ⊔ S
  normalizes : S ≤ normalizer (L : Set G)
  minParabolic : IsMinimalParabolic S H

omit [Finite G] in
theorem exists_mem_diff_of_relIndex_two {S M₀ : Subgroup G} (h2 : S.relIndex M₀ = 2) :
    ∃ x ∈ M₀, x ∉ S := by
  by_contra hcon
  push Not at hcon
  have h1 : S.relIndex M₀ = 1 := Subgroup.relIndex_eq_one.mpr hcon
  omega

namespace WSet1

variable (hcs : WSet1 H S L)
include hcs

theorem sylow : IsSylowTwoOf S H := hcs.minParabolic.1

theorem isShort : IsShort2 L := hcs.block.1.1

theorem le_H : L ≤ H := hcs.block.1.2.1

theorem isPGroup_S : IsPGroup 2 S := hcs.sylow.isPGroup

theorem pCoreOf_le_S : pCoreOf 2 H ≤ S := hcs.sylow.pCoreOf_le

theorem conjJoin_eq : conjJoin S L = L := C56.conjJoin_eq_of_le_normalizer hcs.normalizes

theorem H_le_normalizer : H ≤ normalizer (L : Set G) := by
  rw [hcs.eq_join]
  exact sup_le Subgroup.le_normalizer hcs.normalizes

theorem H_pow_mem : ∀ g ∈ H, ∃ k : ℕ, g ^ 2 ^ k ∈ L := fun _ hg =>
  C1.exists_pow_mem_of_mem_sup hcs.isPGroup_S hcs.normalizes (hcs.eq_join ▸ hg)

theorem inf_centralizer_eq : H ⊓ centralizer (blockU L : Set G) = pCoreOf 2 H :=
  C1.inf_centralizer_blockU_eq hcs.isShort hcs.le_H hcs.H_le_normalizer hcs.H_pow_mem

theorem blockQ_le_pCoreOf : blockQ L ≤ pCoreOf 2 H :=
  C1.le_pCoreOf_of_normalized ((C1.blockQ_le L).trans hcs.le_H)
    (fun _ hg => C1.mem_normalizer_blockQ (hcs.H_le_normalizer hg)) (C1.blockQ_isPGroup L)

theorem blockU_le_pCoreOf : blockU L ≤ pCoreOf 2 H :=
  (C1.blockU_le_blockQ hcs.isShort).trans hcs.blockQ_le_pCoreOf

theorem S_le_normalizer_blockU : S ≤ normalizer (blockU L : Set G) :=
  fun _ hg => C1.mem_normalizer_blockU (hcs.normalizes hg)

theorem bb1 : ∀ p ∈ pCoreOf 2 H, ∀ l ∈ L, p * l * p⁻¹ * l⁻¹ ∈ blockU L := by
  intro p hp l hl
  exact C1.commutator_mem_blockU_of_mem_blockQ hcs.isShort
    (fun l hl => C1.commutator_mem_blockQ_of_mem_pCoreOf hcs.le_H hcs.H_le_normalizer hp hl) l hl

theorem c55 {M₀ : Subgroup G} (hC52 : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀) :
    ∃ y ∈ M₀, ¬ conjR (blockU L) y ≤ pCoreOf 2 H := by
  by_contra hcon
  push Not at hcon
  have hL := hcs.isShort
  set U := blockU L with hU
  set P := pCoreOf 2 H with hP
  set X : Subgroup G := ⨆ y : M₀, conjR U (y : G) with hX
  have hXP : X ≤ P := iSup_le fun y => hcon y y.2
  have hUX : U ≤ X := by
    have h1 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) ≤ X :=
      le_iSup (fun y : M₀ => conjR U (y : G)) ⟨1, one_mem _⟩
    have h2 : conjR U ((⟨1, one_mem _⟩ : M₀) : G) = U := conjSubgroup_one U
    rwa [h2] at h1
  have hXne : X ≠ ⊥ := fun h => C56.blockU_ne_bot hL (le_bot_iff.mp (h ▸ hUX))
  have hXS : X ≤ S := hXP.trans hcs.pCoreOf_le_S
  have hM₀X : M₀ ≤ normalizer (X : Set G) := by
    intro m hm
    rw [← conjSubgroup_eq_iff_mem_normalizer]
    have hle : conjSubgroup X m ≤ X := by
      have : conjSubgroup X m = ⨆ y : M₀, conjSubgroup (conjR U (y : G)) m := by
        simp only [conjSubgroup, hX]
        exact Subgroup.map_iSup _ _
      rw [this]
      refine iSup_le fun y => ?_
      have : conjSubgroup (conjR U (y : G)) m = conjR U ((y : G) * m) :=
        conjSubgroup_conjSubgroup U (y : G) m
      rw [this]
      exact le_iSup (fun y : M₀ => conjR U (y : G)) ⟨(y : G) * m, mul_mem y.2 hm⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [C5.card_conjSubgroup])
  have key : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X := by
    intro l hl x hx
    refine Subgroup.iSup_induction (fun y : M₀ => conjR U (y : G))
      (C := fun x => l * x * l⁻¹ ∈ X) hx ?_ ?_ ?_
    · intro y x hxy
      have hxP : x ∈ P := hcon y y.2 hxy
      have hc : l * x * l⁻¹ * x⁻¹ ∈ U := by
        have h1 := hcs.bb1 x hxP l hl
        have e : l * x * l⁻¹ * x⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem h1
      have hxX : x ∈ X := le_iSup (fun y : M₀ => conjR U (y : G)) y hxy
      have e : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact mul_mem (hUX hc) hxX
    · simp
    · intro a b ha hb
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
  have hLX : L ≤ normalizer (X : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key l hl x hx
    · intro h
      have := key l⁻¹ (inv_mem hl) _ h
      simpa [mul_assoc] using this
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hcs.eq_join]
    exact sup_le hLX (hSM.trans hM₀X)
  exact hC52 X hXS hXne hHX hM₀X

theorem not_conj_le_of_mem_diff {M₀ : Subgroup G} (hC52 : C5.NoCommonNormal S H M₀) (hSM : S ≤ M₀)
    (h2 : S.relIndex M₀ = 2) {x : G} (hx : x ∈ M₀) (hxS : x ∉ S) :
    ¬ conjR (blockU L) x ≤ pCoreOf 2 H := by
  obtain ⟨y, hy, hyU⟩ := hcs.c55 hC52 hSM
  have hyS : y ∉ S := by
    intro hyS
    apply hyU
    have hUP := hcs.blockU_le_pCoreOf
    have hPn : y ∈ normalizer (pCoreOf 2 H : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hcs.sylow.le hyS)
    have := C5.conjSubgroup_mono hUP y
    rwa [C5.conjSubgroup_eq_self hPn] at this
  have hs : y⁻¹ * x ∈ S := inv_mul_mem_of_relIndex_two h2 hy hyS hx hxS
  intro hxP
  apply hyU
  have hPn : (y⁻¹ * x)⁻¹ ∈ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
      (hcs.sylow.le (inv_mem hs))
  have h1 := C5.conjSubgroup_mono hxP (y⁻¹ * x)⁻¹
  rw [C56.conjR_eq, conjSubgroup_conjSubgroup, C5.conjSubgroup_eq_self hPn] at h1
  have e : x * (y⁻¹ * x)⁻¹ = y := by group
  rw [e] at h1
  exact h1

end WSet1

end CFSG.QuasithinUnique.C56W

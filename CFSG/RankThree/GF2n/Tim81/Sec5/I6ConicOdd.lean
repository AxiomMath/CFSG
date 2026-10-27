module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape
import CFSG.RankThree.GF2n.Tim81.Sec5.I6Conic
import CFSG.RankThree.GF2n.Tim81.Sec5.I6ConicScalar
import CFSG.GroupTheory.ConjFixedParity

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G} {h₀ : G}

namespace Sec45Shape

private theorem eq_xOf_of_not_le (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {𝒮 : Set (Subgroup G)} (hsub : 𝒮 ⊆ Tim79a.omegaOf V H) (hV : V ∈ 𝒮)
    {C₂ C₃ C₄ : Subgroup G} (hC₂ : C₂ ∈ 𝒮) (hC₃ : C₃ ∈ 𝒮) (hC₄ : C₄ ∈ 𝒮)
    (hV₂ : C₂ ≠ V) (hV₃ : C₃ ≠ V) (h₂₃ : C₂ ≠ C₃)
    (hC₄X : ¬ C₄ ≤ V ⊔ C₂ ⊔ C₃)
    (hcardW : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4) :
    (⨆ A ∈ 𝒮, A) = Tim79a.xOf V H := by
  have hXeq : (⨆ A ∈ ({V, C₂, C₃} : Set (Subgroup G)), A) = V ⊔ C₂ ⊔ C₃ := by
    rw [show ({V, C₂, C₃} : Set (Subgroup G)) = insert V (insert C₂ {C₃}) from rfl,
      iSup_insert, iSup_insert, iSup_singleton]
    show V ⊔ (C₂ ⊔ C₃) = V ⊔ C₂ ⊔ C₃
    ac_rfl
  have hC₄pts : C₄ ∈ Tim79a.omegaOf V H := hsub hC₄
  have hXW : V ⊔ C₂ ⊔ C₃ ≤ Tim79a.xOf V H :=
    sup_le (sup_le (le_xOf_self V H) (Tim79a.le_xOf (hsub hC₂)))
      (Tim79a.le_xOf (hsub hC₃))
  have hC₄W : C₄ ≤ Tim79a.xOf V H := Tim79a.le_xOf hC₄pts
  have hinf : C₄ ⊓ (V ⊔ C₂ ⊔ C₃) = ⊥ := by
    by_contra hne
    have hne' : C₄ ⊓ (⨆ A ∈ ({V, C₂, C₃} : Set (Subgroup G)), A) ≠ ⊥ := by
      rwa [hXeq]
    have hle := Sec45Shape.le_of_inf_ne_bot h hS ?_ hC₄pts hne'
    · have hle' : C₄ ≤ V ⊔ C₂ ⊔ C₃ := by rwa [hXeq] at hle
      exact hC₄X hle'
    · intro A hA
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
      rcases hA with hA | hA | hA
      · rw [hA]
        exact hsub hV
      · rw [hA]
        exact hsub hC₂
      · rw [hA]
        exact hsub hC₃
  have hcardX : Nat.card ↥(V ⊔ C₂ ⊔ C₃) = Nat.card V ^ 3 :=
    card_sup_three h hS (hsub hC₂) (hsub hC₃) hV₂ hV₃ h₂₃
  have hcardC₄ : Nat.card C₄ = Nat.card V := by
    obtain ⟨y, -, rfl⟩ := hC₄pts
    exact card_conjSubgroup y V
  have hcomm : ∀ x ∈ (V ⊔ C₂ ⊔ C₃ : Subgroup G), ∀ y ∈ C₄, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((hS.isElemAbelian h).1.is_comm.comm
      ⟨x, hXW hx⟩ ⟨y, hC₄W hy⟩)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (V ⊔ C₂ ⊔ C₃) C₄ hcomm).1
  rw [show (V ⊔ C₂ ⊔ C₃) ⊓ C₄ = ⊥ by rw [inf_comm, hinf], Subgroup.card_bot,
    mul_one] at hprod
  have hcardSup : Nat.card ↥((V ⊔ C₂ ⊔ C₃) ⊔ C₄) = Nat.card V ^ 4 := by
    rw [hprod, hcardX, hcardC₄, ← pow_succ]
  have hsupW : (V ⊔ C₂ ⊔ C₃) ⊔ C₄ = Tim79a.xOf V H :=
    Subgroup.eq_of_le_of_card_ge (sup_le hXW hC₄W) (by rw [hcardSup, hcardW])
  have hXY : V ⊔ C₂ ⊔ C₃ ≤ ⨆ A ∈ 𝒮, A :=
    sup_le (sup_le (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) V hV)
      (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) C₂ hC₂))
      (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) C₃ hC₃)
  have hC₄Y : C₄ ≤ ⨆ A ∈ 𝒮, A := le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) C₄ hC₄
  refine le_antisymm (iSup₂_le fun A hA => Tim79a.le_xOf (hsub hA)) ?_
  rw [← hsupW]
  exact sup_le hXY hC₄Y

private theorem conj_sup_eq_of_swap (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {𝒮 : Set (Subgroup G)} (hsub : 𝒮 ⊆ Tim79a.omegaOf V H) (hV : V ∈ 𝒮)
    {C₂ C₃ : Subgroup G} (hC₂ : C₂ ∈ 𝒮) (hC₃ : C₃ ∈ 𝒮)
    (hV₂ : C₂ ≠ V) (hV₃ : C₃ ≠ V) (h₂₃ : C₂ ≠ C₃)
    {p : G} (hpP : p ∈ Pc M V) (hp₂ : conjSubgroup p C₂ = C₃)
    (hp₃ : conjSubgroup p C₃ = C₂)
    (hcardW : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4)
    {Y : Subgroup G} (hY : Y = ⨆ A ∈ 𝒮, A) :
    conjSubgroup p Y = Y := by
  by_cases hsmall : ∀ C ∈ 𝒮, C ≤ V ⊔ C₂ ⊔ C₃
  · have hYX : Y ≤ V ⊔ C₂ ⊔ C₃ := by
      rw [hY]
      exact iSup₂_le hsmall
    have hXY : V ⊔ C₂ ⊔ C₃ ≤ Y := by
      rw [hY]
      exact sup_le (sup_le (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) V hV)
        (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) C₂ hC₂))
        (le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) C₃ hC₃)
    have hYeq : Y = V ⊔ C₂ ⊔ C₃ := le_antisymm hYX hXY
    rw [hYeq]
    have hpV : conjSubgroup p V = V :=
      mem_normalizer_iff_conjSubgroup_eq.mp
        (h.toHyp.le_normalizer (h.toHyp.Pc_le_M hpP))
    rw [conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup, hpV, hp₂, hp₃]
    ac_rfl
  · push Not at hsmall
    obtain ⟨C₄, hC₄, hC₄X⟩ := hsmall
    rw [hY, eq_xOf_of_not_le h hS hsub hV hC₂ hC₃ hC₄ hV₂ hV₃ h₂₃ hC₄X hcardW]
    exact mem_normalizer_iff_conjSubgroup_eq.mp
      (Tim79a.H_le_normalizer_xOf V H (hS.Pc_le hpP))

private theorem maps_conj_mem (hS : Sec45Shape M V H h₀)
    {𝒮 : Set (Subgroup G)} (hsub : 𝒮 ⊆ Tim79a.omegaOf V H)
    (hcl : ∀ C ∈ Tim79a.omegaOf V H, C ≤ (⨆ A ∈ 𝒮, A) → C ∈ 𝒮)
    {p : G} (hpP : p ∈ Pc M V) {Y : Subgroup G} (hY : Y = ⨆ A ∈ 𝒮, A)
    (hpN : p ∈ Subgroup.normalizer (Y : Set G)) :
    ∀ x ∈ Subgroup.zpowers p, ∀ C ∈ 𝒮, C.map (MulAut.conj x).toMonoidHom ∈ 𝒮 := by
  intro x hx C hC
  have hxH : x ∈ H := hS.Pc_le (Subgroup.zpowers_le.mpr hpP hx)
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) := Subgroup.zpowers_le.mpr hpN hx
  have hxY : conjSubgroup x Y = Y := mem_normalizer_iff_conjSubgroup_eq.mp hxN
  have hCpts : C ∈ Tim79a.omegaOf V H := hsub hC
  have hCY : C ≤ Y := by
    rw [hY]
    exact le_iSup₂ (f := fun A (_ : A ∈ 𝒮) => A) C hC
  have hle : conjSubgroup x C ≤ Y := by
    rw [← hxY]
    exact Subgroup.map_mono hCY
  have hle' : conjSubgroup x C ≤ ⨆ A ∈ 𝒮, A := by rwa [hY] at hle
  have hmem : conjSubgroup x C ∈ 𝒮 :=
    hcl (conjSubgroup x C) (Tim79a.conjSubgroup_mem_omegaOf_of_mem hCpts hxH) hle'
  simpa [conjSubgroup] using hmem

private theorem fixed_eq_singleton (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {𝒮 : Set (Subgroup G)} (hsub : 𝒮 ⊆ Tim79a.omegaOf V H) (hV : V ∈ 𝒮)
    {C₂ C₃ : Subgroup G} (hC₂ : C₂ ∈ 𝒮) (h₂₃ : C₂ ≠ C₃)
    {p : G} (hpP : p ∈ Pc M V) (hp₂ : conjSubgroup p C₂ = C₃) :
    {C ∈ 𝒮 | ∀ x ∈ Subgroup.zpowers p, C.map (MulAut.conj x).toMonoidHom = C} = {V} := by
  ext C
  constructor
  · rintro ⟨hC, hfix⟩
    have hpC : conjSubgroup p C = C := by
      have h := hfix p (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
      simpa [conjSubgroup] using h
    have hp₂ne : conjSubgroup p C₂ ≠ C₂ := by
      rw [hp₂]
      exact h₂₃.symm
    exact eq_V_of_conj_eq h hS hpP (hsub hC₂) hp₂ne (hsub hC) hpC
  · intro hC
    rw [Set.mem_singleton_iff] at hC
    rw [hC]
    refine ⟨hV, ?_⟩
    intro x hx
    have hxM : x ∈ M := h.toHyp.Pc_le_M (Subgroup.zpowers_le.mpr hpP hx)
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
      rw [h.toHyp.normalizer_eq]
      exact hxM
    have hxV : conjSubgroup x V = V := mem_normalizer_iff_conjSubgroup_eq.mp hxN
    simpa [conjSubgroup] using hxV

theorem odd_ncard_of_closed (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {𝒮 : Set (Subgroup G)} (hsub : 𝒮 ⊆ Tim79a.omegaOf V H) (hV : V ∈ 𝒮)
    (h3 : 3 ≤ 𝒮.ncard)
    (hcl : ∀ C ∈ Tim79a.omegaOf V H, C ≤ (⨆ A ∈ 𝒮, A) → C ∈ 𝒮) : Odd 𝒮.ncard := by
  classical
  have h2 : 2 ≤ (𝒮 \ {V}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hV]
    have h3' : 2 < 𝒮.ncard := lt_of_lt_of_le (by norm_num) h3
    omega
  obtain ⟨t, ht_sub, ht_card⟩ := Set.exists_subset_card_eq h2
  obtain ⟨C₂, C₃, h₂₃, rfl⟩ := Set.ncard_eq_two.mp ht_card
  obtain ⟨hC₂, hC₂V⟩ := ht_sub (by simp : C₂ ∈ ({C₂, C₃} : Set (Subgroup G)))
  obtain ⟨hC₃, hC₃V⟩ := ht_sub (by simp : C₃ ∈ ({C₂, C₃} : Set (Subgroup G)))
  have hV₂ : C₂ ≠ V := by simpa using hC₂V
  have hV₃ : C₃ ≠ V := by simpa using hC₃V
  obtain ⟨p, hpP, hp₂, hp₃⟩ :=
    exists_swap h hS (hsub hC₂) (hsub hC₃) hV₂ hV₃
  obtain ⟨F, hField, hFintype, hCharP, l, hl, ψ, hw⟩ := hS.shape
  letI := hField
  letI := hFintype
  letI := hCharP
  have hcardW : Nat.card (Tim79a.xOf V H) = Nat.card V ^ 4 := by
    rw [hw.card_W, hw.card_V, ← pow_mul]
    congr 1
    ring
  let Y : Subgroup G := ⨆ A ∈ 𝒮, A
  have hY : Y = ⨆ A ∈ 𝒮, A := rfl
  have hpY : conjSubgroup p Y = Y :=
    conj_sup_eq_of_swap h hS hsub hV hC₂ hC₃ hV₂ hV₃ h₂₃ hpP hp₂ hp₃ hcardW hY
  have hpN : p ∈ Subgroup.normalizer (Y : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr hpY
  have hT : IsPGroup 2 (Subgroup.zpowers p) :=
    (inSubgroup_pCore_two M).1.to_le
      ((Subgroup.zpowers_le.mpr hpP).trans
        (show Pc M V ≤ inSubgroup (pCore 2) M from inf_le_left))
  have hpar := CFSG.GroupTheory.ncard_modEq_ncard_fixed hT
    (maps_conj_mem hS hsub hcl hpP hY hpN)
  rw [fixed_eq_singleton h hS hsub hV hC₂ h₂₃ hpP hp₂, Set.ncard_singleton] at hpar
  exact Nat.odd_iff.mpr (by simpa [Nat.ModEq] using hpar)

end Sec45Shape

end CFSG.RankThree.GF2n.Tim81

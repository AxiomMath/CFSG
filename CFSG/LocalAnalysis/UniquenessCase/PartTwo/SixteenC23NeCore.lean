module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem c23ne_binaryNatural (M : Subgroup G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hne : V₀ ≠ ⊥)
    (h : BinaryNaturalSL (lStar M V₀ V hV L) (wStar M V₀ V hV L) ⊥ 3 1) :
    BinaryNaturalSL (barSub V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 1 := by
  have hW : ∀ V₁ : Subgroup G, V₁ = V₀ → BinaryNaturalSL (barSub V₁ V hV L)
      (imgTil V₁ V hV (wSub V₀ V hV L)) ⊥ 3 1 →
      BinaryNaturalSL (barSub V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 1 := by
    intro V₁ hV₁ h
    rw [hV₁] at h
    rwa [show imgTil V₀ V hV (wSub V₀ V hV L) = wTil V₀ V hV L from imgTil_preTil V₀ V hV _] at h
  exact hW _ (v1Sub_of_ne_bot M V₀ V hV L hne) h

theorem c23ne_wTil_inf_conj_eq_bot {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V)
    (hnat : BinaryNaturalSL (barSub V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 1) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    wTil V₀ V hV L ⊓ wTil V₀ V hV (conjSubgroup L x) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨hu1, hu2⟩ := hu
  by_contra hne
  have hfix : ∀ a ∈ barSub V₀ V hV L, (a : MulAut (Vtil V₀ V hV)) u = u :=
    fun a ha => c23_fix_wTil_conj h hV hx hxn a ha u hu2
  have htr := c23_binaryNatural_transitive hnat
  have hy_eq : ∀ y ∈ wTil V₀ V hV L, y = 1 ∨ y = u := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · refine Or.inr ?_
      obtain ⟨φ, hφ, hφu⟩ := htr u hu1 hne y hy hy1
      rw [← hφu, hfix φ hφ]
  have hsub : (wTil V₀ V hV L : Set (Vtil V₀ V hV)) ⊆ {1, u} := by
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hy_eq y hy
  have hle2 : Nat.card ↥(wTil V₀ V hV L) ≤ 2 := by
    calc Nat.card ↥(wTil V₀ V hV L)
        = (wTil V₀ V hV L : Set (Vtil V₀ V hV)).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, u} : Set (Vtil V₀ V hV)).ncard :=
          Set.ncard_le_ncard hsub ((Set.finite_singleton u).insert 1)
      _ = 2 := Set.ncard_pair (Ne.symm hne)
  have h8 := s15_T7_card_eight hnat
  omega

theorem c23ne_core_of_case2 {D : Data G} (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2)
    (hL3 : IsL3 ↥(barSub V₀ V hV L) 1)
    (hnat : BinaryNaturalSL (barSub V₀ V hV L) (wTil V₀ V hV L) ⊥ 3 1) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    C23Core (wTil V₀ V hV L) (wTil V₀ V hV (conjSubgroup L x)) (barSub V₀ V hV L)
      (barSub V₀ V hV (conjSubgroup L x)) (Mbar D.M V₀ V hV) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hxs : x ∈ stabTil V₀ V := hMs hx
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    intro h0
    have := card_eq_of_isL3 hL3
    rw [h0, Subgroup.card_bot] at this
    omega
  have h8 := s15_T7_card_eight hnat
  have htr := c23_binaryNatural_transitive hnat
  exact ⟨h8, (c23_card_wTil_conj hV hxs L).trans h8,
    c23ne_wTil_inf_conj_eq_bot h hV hnat hx hxn, c23_wTil_sup_conj_eq_top h1217 h hV hs hL hx hxn,
    card_eq_of_isL3 hL3, (c23_card_barSub_conjSubgroup hV hxs L).trans (card_eq_of_isL3 hL3),
    c23_fix_wTil_conj h hV hx hxn, c23_fix_wTil_of_nBar h hV hx hxn, htr,
    c23_exists_trans_conj hV hxs htr, barSub_mono V₀ V hV h.le,
    c23_barSub_conjSubgroup_le_Mbar D h hV hx, c23_perm_wTil h hV hs hL hx hxn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

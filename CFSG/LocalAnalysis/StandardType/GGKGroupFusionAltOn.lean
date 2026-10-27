module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltThree

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section AltOn

variable {V : Type} [DecidableEq V] [Fintype V]

@[expose] noncomputable def GGAltOn (X : Finset V) : Subgroup (Perm V) :=
  (alternatingGroup ↥X).map (Perm.ofSubtype : Perm ↥X →* Perm V)

theorem ggMem_altOn_iff {X : Finset V} {σ : Perm V} :
    σ ∈ GGAltOn X ↔ σ ∈ alternatingGroup V ∧ ∀ v, σ v ≠ v → v ∈ X := by
  unfold GGAltOn
  rw [alternatingGroup.map_ofSubtype, Subgroup.mem_inf, Perm.mem_range_ofSubtype_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun v hv => h1 (Perm.mem_support.mpr hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun v hv => h2 v (Perm.mem_support.mp hv), h1⟩

theorem ggSwap_mul_swap_mem_altOn {X : Finset V} {a b c : V} (ha : a ∈ X) (hb : b ∈ X)
    (hc : c ∈ X) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    swap a b * swap b c ∈ GGAltOn X := by
  rw [ggMem_altOn_iff]
  have hnd : [a, b, c].Nodup := by simp [hab, hbc, hac]
  have h3 : (swap a b * swap b c).IsThreeCycle := by
    rw [← card_support_eq_three_iff, Equiv.Perm.support_swap_mul_swap hnd]
    simp [hab, hbc, hac]
  refine ⟨h3.mem_alternatingGroup, fun v hv => ?_⟩
  have hv' : v ∈ (swap a b * swap b c).support := Perm.mem_support.mpr hv
  rw [Equiv.Perm.support_swap_mul_swap hnd] at hv'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
  rcases hv' with rfl | rfl | rfl <;> assumption

theorem ggAltIn_of_altOn_le {N : Subgroup (Perm V)} {X : Finset V} (h : GGAltOn X ≤ N) :
    GGAltIn N X :=
  fun _ ha _ hb _ hc hab hbc hac => h (ggSwap_mul_swap_mem_altOn ha hb hc hab hbc hac)

omit [Fintype V] in
theorem ggAltOn_le_of_altIn {N : Subgroup (Perm V)} {X : Finset V} (h : GGAltIn N X) :
    GGAltOn X ≤ N := by
  unfold GGAltOn
  rw [Subgroup.map_le_iff_le_comap, ← Equiv.Perm.closure_three_cycles_eq_alternating,
    Subgroup.closure_le]
  intro σ hσ
  have hσ3 : σ.IsThreeCycle := hσ
  obtain ⟨c, hc⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ3.card_support]
    norm_num
  have h1 := (hσ3.eq_swap_mul_swap_iff_mem_support (a := c)).mpr hc
  obtain ⟨hc1, hc2⟩ := List.nodup_cons.mp (hσ3.nodup_iff_mem_support.mpr hc)
  obtain ⟨hc3, -⟩ := List.nodup_cons.mp hc2
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hc1 hc3
  have hne1 : (c : V) ≠ (σ c : V) := fun h => hc1.1 (Subtype.ext h)
  have hne2 : (σ c : V) ≠ (σ (σ c) : V) := fun h => hc3 (Subtype.ext h)
  have hne3 : (c : V) ≠ (σ (σ c) : V) := fun h => hc1.2 (Subtype.ext h)
  have h3 := h c.2 (σ c).2 (σ (σ c)).2 hne1 hne2 hne3
  unfold GGContains3 at h3
  have e : (Perm.ofSubtype : Perm ↥X →* Perm V) σ =
      swap (c : V) (σ c : V) * swap (σ c : V) (σ (σ c) : V) := by
    conv_lhs => rw [h1]
    rw [map_mul, Perm.ofSubtype_swap_eq, Perm.ofSubtype_swap_eq]
  rw [SetLike.mem_coe, Subgroup.mem_comap, e]
  exact h3

noncomputable def ggAltOnMulEquiv (X : Finset V) :
    ↥(GGAltOn X) ≃* ↥(alternatingGroup (Fin X.card)) :=
  (Subgroup.equivMapOfInjective (alternatingGroup ↥X) (Perm.ofSubtype : Perm ↥X →* Perm V)
    Perm.ofSubtype_injective).symm.trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq (Fintype.card_coe X)))

omit [Fintype V] in
theorem ggAltOn_isSimpleGroup {X : Finset V} (hX : 5 ≤ X.card) : IsSimpleGroup ↥(GGAltOn X) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin X.card)) :=
    alternatingGroup.isSimpleGroup (by simpa using hX)
  exact (MulEquiv.isSimpleGroup_congr (ggAltOnMulEquiv X)).mpr this

theorem ggConj_mem_altOn {X : Finset V} {σ : Perm V} (hσ : σ ∈ GGAltOn X) (g : Perm V) :
    g * σ * g⁻¹ ∈ GGAltOn (X.image g) := by
  rw [ggMem_altOn_iff] at hσ ⊢
  refine ⟨?_, fun v hv => ?_⟩
  · rw [mem_alternatingGroup, map_mul, map_mul, map_inv, mem_alternatingGroup.mp hσ.1, mul_one,
      mul_inv_cancel]
  rw [Finset.mem_image]
  refine ⟨g⁻¹ v, hσ.2 _ fun h => hv ?_, by simp⟩
  simp only [Perm.coe_mul, Function.comp_apply, h]
  simp

theorem ggAltOn_commute_of_disjoint {X Y : Finset V} (hXY : Disjoint X Y) {σ τ : Perm V}
    (hσ : σ ∈ GGAltOn X) (hτ : τ ∈ GGAltOn Y) : σ * τ = τ * σ := by
  rw [ggMem_altOn_iff] at hσ hτ
  have hd : Perm.Disjoint σ τ := by
    intro v
    by_cases hv : σ v = v
    · exact Or.inl hv
    · right
      by_contra hv'
      exact Finset.disjoint_left.mp hXY (hσ.2 v hv) (hτ.2 v hv')
  exact hd.commute.eq

omit [Fintype V] in
theorem ggSwap_mul_swap_apply_of_ne {x y z w : V} (hx : w ≠ x) (hy : w ≠ y) (hz : w ≠ z) :
    (swap x y * swap y z) w = w := by
  rw [Perm.coe_mul, Function.comp_apply, swap_apply_of_ne_of_ne hy hz,
    swap_apply_of_ne_of_ne hx hy]

omit [Fintype V] in
theorem ggMem_three_of_commute {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    {g : Perm V} (hg : g * (swap x y * swap y z) = (swap x y * swap y z) * g) :
    g x = x ∨ g x = y ∨ g x = z := by
  by_contra h
  push Not at h
  have h1 := congrArg (fun f : Perm V => f x) hg
  simp only [Perm.coe_mul, Function.comp_apply] at h1
  have e2 : swap x y (swap y z x) = y := by
    rw [swap_apply_of_ne_of_ne hxy hxz, swap_apply_left]
  have e1 : swap x y (swap y z (g x)) = g x := by
    rw [swap_apply_of_ne_of_ne h.2.1 h.2.2, swap_apply_of_ne_of_ne h.1 h.2.1]
  rw [e2, e1] at h1
  exact hxy (g.injective h1).symm

theorem ggFix_of_commute_altOn {X : Finset V} (hX : 5 ≤ X.card) {g : Perm V}
    (hg : ∀ σ ∈ GGAltOn X, g * σ = σ * g) : ∀ v ∈ X, g v = v := by
  intro v hv
  obtain ⟨a, ha, hav⟩ : ∃ a ∈ X, a ≠ v := Finset.exists_mem_ne (by omega) v
  obtain ⟨b, hb, hbv, hba⟩ := ggExists_mem_ne_ne (X := X) (by omega) v a
  obtain ⟨c, hc, hcvab⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {v, a, b}) (t := X) (lt_of_le_of_lt Finset.card_le_three (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcvab
  obtain ⟨d, hd, hdvabc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {v, a, b, c}) (t := X) (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdvabc
  have h1 := ggMem_three_of_commute (Ne.symm hav) (Ne.symm hbv)
    (hg _ (ggSwap_mul_swap_mem_altOn hv ha hb (Ne.symm hav) (Ne.symm hba) (Ne.symm hbv)))
  have h2 := ggMem_three_of_commute (Ne.symm hcvab.1) (Ne.symm hdvabc.1)
    (hg _ (ggSwap_mul_swap_mem_altOn hv hc hd (Ne.symm hcvab.1) (Ne.symm hdvabc.2.2.2)
      (Ne.symm hdvabc.1)))
  rcases h1 with h1 | h1 | h1
  · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hcvab.2.1)
    · exact absurd (h1.symm.trans h2) (Ne.symm hdvabc.2.1)
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) (Ne.symm hcvab.2.2)
    · exact absurd (h1.symm.trans h2) (Ne.symm hdvabc.2.2.1)

end AltOn

end CFSG.StandardType

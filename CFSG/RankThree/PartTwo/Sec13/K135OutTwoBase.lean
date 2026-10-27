module

public import CFSG.RankThree.PartTwo.Sec13.K135G1Out

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def OutTwoGen (X : Type*) [Group X] : Prop :=
  ∀ V : Subgroup (MulAut X), IsPGroup 2 V →
    ∃ a ∈ V, ∃ b ∈ V,
      V ≤ Subgroup.closure ({a, b} : Set (MulAut X)) ⊔ (MulAut.conj : X →* MulAut X).range

theorem kFactOutTwo_of_gen
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Sec4.Census.List42 S → OutTwoGen S) : KFactOutTwo := h

theorem ot_two_gen_of_card_le_four {Γ : Type*} [Group Γ] [Finite Γ] (W : Subgroup Γ)
    (hW : Nat.card W ≤ 4) :
    ∃ α ∈ W, ∃ β ∈ W, W ≤ Subgroup.closure ({α, β} : Set Γ) := by
  by_cases h1 : ∃ α ∈ W, α ≠ 1
  · obtain ⟨α, hαW, hα1⟩ := h1
    by_cases hWC : W ≤ Subgroup.zpowers α
    · refine ⟨α, hαW, α, hαW, hWC.trans ?_⟩
      exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
    · obtain ⟨β, hβW, hβC⟩ : ∃ β ∈ W, β ∉ Subgroup.zpowers α := by
        by_contra hcon
        push Not at hcon
        exact hWC (by intro x hx; exact hcon x hx)
      refine ⟨α, hαW, β, hβW, ?_⟩
      have hHW : Subgroup.closure ({α, β} : Set Γ) ≤ W :=
        (Subgroup.closure_le W).mpr
          (Set.insert_subset_iff.mpr ⟨hαW, Set.singleton_subset_iff.mpr hβW⟩)
      have hCH : Subgroup.zpowers α ≤ Subgroup.closure ({α, β} : Set Γ) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
      have hβH : β ∈ Subgroup.closure ({α, β} : Set Γ) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hlt : Nat.card (Subgroup.zpowers α) < Nat.card (Subgroup.closure ({α, β} : Set Γ)) := by
        rcases Nat.lt_or_ge (Nat.card (Subgroup.zpowers α))
            (Nat.card (Subgroup.closure ({α, β} : Set Γ))) with h | h
        · exact h
        · exfalso
          have heq : Subgroup.zpowers α = Subgroup.closure ({α, β} : Set Γ) :=
            Subgroup.eq_of_le_of_card_ge hCH h
          apply hβC
          rw [heq]
          exact hβH
      have h2 : 2 ≤ Nat.card (Subgroup.zpowers α) := by
        rw [Nat.card_zpowers α]
        have hpos : 0 < orderOf α := orderOf_pos α
        have hne : orderOf α ≠ 1 := fun h => hα1 (orderOf_eq_one_iff.mp h)
        omega
      have hdvd : Nat.card (Subgroup.closure ({α, β} : Set Γ)) ∣ Nat.card W :=
        Subgroup.card_dvd_of_le hHW
      obtain ⟨k, hk⟩ := hdvd
      have hkle : k ≤ 1 := by
        by_contra hk2
        have hk2' : 2 ≤ k := by omega
        have h3 : Nat.card (Subgroup.closure ({α, β} : Set Γ)) * 2
            ≤ Nat.card (Subgroup.closure ({α, β} : Set Γ)) * k :=
          Nat.mul_le_mul_left _ hk2'
        omega
      have hWle : Nat.card W ≤ Nat.card (Subgroup.closure ({α, β} : Set Γ)) := by
        calc Nat.card W = Nat.card (Subgroup.closure ({α, β} : Set Γ)) * k := hk
          _ ≤ Nat.card (Subgroup.closure ({α, β} : Set Γ)) * 1 :=
            Nat.mul_le_mul_left _ hkle
          _ = Nat.card (Subgroup.closure ({α, β} : Set Γ)) := mul_one _
      exact le_of_eq (Subgroup.eq_of_le_of_card_ge hHW hWle).symm
  · push Not at h1
    refine ⟨1, Subgroup.one_mem W, 1, Subgroup.one_mem W, ?_⟩
    intro w hw
    rw [h1 w hw]
    exact Subgroup.one_mem _

theorem ot_cyclic_of_comparable {Γ : Type*} [Group Γ] [Finite Γ] (W : Subgroup Γ)
    (h : ∀ a ∈ W, ∀ b ∈ W, a ∈ Subgroup.zpowers b ∨ b ∈ Subgroup.zpowers a) :
    ∃ g ∈ W, W ≤ Subgroup.zpowers g := by
  haveI : Nonempty W := ⟨⟨1, W.one_mem⟩⟩
  obtain ⟨g0, hg0⟩ := Finite.exists_max (fun x : W => orderOf (x : Γ))
  refine ⟨(g0 : Γ), g0.2, ?_⟩
  intro x hx
  rcases h x hx (g0 : Γ) g0.2 with hxg | hgx
  · exact hxg
  · have hle : Subgroup.zpowers (g0 : Γ) ≤ Subgroup.zpowers x :=
      Subgroup.zpowers_le.mpr hgx
    have hord : orderOf x ≤ orderOf (g0 : Γ) := hg0 ⟨x, hx⟩
    have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers (g0 : Γ)) := by
      rw [Nat.card_zpowers, Nat.card_zpowers]
      exact hord
    have heq : Subgroup.zpowers (g0 : Γ) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    rw [heq]
    exact Subgroup.mem_zpowers x

theorem ot_lift_two_gen {X : Type*} [Group X]
    (V : Subgroup (MulAut X)) (α β : CFSG.ComponentClassification.OuterAutomorphisms.Outer X)
    (hα : α ∈ V.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)))
    (hβ : β ∈ V.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)))
    (hle : V.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)) ≤
      Subgroup.closure ({α, β} : Set (CFSG.ComponentClassification.OuterAutomorphisms.Outer X))) :
    ∃ a ∈ V, ∃ b ∈ V, V ≤ Subgroup.closure ({a, b} : Set (MulAut X)) ⊔
      (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨a, ha, hαa⟩ := Subgroup.mem_map.mp hα
  obtain ⟨b, hb, hβb⟩ := Subgroup.mem_map.mp hβ
  refine ⟨a, ha, b, hb, ?_⟩
  have hsub : ({α, β} : Set (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) ⊆
      (Subgroup.closure ({a, b} : Set (MulAut X))).map
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · exact Subgroup.mem_map.mpr
        ⟨a, Subgroup.subset_closure (Set.mem_insert _ _), hαa.trans h.symm⟩
    · exact Subgroup.mem_map.mpr
        ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)),
          hβb.trans h.symm⟩
  have hclos : Subgroup.closure ({α, β} : Set (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) ≤
      (Subgroup.closure ({a, b} : Set (MulAut X))).map
        (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)) :=
    (Subgroup.closure_le _).mpr hsub
  intro v hv
  have hmem : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)) v ∈
      Subgroup.closure ({α, β} : Set (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :=
    hle (Subgroup.mem_map_of_mem _ hv)
  obtain ⟨c, hc, hcv⟩ := Subgroup.mem_map.mp (hclos hmem)
  have h2 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X))
      (c⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, hcv, inv_mul_cancel]
  have h3 : c⁻¹ * v ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
    (QuotientGroup.eq_one_iff (c⁻¹ * v)).mp h2
  have h4 : c⁻¹ * v ∈ (MulAut.conj : X →* MulAut X).range := h3
  have hc' : c ∈ Subgroup.closure ({a, b} : Set (MulAut X)) ⊔ (MulAut.conj : X →* MulAut X).range :=
    Subgroup.mem_sup_left hc
  have hd' : c⁻¹ * v ∈
      Subgroup.closure ({a, b} : Set (MulAut X)) ⊔ (MulAut.conj : X →* MulAut X).range :=
    Subgroup.mem_sup_right h4
  have key := mul_mem hc' hd'
  rwa [mul_inv_cancel_left] at key

end CFSG.RankThree.PartTwo.Sec13.F135Last

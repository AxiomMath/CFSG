module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

theorem normalizer_of_abelian_bound {X : Type*} [Group X] [Finite X]
    (V L Nbg Vg : Subgroup X) (q : ℕ)
    (hVVg : V ⊓ Vg = ⊥) (hV1 : V ≠ ⊥) (hLab : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hLcard : Nat.card L = q ^ 5) (hVL : V ≤ L) (hLN : L ≤ Nbg) (hVgN : Vg ≤ Nbg)
    (hLVg : ∀ u ∈ L, ∀ v ∈ Vg, u * v = v * u) (hVgab : ∀ a ∈ Vg, ∀ b ∈ Vg, a * b = b * a)
    (hbound : ∀ A : Subgroup X, A ≤ Nbg → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ q ^ 5)
    (hZ : ∀ z ∈ Nbg, (∀ n ∈ Nbg, z * n = n * z) → z ∈ Vg)
    (hcomm : ∀ a ∈ Nbg, ∀ b ∈ Nbg, ⁅a, b⁆ ∈ Vg) (hp : IsPGroup 2 Nbg) :
    (∀ n ∈ Nbg, n ∈ Subgroup.normalizer (L : Set X)) ∧
    ¬ (∀ n ∈ Nbg, n ∈ Subgroup.normalizer (V : Set X)) := by
  have hcommS : ∀ a ∈ (L : Set X) ∪ (Vg : Set X), ∀ b ∈ (L : Set X) ∪ (Vg : Set X),
      a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact hLab a ha b hb
    · exact hLVg a ha b hb
    · exact (hLVg b hb a ha).symm
    · exact hVgab a ha b hb
  have hAab : ∀ a ∈ L ⊔ Vg, ∀ b ∈ L ⊔ Vg, a * b = b * a := by
    have hLS : L ≤ Subgroup.centralizer ((L : Set X) ∪ (Vg : Set X)) := by
      intro s hs
      exact Subgroup.mem_centralizer_iff.mpr
        (fun h hh => hcommS h hh s (Set.mem_union_left _ hs))
    have hVS : Vg ≤ Subgroup.centralizer ((L : Set X) ∪ (Vg : Set X)) := by
      intro s hs
      exact Subgroup.mem_centralizer_iff.mpr
        (fun h hh => hcommS h hh s (Set.mem_union_right _ hs))
    have hcen : L ⊔ Vg ≤ Subgroup.centralizer ((L : Set X) ∪ (Vg : Set X)) :=
      sup_le hLS hVS
    intro a ha b hb
    have hb1 : ∀ t ∈ (L : Set X) ∪ (Vg : Set X), t * b = b * t :=
      fun t ht => Subgroup.mem_centralizer_iff.mp (hcen hb) t ht
    have hsub : L ⊔ Vg ≤ Subgroup.centralizer ({b} : Set X) := by
      apply sup_le
      · intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hb1 t (Set.mem_union_left _ ht)).symm
      · intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hb1 t (Set.mem_union_right _ ht)).symm
    exact (Subgroup.mem_centralizer_iff.mp (hsub ha) b (Set.mem_singleton b)).symm
  have hAle : L ⊔ Vg ≤ Nbg := sup_le hLN hVgN
  have hcardA : Nat.card (L ⊔ Vg : Subgroup X) ≤ q ^ 5 := hbound (L ⊔ Vg) hAle hAab
  have hEq : L = L ⊔ Vg :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hLcard]; exact hcardA)
  have hVgL : Vg ≤ L := le_sup_right.trans (le_of_eq hEq.symm)
  have hpart2 : ∀ n ∈ Nbg, n ∈ Subgroup.normalizer (L : Set X) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype (fun l hl => ?_)
    have hl' : l ∈ L := hl
    have hcnL : ⁅n, l⁆ ∈ L := hVgL (hcomm n hn l (hLN hl'))
    have hprod : n * l * n⁻¹ = ⁅n, l⁆ * l := by
      rw [commutatorElement_def]
      group
    show n * l * n⁻¹ ∈ L
    rw [hprod]
    exact L.mul_mem hcnL hl'
  have hpart3 : ¬ (∀ n ∈ Nbg, n ∈ Subgroup.normalizer (V : Set X)) := by
    intro hall
    have hVN : V ≤ Nbg := hVL.trans hLN
    have hnorm : Nbg ≤ Subgroup.normalizer (V : Set X) := by
      intro n hn
      exact hall n hn
    haveI : (V.subgroupOf Nbg).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVN).mpr hnorm
    haveI : Group.IsNilpotent ↥Nbg := hp.isNilpotent
    have hne : V.subgroupOf Nbg ≠ ⊥ := by
      intro h
      apply hV1
      rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hVN] at h
      exact h
    have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
    rw [ne_eq, Subgroup.eq_bot_iff_forall] at hcen
    push Not at hcen
    obtain ⟨w, hwH, hw1⟩ := hcen
    obtain ⟨hwV, hwC⟩ := Subgroup.mem_inf.mp hwH
    have hwV' : (w : X) ∈ V := Subgroup.mem_subgroupOf.mp hwV
    have hwcomm : ∀ n ∈ Nbg, (w : X) * n = n * (w : X) := by
      intro n hn
      have h1 := Subgroup.mem_center_iff.mp hwC ⟨n, hn⟩
      have h2 := congrArg Subtype.val h1
      simpa using h2.symm
    have hwVg : (w : X) ∈ Vg := hZ (w : X) w.2 hwcomm
    have hw_bot : (w : X) ∈ V ⊓ Vg := Subgroup.mem_inf.mpr ⟨hwV', hwVg⟩
    rw [hVVg, Subgroup.mem_bot] at hw_bot
    exact hw1 (Subtype.ext hw_bot)
  exact ⟨hpart2, hpart3⟩

end CFSG.RankThree.GF2n.Stroth80

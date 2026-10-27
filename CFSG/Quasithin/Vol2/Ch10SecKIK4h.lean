module

public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open Equiv Equiv.Perm
open scoped commutatorElement

noncomputable def altOn (s : Finset (Fin 7)) : Subgroup (Perm (Fin 7)) :=
  (alternatingGroup ↥s).map (Perm.ofSubtype : Perm ↥s →* Perm (Fin 7))

theorem mem_altOn {s : Finset (Fin 7)} {σ : Perm (Fin 7)} :
    σ ∈ altOn s ↔ σ ∈ alternatingGroup (Fin 7) ∧ ∀ x ∉ s, σ x = x := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨?_, fun x hx => Perm.ofSubtype_apply_of_not_mem τ hx⟩
    rw [mem_alternatingGroup, sign_ofSubtype]
    exact hτ
  · rintro ⟨hσ, hfix⟩
    have h2 : ∀ x, σ x ≠ x → x ∈ s := fun x hx => by
      by_contra h
      exact hx (hfix x h)
    have h1 : ∀ x, σ x ∈ s ↔ x ∈ s := by
      intro x
      constructor
      · intro hx
        by_contra h
        have := hfix x h
        rw [this] at hx
        exact h hx
      · intro hx
        by_contra h
        have h' := σ.injective (hfix (σ x) h)
        rw [h'] at h
        exact h hx
    refine ⟨σ.subtypePerm h1, ?_, Perm.ofSubtype_subtypePerm h1 h2⟩
    show σ.subtypePerm h1 ∈ alternatingGroup ↥s
    rw [mem_alternatingGroup]
    convert (sign_subtypePerm σ h1 h2).trans (mem_alternatingGroup.1 hσ)

noncomputable def altOnEquiv (s : Finset (Fin 7)) : ↥(alternatingGroup ↥s) ≃* ↥(altOn s) :=
  (alternatingGroup ↥s).equivMapOfInjective _ Perm.ofSubtype_injective

theorem card_altOn (s : Finset (Fin 7)) (hs : 2 ≤ s.card) :
    Nat.card ↥(altOn s) = s.card.factorial / 2 := by
  have : Nontrivial ↥s := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
    omega
  rw [← Nat.card_congr (altOnEquiv s).toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
    Fintype.card_coe]

theorem isSimpleGroup_altOn (s : Finset (Fin 7)) (hs : 5 ≤ s.card) :
    IsSimpleGroup ↥(altOn s) := by
  have : IsSimpleGroup ↥(alternatingGroup ↥s) := alternatingGroup.isSimpleGroup (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hs)
  exact (altOnEquiv s).symm.isSimpleGroup

theorem isCycle_of_order_five {g : Perm (Fin 7)} (hg : orderOf g = 5) :
    g.IsCycle ∧ g.support.card = 5 := by
  have h1 : g.IsCycle :=
    isCycle_of_prime_order' (by rw [hg]; norm_num) (by rw [hg, Fintype.card_fin]; norm_num)
  exact ⟨h1, h1.orderOf.symm.trans hg⟩

theorem fix_or_swap {a b : Fin 7} (hab : a ≠ b) {ρ : Perm (Fin 7)} (ha : ρ a = a ∨ ρ a = b)
    (hb : ρ b = a ∨ ρ b = b) :
    (ρ a = a ∧ ρ b = b ∧ ρ⁻¹ a = a ∧ ρ⁻¹ b = b) ∨
      (ρ a = b ∧ ρ b = a ∧ ρ⁻¹ a = b ∧ ρ⁻¹ b = a) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ρ.injective (ha.trans hb.symm)) hab
  · exact Or.inl ⟨ha, hb, by rw [Perm.inv_eq_iff_eq, ha], by rw [Perm.inv_eq_iff_eq, hb]⟩
  · exact Or.inr ⟨ha, hb, by rw [Perm.inv_eq_iff_eq, hb], by rw [Perm.inv_eq_iff_eq, ha]⟩
  · exact absurd (ρ.injective (ha.trans hb.symm)) hab

theorem fix_of_perfect_of_pair {Lp : Subgroup (Perm (Fin 7))} (hperf : ⁅Lp, Lp⁆ = Lp)
    {a b : Fin 7} (hab : a ≠ b) (hpair : ∀ σ ∈ Lp, (σ a = a ∨ σ a = b) ∧ (σ b = a ∨ σ b = b)) :
    ∀ σ ∈ Lp, σ a = a := by
  have hfix : ⁅Lp, Lp⁆ ≤ MulAction.stabilizer (Perm (Fin 7)) a := by
    rw [Subgroup.commutator_le]
    intro σ hσ τ hτ
    rw [MulAction.mem_stabilizer_iff, Perm.smul_def, commutatorElement_def]
    simp only [Perm.mul_apply]
    rcases fix_or_swap hab (hpair σ hσ).1 (hpair σ hσ).2 with
        ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
      rcases fix_or_swap hab (hpair τ hτ).1 (hpair τ hτ).2 with
        ⟨k1, k2, k3, k4⟩ | ⟨k1, k2, k3, k4⟩
    · rw [k3, h3, k1, h1]
    · rw [k3, h4, k2, h1]
    · rw [k3, h3, k2, h2]
    · rw [k3, h4, k1, h2]
  intro σ hσ
  have := hfix (hperf.symm ▸ hσ)
  rwa [MulAction.mem_stabilizer_iff, Perm.smul_def] at this

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

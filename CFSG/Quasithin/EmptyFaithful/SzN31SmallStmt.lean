module

public import CFSG.Quasithin.EmptyFaithful.SzN31Top

public section

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11

@[expose] def SylowGL6NoCover : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V], Module.finrank (ZMod 2) V = 6 →
    ∀ S : Subgroup (GLV V), IsPGroup 3 S → Nat.card S = 81 →
      ∀ (Q : Type) [Group Q] [Finite Q], IsPGroup 3 Q →
        (∀ E : Subgroup Q, (∀ x ∈ E, x ^ 3 = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
          Nat.card E ≤ 3 ^ 2) →
        ∀ π : Q →* S, ¬ Function.Surjective π

@[expose] def SmallCase (d : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A : Subgroup (GLV V)) (m : ℕ),
    G94Hyp Γ A m → Group.IsSolvable ↥Γ → KCFor Γ → m ≤ 2 → Module.finrank (ZMod 2) V = d →
      G94Concl Γ A m

@[expose] def SmallCase6 : Prop := SylowGL6NoCover → SmallCase 6

@[expose] def SmallOdd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A : Subgroup (GLV V)) (m : ℕ),
    G94Hyp Γ A m → Group.IsSolvable ↥Γ → KCFor Γ → m ≤ 2 → Odd (Module.finrank (ZMod 2) V) → False

theorem g94Small_of_cases (hT : SylowGL6NoCover) (h2 : SmallCase 2) (h4 : SmallCase 4)
    (h6 : SmallCase6) (hodd : SmallOdd) : G94Small := by
  intro V _ _ _ Γ A m hyp hsolv hkc hm
  have hd : Module.finrank (ZMod 2) V ≤ 6 := by
    have := hyp.bound
    omega
  have hpos : 0 < Module.finrank (ZMod 2) V := by
    have hne : (⊤ : Submodule (ZMod 2) V) ≠ ⊥ := hyp.irreducible.ne_bot
    have : Nontrivial V := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hne (Subsingleton.elim _ _)
    exact Module.finrank_pos
  obtain ⟨d, hd'⟩ : ∃ d, Module.finrank (ZMod 2) V = d := ⟨_, rfl⟩
  rw [hd'] at hd hpos
  interval_cases d
  · exact (hodd V Γ A m hyp hsolv hkc hm (by rw [hd']; exact ⟨0, rfl⟩)).elim
  · exact h2 V Γ A m hyp hsolv hkc hm hd'
  · exact (hodd V Γ A m hyp hsolv hkc hm (by rw [hd']; exact ⟨1, rfl⟩)).elim
  · exact h4 V Γ A m hyp hsolv hkc hm hd'
  · exact (hodd V Γ A m hyp hsolv hkc hm (by rw [hd']; exact ⟨2, rfl⟩)).elim
  · exact h6 hT V Γ A m hyp hsolv hkc hm hd'

end CFSG.Quasithin.SzN31

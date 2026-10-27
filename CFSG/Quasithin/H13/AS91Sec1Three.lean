module

public import CFSG.Quasithin.H13.AS91Sec1Defs

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} {Δ : SimpleGraph V}

theorem Perp.symm {x y : V} (h : Perp Δ x y) : Perp Δ y x :=
  h.elim (fun e => Or.inl e.symm) fun a => Or.inr a.symm

theorem hypA_of_hypB {N : ℕ} {R : ℕ → V → V → V → Prop} (h : HypB Δ N R) :
    HypA Δ N (induced Δ R) where
  symm k x y := by
    rintro (h1 | ⟨u, hu⟩)
    · exact Or.inl h1.symm
    · exact Or.inr ⟨u, h.symm k x u y hu⟩
  mono k hk x y := by
    rintro (h1 | ⟨u, hu⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨u, h.mono k hk x u y hu⟩
  zero x y := by
    constructor
    · rintro (h1 | ⟨u, hu⟩)
      · exact h1
      · exact Or.inr ((h.zero x u y).mp hu).2.2
    · exact fun h1 => Or.inl h1
  top x y := by
    constructor
    · rintro (h1 | ⟨u, hu⟩)
      · exact Or.inl h1
      · obtain ⟨h1, h2, -⟩ := (h.top x u y).mp hu
        exact Or.inr ⟨u, h1, h2⟩
    · rintro (h1 | ⟨w, h1, h2⟩)
      · exact Or.inl h1
      · by_cases hxy : x = y
        · exact Or.inl (Or.inl hxy)
        · exact Or.inr ⟨w, (h.top x w y).mpr ⟨h1, h2, hxy⟩⟩
  a2 k hk x y z hxy hd2y hd2z := by
    obtain ⟨u, hu⟩ : ∃ u, R (k + 1) x u y := by
      rcases hxy with h1 | h1
      · exfalso
        rcases h1 with e | a
        · exact hd2y.1 e
        · exact hd2y.2.1 a
      · exact h1
    have hu0 : ¬ R 0 x u y := fun h0 => hd2y.2.1 ((h.zero x u y).mp h0).2.2
    obtain ⟨w, hxw, hwz⟩ := hd2z.2.2
    have hw : R N x w z := (h.top x w z).mpr ⟨hxw, hwz, hd2z.1⟩
    have hw0 : ¬ R 0 x w z := fun h0 => hd2z.2.1 ((h.zero x w z).mp h0).2.2
    obtain ⟨a, b, ha, hb, hab⟩ := h.b2 k hk x u y w z hu hu0 hw hw0
    obtain ⟨-, ⟨hxb, hzb⟩, -⟩ := hb
    refine ⟨a, b, ?_, ?_, hxb, hzb, hab⟩
    · rcases ha with ⟨-, ⟨-, hya⟩, -⟩ | ⟨-, c, -, hyca⟩
      · exact Or.inl (Or.inr hya)
      · exact Or.inr ⟨c, hyca⟩
    · rcases ha with ⟨-, ⟨hxa, -⟩, -⟩ | ⟨hxa, -⟩
      · exact hxa
      · exact hxa

end CFSG.Quasithin.H13.AS91

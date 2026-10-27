module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem dvd_card_fixedSubgroup_of_embedding {G₀ G : Type} [Group G₀] [Group G] [Finite G]
    {α : MulAut G} (ψ : G₀ →* G) (hψ : Function.Injective ψ) (hfix : ∀ a, α (ψ a) = ψ a)
    {m : ℕ} (hm : m ∣ Nat.card G₀) : m ∣ Nat.card (fixedSubgroup α) := by
  have hle : ψ.range ≤ fixedSubgroup α := by
    rintro _ ⟨a, rfl⟩
    show α (ψ a) = ψ a
    exact hfix a
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at hdvd
  exact hm.trans hdvd

theorem fixedTooBig_of_embedding {G₀ G : Type} [Group G₀] [Group G] [Finite G] {α : MulAut G}
    (ψ : G₀ →* G) (hψ : Function.Injective ψ) (hfix : ∀ a, α (ψ a) = ψ a)
    (h27 : 27 ∣ Nat.card G₀) : FixedTooBig α :=
  Or.inl (dvd_card_fixedSubgroup_of_embedding ψ hψ hfix h27)

theorem card_threeTorus : Nat.card (Fin 3 → Multiplicative (ZMod 3)) = 27 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_multiplicative,
    ZMod.card]
  norm_num

theorem fixedTooBig_of_torus {G : Type} [Group G] [Finite G] {α : MulAut G}
    (T : (Fin 3 → Multiplicative (ZMod 3)) →* G) (hT : Function.Injective T)
    (hfix : ∀ x, α (T x) = T x) : FixedTooBig α :=
  fixedTooBig_of_embedding T hT hfix (by rw [card_threeTorus])

end CFSG.StandardType.FF81.CatQ1

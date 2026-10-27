module

public import CFSG.Quasithin.Background.ShultG53Defs

public section

namespace CFSG.Quasithin.ShultG53

theorem exists_lift {N M P : Type} [AddCommGroup N] [AddCommGroup M] [AddCommGroup P]
    (π : N →+ M) (hπ : Function.Surjective π) (φ : N →+ P) (hker : ∀ n, π n = 0 → φ n = 0) :
    ∃ f : M →+ P, ∀ n, f (π n) = φ n := by
  refine ⟨{ toFun := fun m => φ (Function.surjInv hπ m)
            map_zero' := hker _ (Function.surjInv_eq hπ 0)
            map_add' := fun a b => ?_ }, fun n => ?_⟩
  · have h1 : π (Function.surjInv hπ (a + b) - (Function.surjInv hπ a + Function.surjInv hπ b))
        = 0 := by
      rw [map_sub, map_add, Function.surjInv_eq hπ, Function.surjInv_eq hπ,
        Function.surjInv_eq hπ, sub_self]
    have h2 := hker _ h1
    rw [map_sub, map_add, sub_eq_zero] at h2
    exact h2
  · have h1 : π (Function.surjInv hπ (π n) - n) = 0 := by
      rw [map_sub, Function.surjInv_eq hπ, sub_self]
    have h2 := hker _ h1
    rw [map_sub, sub_eq_zero] at h2
    exact h2

theorem iso_of_equivariant_surj {X : Type} [Group X] {N : Type} [AddCommGroup N]
    (a : X → N → N) {M₁ M₂ : Md X} (π₁ : N →+ M₁.carrier) (π₂ : N →+ M₂.carrier)
    (hs₁ : Function.Surjective π₁) (hs₂ : Function.Surjective π₂)
    (hk : ∀ n, π₁ n = 0 ↔ π₂ n = 0) (he₁ : ∀ g n, π₁ (a g n) = M₁.ρ g (π₁ n))
    (he₂ : ∀ g n, π₂ (a g n) = M₂.ρ g (π₂ n)) : M₁.Iso M₂ := by
  obtain ⟨f, hf⟩ := exists_lift π₁ hs₁ π₂ (fun n h => (hk n).mp h)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨n, rfl⟩ := hs₁ m
    rw [hf] at hm
    exact (hk n).mpr hm
  have hsurj : Function.Surjective f := by
    intro m
    obtain ⟨n, rfl⟩ := hs₂ m
    exact ⟨π₁ n, hf n⟩
  refine ⟨AddEquiv.ofBijective f ⟨hinj, hsurj⟩, fun g m => ?_⟩
  obtain ⟨n, rfl⟩ := hs₁ m
  show f (M₁.ρ g (π₁ n)) = M₂.ρ g (f (π₁ n))
  rw [← he₁, hf, hf, he₂]

end CFSG.Quasithin.ShultG53

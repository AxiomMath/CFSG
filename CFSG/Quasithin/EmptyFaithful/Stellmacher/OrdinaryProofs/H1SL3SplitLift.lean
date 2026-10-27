module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitCoef
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitRoots

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

theorem crossedHom_lift {A B M : Type*} [Group A] [Group B] [AddCommGroup M]
    (φ : A →* B) (hφ : Function.Surjective φ) (ρ : B →* AddMonoid.End M)
    (c : A → M) (hc : ∀ a b : A, c (a * b) = c a + ρ (φ a) (c b))
    (hk : ∀ k : A, φ k = 1 → c k = 0) :
    ∃ f : B → M, (∀ a : A, f (φ a) = c a) ∧ ∀ g h : B, f (g * h) = f g + ρ g (f h) := by
  have hfac : ∀ a a' : A, φ a = φ a' → c a = c a' := by
    intro a a' h
    have hk' : φ (a⁻¹ * a') = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have hsplit : a' = a * (a⁻¹ * a') := (mul_inv_cancel_left a a').symm
    rw [hsplit, hc, hk _ hk', map_zero, add_zero]
  have key : ∀ a : A, c (Function.surjInv hφ (φ a)) = c a :=
    fun a => hfac _ _ (Function.surjInv_eq hφ (φ a))
  refine ⟨fun g => c (Function.surjInv hφ g), fun a => key a, fun g h => ?_⟩
  dsimp only
  obtain ⟨a, rfl⟩ := hφ g
  obtain ⟨b, rfl⟩ := hφ h
  rw [← map_mul, key, key, key, hc]

theorem piAct_fixed_free {H : Type*} [Group H] {ι V₀ : Type*} [AddCommGroup V₀]
    (e : H →* AddMonoid.End V₀) (t : H) (h : ∀ v : V₀, e t v = v → v = 0)
    (x : ι → V₀) (hx : piAct e t x = x) : x = 0 :=
  funext fun i => h (x i) (congrFun hx i)

theorem crossedHom_principal_coef {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {N Q : Type*} [AddCommGroup N] [Finite N] [AddCommGroup Q] [Module (ZMod 2) Q]
    (ρ : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End N)
    (hX : ∃ t ∈ diagSL (F := F), (∀ a : F, t * unitriMk a 0 0 = unitriMk a 0 0 * t) ∧
      ∀ x : N, ρ t x = x → x = 0)
    (hY : ∃ t ∈ diagSL (F := F), (∀ b : F, t * unitriMk 0 b 0 = unitriMk 0 b 0 * t) ∧
      ∀ x : N, ρ t x = x → x = 0)
    (hZ : ∃ t ∈ diagSL (F := F), (∀ c : F, t * unitriMk 0 0 c = unitriMk 0 0 c * t) ∧
      ∀ x : N, ρ t x = x → x = 0)
    (f : Matrix.SpecialLinearGroup (Fin 3) F → (N →+ Q))
    (hf : ∀ g h, f (g * h) = f g + homAct ρ g (f h)) :
    ∃ w : N →+ Q, ∀ g, f g = w - homAct ρ g w := by
  have hM : ∀ {t : Matrix.SpecialLinearGroup (Fin 3) F}, (∀ x : N, ρ t x = x → x = 0) →
      ∀ v : N →+ Q, homAct ρ t v = v → v = 0 :=
    fun ht v hv => homAct_fixed_free ρ _ ht v hv
  refine crossedHom_principal_of_roots_gen (homAct ρ) f hf ?_ ?_ ?_
  · obtain ⟨t, ht, hc, hfix⟩ := hX
    exact ⟨t, ht, hc, fun v hv => hM hfix v hv⟩
  · obtain ⟨t, ht, hc, hfix⟩ := hY
    exact ⟨t, ht, hc, fun v hv => hM hfix v hv⟩
  · obtain ⟨t, ht, hc, hfix⟩ := hZ
    exact ⟨t, ht, hc, fun v hv => hM hfix v hv⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {F : Type} [Field F]

theorem card_fix_sq_le {M : Type*} [AddCommGroup M] [Module F M] [Finite M] (T : M →+ M)
    (σ : F →+* F) {θ : F} (hθ : σ θ ≠ θ) (hT : ∀ (c : F) (x : M), T (c • x) = σ c • T x) :
    Nat.card {x : M // T x = x} ^ 2 ≤ Nat.card M := by
  have hd : θ - σ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  let φ : {x : M // T x = x} × {x : M // T x = x} → M := fun p => p.1.1 + θ • p.2.1
  have hφ : Function.Injective φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    simp only [φ] at h
    have h1 : T (a + θ • b) = T (a' + θ • b') := by rw [h]
    rw [map_add, map_add, hT, hT, ha, hb, ha', hb'] at h1
    have h2 : (θ - σ θ) • (b - b') = 0 := by
      rw [sub_smul, smul_sub, smul_sub]
      have e1 : θ • b - θ • b' = a' - a := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, ← h, add_comm a]
      have e2 : σ θ • b - σ θ • b' = a' - a := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, ← h1, add_comm a]
      rw [e1, e2, sub_self]
    have hbb : b = b' := by
      rw [smul_eq_zero] at h2
      exact sub_eq_zero.mp (h2.resolve_left hd)
    subst hbb
    have haa : a = a' := add_right_cancel h
    subst haa
    rfl
  have h3 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, ← sq] at h3

end CFSG.Quasithin.Vol2.Ch11.G2Q8

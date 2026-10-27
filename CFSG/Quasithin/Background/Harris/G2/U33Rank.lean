module

public import CFSG.Quasithin.Background.Harris.G2.Setup
public import CFSG.Quasithin.Background.SmithB42U33Iso
public import CFSG.Quasithin.Background.SmithB42G2Rank

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.H13

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem card_le_eight_autDerived
    (B : Subgroup (MulAut ↥(g2Derived (ZMod 2))))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 3 := by
  let ρ : ↥(quasithinG2 (ZMod 2)) ≃* MulAut ↥(g2Derived (ZMod 2)) :=
    MulEquiv.ofBijective _ B42U33.conjNormal_bijective
  let ε : ↥(quasithinG2 (ZMod 2)) ≃* ↥(cayleyGroup (ZMod 2)) :=
    MulEquiv.subgroupCongr CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup
  let χ : MulAut ↥(g2Derived (ZMod 2)) ≃* ↥(cayleyGroup (ZMod 2)) := ρ.symm.trans ε
  have hcard : Nat.card (B.map χ.toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective χ.injective
  have h := CFSG.Quasithin.B42G2.card_le_cube (F := ZMod 2) (n := 1)
    (by rw [Nat.card_zmod]; rfl) le_rfl (Γ := B.map χ.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hsq x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hc x hx y hy])
  rw [hcard, Nat.card_zmod] at h
  simpa using h

theorem m_le_three_u33 [Finite V]
    {Γ A L : Subgroup (GLV V)} {m : ℕ}
    (hs : OneCompSetting Γ A L m) (θ : ↥L ≃* ↥(g2Derived (ZMod 2))) : m ≤ 3 :=
  m_le_of_autRank hs θ fun B hc hsq => card_le_eight_autDerived B hc hsq

end CFSG.Quasithin.G11.Harris.G2

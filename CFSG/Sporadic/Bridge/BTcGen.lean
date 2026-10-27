module

public import CFSG.Sporadic.Bridge.BSurj

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native

theorem closure_eq_top_of_conj {H : Subgroup NativeSporadic.B}
    {a b : NativeSporadic.B} (ha : a ∈ H) (hb : b ∈ H) (Gu : GL (Fin 4370) (ZMod 2))
    (hA : glA₁ * Gu = Gu * bGL a) (hB : glA₂ * Gu = Gu * bGL b) : H = ⊤ := by
  let c : GL (Fin 4370) (ZMod 2) →* GL (Fin 4370) (ZMod 2) := (MulAut.conj Gu⁻¹).toMonoidHom
  have hc : ∀ g, c g = Gu⁻¹ * g * Gu := fun g => by simp [c]
  have hmap : bGL.range.map c ≤ H.map bGL := by
    rw [range_bGL, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨a, ha, ?_⟩
      rw [hc, mul_assoc, hA, ← mul_assoc, inv_mul_cancel, one_mul]
    · refine ⟨b, hb, ?_⟩
      rw [hc, mul_assoc, hB, ← mul_assoc, inv_mul_cancel, one_mul]
  have hle : H.map bGL ≤ bGL.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hinj : Function.Injective c := (MulAut.conj Gu⁻¹).injective
  have heq : H.map bGL = bGL.range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_le_of_le hmap
  rw [eq_top_iff]
  intro x _
  have hx : bGL x ∈ H.map bGL := by
    rw [heq]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← bGL_injective hyx]

end CFSG.Sporadic.Bridge.B

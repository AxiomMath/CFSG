module

public import CFSG.Quasithin.Background.F918N0
import CFSG.Quasithin.Background.F918N7
import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.F918M0
import CFSG.Quasithin.Background.B5Models

public section

namespace CFSG.Quasithin

@[expose] def D35InspOrbit : Prop :=
  ∀ (X : Type) [CommGroup X] [Finite X] (Mb Tb Lb : Subgroup (MulAut X)) (Vb : Subgroup X)
    (A : Subgroup (MulAut X)),
    Z35 Mb Tb Lb Vb → Mb = Lb → A ≤ Tb ⊓ stabSub Vb →
    B42Conclusion (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) →
    (∀ s ∈ Tb, ∀ r ∈ Tb, XMod.Iso ↥Mb (Vb.map s.toMonoidHom) Vb ∨
        XMod.Iso ↥Mb (Vb.map r.toMonoidHom) Vb ∨
        XMod.Iso ↥Mb (Vb.map s.toMonoidHom) (Vb.map r.toMonoidHom)) ∧
    ((B42Case1 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) ∨
        B42Case4 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb) ∨
        B42Case5 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub A Vb) ∨
        B42Case10 (autSub (Lb ⊔ (Tb ⊓ stabSub Vb)) Vb) (autSub Lb Vb) (autSub A Vb)) →
      ∀ s ∈ Tb, XMod.Iso ↥Mb (Vb.map s.toMonoidHom) Vb)

theorem d35InspB42_of_orbit (hA21 : AsA21SQTKSection) (h : D35InspOrbit) : D35InspB42 := by
  intro X _ _ Mb Tb Lb Vb A hZ hML hA hb42
  obtain ⟨hα, hβ⟩ := h X Mb Tb Lb Vb A hZ hML hA hb42
  have hone : Vb.map (1 : MulAut X).toMonoidHom = Vb := mem_stabSub_iff_map_eq.mp (one_mem _)
  have hst : ∀ s ∈ Tb, XMod.Iso ↥Mb (Vb.map s.toMonoidHom) Vb → s ∈ stabSub Vb := by
    intro s hs hiso
    have he := hZ.homog s hs 1 Tb.one_mem (by rwa [hone])
    rw [hone] at he
    exact mem_stabSub_iff_map_eq.mpr he
  have hpair : ∀ s ∈ Tb, ∀ r ∈ Tb,
      XMod.Iso ↥Mb (Vb.map s.toMonoidHom) (Vb.map r.toMonoidHom) → s⁻¹ * r ∈ stabSub Vb := by
    intro s hs r hr hiso
    have he := hZ.homog s hs r hr hiso
    rw [mem_stabSub_iff_map_eq, map_mul_aut', ← he, ← map_mul_aut', inv_mul_cancel, hone]
  have hns : ¬ Tb ≤ stabSub Vb := z35_not_le_stab hZ
  refine ⟨?_, fun _ => ?_⟩
  · obtain ⟨t, ht, htn⟩ := IsConcreteLE.not_le_iff_exists.mp hns
    refine (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
      ⟨t, ht, fun h1 => htn (Subgroup.mem_inf.mp h1).2, fun b hb => ?_⟩).le
    rcases hα t⁻¹ (Tb.inv_mem ht) b hb with h1 | h1 | h1
    · exact absurd (inv_mem_iff.mp (hst _ (Tb.inv_mem ht) h1)) htn
    · exact Or.inr (Subgroup.mem_inf.mpr ⟨hb, hst b hb h1⟩)
    · have h2 := hpair _ (Tb.inv_mem ht) b hb h1
      rw [inv_inv] at h2
      exact Or.inl (Subgroup.mem_inf.mpr ⟨Tb.mul_mem ht hb, h2⟩)
  · have hstab : ¬ ∀ s ∈ Tb, XMod.Iso ↥Mb (Vb.map s.toMonoidHom) Vb :=
      fun hall => hns fun s hs => hst s hs (hall s hs)
    have hLs : Lb ≤ stabSub Vb := by
      subst hML
      intro g hg u
      refine ⟨fun hu => ?_, fun hu => hZ.irr.1 ⟨g, hg⟩ u hu⟩
      have h1 := hZ.irr.1 ⟨g, hg⟩⁻¹ _ hu
      change (g⁻¹ : MulAut X) (g u) ∈ Vb at h1
      simpa using h1
    have hfix : fixV (autSub Lb Vb) = ⊥ := by
      have h1 := map_subtype_fixV_autSub hLs
      rw [show fixV Lb = ⊥ from hML ▸ hZ.fix, inf_bot_eq] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ Vb.subtype_injective).mp h1
    rw [D35Five, hfix, inf_bot_eq]
    rcases hb42 with c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11
    · exact absurd (hβ (Or.inl c1)) hstab
    · exact Or.inl (Or.inl c2.2.1)
    · obtain ⟨⟨n, hn, hJL⟩, -⟩ := c3
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · rw [hJL h1] at hn
        exact Or.inl (Or.inr (Or.inl ⟨n, hn⟩))
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl
        · obtain ⟨K, _, _, hK, -⟩ := hn
          have := Finite.one_lt_card (α := K)
          rw [hK, pow_zero] at this
          exact absurd this (lt_irrefl 1)
        · obtain ⟨-, hL, -⟩ := FFC.ident_sp4 (z35_b4Hyp hA21 hZ hML) hn
          have h6 := B5.alternatingNatural_derived (by norm_num) (asSp4S6 _ _ _ _ hn)
          rw [← hL] at h6
          exact Or.inl (Or.inr (Or.inr (Or.inl h6)))
    · exact absurd (hβ (Or.inr (Or.inl c4))) hstab
    · exact absurd (hβ (Or.inr (Or.inr (Or.inl c5)))) hstab
    · exact Or.inl (Or.inr (Or.inr (Or.inl c6.2.1)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c7.2.2.1)))))
    · exact Or.inr (Or.inl c8)
    · obtain ⟨-, n, hn, hnat, -⟩ := c9
      rcases hn with rfl | rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hnat))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hnat)))))
    · exact absurd (hβ (Or.inr (Or.inr (Or.inr c10)))) hstab
    · exact Or.inr (Or.inr c11)

end CFSG.Quasithin

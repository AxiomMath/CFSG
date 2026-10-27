module

public import CFSG.Quasithin.Background.F918X1

public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.Quasithin.F918X

open CFSG.LieType.CurtisTits

theorem noOddCoverHatA6_holds : NoOddCoverHatA6 := by
  intro E Γ _ _ _ hE hZ he f hf hodd
  obtain ⟨e⟩ := he
  have : Finite Γ := Finite.of_surjective f hf
  have : Group.IsPerfect E := hE.1
  let π : E →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center Γ)).comp f)
  have hπ : Function.Surjective π :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp hf)
  have hmem : ∀ x : E, x ∈ π.ker ↔ f x ∈ Subgroup.center Γ := by
    intro x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk (f x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hcent : π.ker ≤ Subgroup.center E := by
    rcases le_center_or_eq_top_of_isQuasisimple hE π.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : ↥(alternatingGroup (Fin 6)))
      obtain ⟨y, rfl⟩ := hπ a
      exact ha (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top y))
  have hoddN : Odd (Nat.card π.ker) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) 2 h2
    have hx2 : (x : E) ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this
    have hfx : f x ∈ Subgroup.center Γ := (hmem x).1 x.2
    have hd3 : orderOf (f x) ∣ 3 := hZ ▸ Subgroup.orderOf_dvd_natCard _ hfx
    have hd2 : orderOf (f x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx2, map_one])
    have hf1 : f x = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hd2 hd3))
    have := hodd x (MonoidHom.mem_ker.mpr hf1)
    rw [Subgroup.orderOf_coe, hx] at this
    exact absurd this (by decide)
  have hcard : Nat.card π.ker ≤ 3 := by
    rcases (CFSG.SectionRank.alternating_small_odd_cover_bound (n := 6) (by norm_num)
      (by norm_num) π hπ hcent hoddN).2 (Or.inl rfl) with h | h <;> omega
  let g : π.ker → Subgroup.center Γ := fun x => ⟨f x, (hmem x).1 x.2⟩
  have hg : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := hf z
    exact ⟨⟨y, (hmem y).2 hz⟩, rfl⟩
  have hginj : Function.Injective g :=
    (hg.bijective_of_nat_card_le (hZ ▸ hcard)).1
  refine (injective_iff_map_eq_one f).mpr fun x hx => ?_
  have hxN : x ∈ π.ker := (hmem x).2 (hx ▸ Subgroup.one_mem _)
  have := hginj (a₁ := ⟨x, hxN⟩) (a₂ := 1) (Subtype.ext (by show f x = f 1; rw [hx, map_one]))
  exact congrArg Subtype.val this

end CFSG.Quasithin.F918X

module

public import CFSG.Permutation.FiveTransitive.PGroupConjugateIntoPreimageSylow
public import CFSG.Permutation.FiveTransitive.SevenCommutingSwapInvolution

public section

namespace CFSG

namespace FiveTransitive.CommutingTriplePreimageSylow

theorem exists_conjugate
    {G F : Type*} [Group G] [Finite G] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 7) (e : Fin 6 ↪ F)
    (f : G →* Equiv.Perm F) (hf : Function.Surjective f)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap f))
    (a x u : G) (ha : a ^ 2 = 1) (hx : x ^ 2 = 1) (hu : u ^ 2 = 1)
    (hax : Commute a x) (hau : Commute a u) (hxu : Commute x u)
    (hfa : f a = 1) (hfx : (f x).IsSwap) :
    ∃ c : G, ∀ h ∈ Subgroup.closure ({a, x, u} : Set G),
      c * h * c⁻¹ ∈ SylowPreimageNormalizer.ambient f (ThreeSwapTwoGroup.subgroup e) P := by
  let H := Subgroup.closure ({a, x, u} : Set G)
  have hHp : IsPGroup 2 H := by
    apply (ThreeSwapTwoGroup.closure_two_group _ ?_ ?_).1
    · intro b hb c hc hbc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
      rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      all_goals first | exact Commute.refl _ | exact hax | exact hax.symm | exact hau | exact hau.symm | exact hxu | exact hxu.symm
    · intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl <;> assumption
  obtain ⟨d, hdx, hdu⟩ := SevenCommutingSwapInvolution.exists_conjugate hF e (f x) (f u)
    hfx (by rw [← map_pow, hu, map_one]) (hxu.map f)
  let j := (MulAut.conj d).toMonoidHom.comp f
  have hJ : H ≤ (ThreeSwapTwoGroup.subgroup e).comap j := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with hh | hh | hh
    · subst h
      change d * f a * d⁻¹ ∈ ThreeSwapTwoGroup.subgroup e
      rw [hfa, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · subst h
      exact hdx
    · subst h
      exact hdu
  obtain ⟨c, hc⟩ := PGroupConjugateIntoPreimageSylow.exists_conjugate f hf
    (ThreeSwapTwoGroup.subgroup e) P H hHp ⟨d, fun h => hJ h.property⟩
  exact ⟨c, fun h hh => hc ⟨h, hh⟩⟩

end FiveTransitive.CommutingTriplePreimageSylow

end CFSG

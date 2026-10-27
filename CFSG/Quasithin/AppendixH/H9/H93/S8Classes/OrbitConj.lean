module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Struct

public section

namespace CFSG.ASVolI.ChH

open Equiv

namespace E16Orbits

theorem orbit_map_conj (B : Subgroup (Perm (Fin 8))) (g : Perm (Fin 8)) (x : Fin 8) :
    MulAction.orbit (B.map (MulAut.conj g).toMonoidHom) (g x) = g '' MulAction.orbit B x := by
  ext y
  constructor
  · rintro ⟨⟨_, b, hb, rfl⟩, rfl⟩
    exact ⟨b x, ⟨⟨b, hb⟩, rfl⟩, by show g (b x) = (g * b * g⁻¹) (g x); simp⟩
  · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
    exact ⟨⟨_, b, hb, rfl⟩, by show (g * b * g⁻¹) (g x) = g (b x); simp⟩

theorem isElemAb2_map_conj {E : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E) (g : Perm (Fin 8)) :
    IsElemAb2 (E.map (MulAut.conj g).toMonoidHom) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem card_map_conj (E : Subgroup (Perm (Fin 8))) (g : Perm (Fin 8)) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem orbitSizesOf_conj (B : Subgroup (Perm (Fin 8))) (g : Perm (Fin 8)) :
    orbitSizesOf (B.map (MulAut.conj g).toMonoidHom) = orbitSizesOf B := by
  classical
  unfold orbitSizesOf
  have himg : (Finset.univ.image fun i : Fin 8 =>
        (MulAction.orbit (B.map (MulAut.conj g).toMonoidHom) i : Set (Fin 8))) =
      (Finset.univ.image fun i : Fin 8 => (MulAction.orbit B i : Set (Fin 8))).image
        (fun S => g '' S) := by
    ext S
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨MulAction.orbit B (g.symm i), ⟨g.symm i, rfl⟩, ?_⟩
      rw [← orbit_map_conj, Equiv.apply_symm_apply]
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨g j, orbit_map_conj B g j⟩
  rw [himg, Finset.image_val_of_injOn (Set.image_injective.2 g.injective).injOn,
    Multiset.map_map]
  refine Multiset.map_congr rfl fun S _ => ?_
  exact Set.ncard_image_of_injective S g.injective

theorem eq_of_orbit_eq {E E' : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E) (hc : Nat.card E = 16)
    (hE' : IsElemAb2 E') (hc' : Nat.card E' = 16)
    (h : ∀ x : Fin 8, MulAction.orbit E x = MulAction.orbit E' x) : E = E' := by
  ext σ
  rw [mem_e16_iff hE hc σ, mem_e16_iff hE' hc' σ]
  simp only [h]

theorem ncard_cycleType_map_conj (E : Subgroup (Perm (Fin 8))) (g : Perm (Fin 8))
    (c : Multiset ℕ) :
    Set.ncard {x : Perm (Fin 8) | x ∈ E.map (MulAut.conj g).toMonoidHom ∧ x.cycleType = c} =
      Set.ncard {x : Perm (Fin 8) | x ∈ E ∧ x.cycleType = c} := by
  have hs : {x : Perm (Fin 8) | x ∈ E.map (MulAut.conj g).toMonoidHom ∧ x.cycleType = c} =
      (MulAut.conj g).toMonoidHom '' {x | x ∈ E ∧ x.cycleType = c} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hc⟩
      exact ⟨y, ⟨hy, by simpa [MulAut.conj_apply, Equiv.Perm.cycleType_conj] using hc⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by simpa [MulAut.conj_apply, Equiv.Perm.cycleType_conj] using hc⟩
  rw [hs]
  exact Set.ncard_image_of_injective _ (MulAut.conj g).injective

theorem sign_conj_eq (g y : Perm (Fin 8)) : Perm.sign (g * y * g⁻¹) = Perm.sign y := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_right_comm, Int.units_mul_self, one_mul]

end E16Orbits

end CFSG.ASVolI.ChH

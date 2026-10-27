module

public import CFSG.Monster.GMS.BabyCover

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem orderOf_eq_of_babyOrbit {k : Fin 4} {r s : B} (h : BabyOrbit k r s) :
    orderOf (r * s) = ![2, 2, 3, 4] k := by
  match k, h with
  | 0, h => exact h.1
  | 1, h => exact h.1
  | 2, h => exact h
  | 3, h => exact h.1

theorem babyOrbit_unique {k j : Fin 4} {r s : B} (hk : BabyOrbit k r s) (hj : BabyOrbit j r s) :
    k = j := by
  have h2 := orderOf_eq_of_babyOrbit hj
  rw [orderOf_eq_of_babyOrbit hk] at h2
  match k, j with
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 2, 2 => rfl
  | 3, 3 => rfl
  | 0, 1 => exact absurd (BabyInv.unique hk hj) (by decide)
  | 1, 0 => exact absurd (BabyInv.unique hk hj) (by decide)
  | 0, 2 | 0, 3 | 1, 2 | 1, 3 | 2, 0 | 2, 1 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
    exact absurd h2 (by decide)

theorem babyTableIV_of_labels {H V : Type*} [Group H] (ρ : B ≃* H) (lab : V → H)
    (sph : Fin 4 → V → Set V) (b₂ b₄ : B) (hb₂ : BabyInv 1 b₂) (hb₄ : BabyInv 3 b₄)
    (hW₁ : ∀ t : B, BabyInv 0 t ↔ ∃ v, lab v = ρ t) (hinj : Function.Injective lab)
    (hcover : ∀ v u, u = v ∨ ∃ k, u ∈ sph k v)
    (htrans : ∀ k v u u', u ∈ sph k v → u' ∈ sph k v →
      ∃ s : H, s * lab v = lab v * s ∧ s⁻¹ * lab u * s = lab u')
    (hcard : ∀ k v, (sph k v).ncard = babyOrbitSize k)
    (h₀ : ∀ v u, u ∈ sph 0 v → IsConj (lab v * lab u) (ρ b₂))
    (h₁ : ∀ v u, u ∈ sph 1 v → IsConj (lab v * lab u) (ρ b₄))
    (h₂ : ∀ v u, u ∈ sph 2 v → orderOf (lab v * lab u) = 3)
    (h₃ : ∀ v u, u ∈ sph 3 v →
      orderOf (lab v * lab u) = 4 ∧ IsConj ((lab v * lab u) ^ 2) (ρ b₂)) :
    BabyTableIV := by
  have hconj : ∀ {k : Fin 4} {b : B} {x : H}, BabyInv k b → IsConj x (ρ b) →
      BabyInv k (ρ.symm x) := fun {k b x} hb hx => by
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    refine hb.of_isConj (isConj_iff.2 ⟨ρ.symm c⁻¹, ρ.injective ?_⟩)
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
    rw [← hc]
    group
  have hprod : ∀ k v u, u ∈ sph k v → BabyOrbit k (ρ.symm (lab v)) (ρ.symm (lab u)) := by
    intro k v u hu
    have hmul : ρ.symm (lab v) * ρ.symm (lab u) = ρ.symm (lab v * lab u) :=
      (map_mul ρ.symm _ _).symm
    match k, hu with
    | 0, hu =>
      rw [BabyOrbit, hmul]
      exact hconj hb₂ (h₀ v u hu)
    | 1, hu =>
      rw [BabyOrbit, hmul]
      exact hconj hb₄ (h₁ v u hu)
    | 2, hu =>
      rw [BabyOrbit, hmul, MulEquiv.orderOf_eq]
      exact h₂ v u hu
    | 3, hu =>
      rw [BabyOrbit, hmul, MulEquiv.orderOf_eq, ← map_pow ρ.symm]
      exact ⟨(h₃ v u hu).1, hconj hb₂ (h₃ v u hu).2⟩
  intro r hr
  obtain ⟨v, hv⟩ := (hW₁ r).1 hr
  have hr' : r = ρ.symm (lab v) := by rw [hv, MulEquiv.symm_apply_apply]
  subst hr'
  have hs : ∀ s : B, BabyInv 0 s → ∃ u, s = ρ.symm (lab u) := fun s hs0 => by
    obtain ⟨u, hu⟩ := (hW₁ s).1 hs0
    exact ⟨u, by rw [hu, MulEquiv.symm_apply_apply]⟩
  have hbi : ∀ u, BabyInv 0 (ρ.symm (lab u)) := fun u =>
    (hW₁ _).2 ⟨u, by rw [MulEquiv.apply_symm_apply]⟩
  have key : ∀ k u, BabyOrbit k (ρ.symm (lab v)) (ρ.symm (lab u)) ↔ u ∈ sph k v := by
    intro k u
    refine ⟨fun h => ?_, hprod k v u⟩
    rcases hcover v u with rfl | ⟨j, hj⟩
    · exact absurd h (not_babyOrbit_self hr)
    · exact (babyOrbit_unique h (hprod j v u hj)) ▸ hj
  refine ⟨fun s hs0 hsr => ?_, fun k s s' hs0 hs0' hk hk' => ?_, fun k => ?_⟩
  · obtain ⟨u, rfl⟩ := hs s hs0
    rcases hcover v u with rfl | ⟨k, hk⟩
    · exact absurd rfl hsr
    · exact ⟨k, (key k u).2 hk⟩
  · obtain ⟨u, rfl⟩ := hs s hs0
    obtain ⟨u', rfl⟩ := hs s' hs0'
    obtain ⟨h, hc, he⟩ := htrans k v u u' ((key k u).1 hk) ((key k u').1 hk')
    refine ⟨ρ.symm h⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg ρ.symm (Commute.inv_left (show Commute h (lab v) from hc)).eq
    · rw [← map_inv, ← map_mul, ← map_mul, inv_inv, he]
  · have himg : {s | BabyInv 0 s ∧ BabyOrbit k (ρ.symm (lab v)) s} =
        (fun u => ρ.symm (lab u)) '' sph k v := by
      ext s
      refine ⟨fun ⟨hs0, hk⟩ => ?_, ?_⟩
      · obtain ⟨u, rfl⟩ := hs s hs0
        exact ⟨u, (key k u).1 hk, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hbi u, (key k u).2 hu⟩
    rw [himg, Set.ncard_image_of_injective _ fun a b hab => hinj (ρ.symm.injective hab), hcard]

end CFSG.Monster.Existence

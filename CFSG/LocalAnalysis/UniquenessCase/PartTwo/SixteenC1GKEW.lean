module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G44Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 Subgroup

@[expose] def s16c1cE16Lin (E : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)) : Prop :=
  ∃ z : V₀, z ≠ 0 ∧ ∃ ℓ : V₀ →ₗ[ZMod 2] ZMod 2, ℓ ≠ 0 ∧
    (∀ u : V₀, (∀ e ∈ E, e u = u) ↔ (u = 0 ∨ u = z)) ∧
    (∀ e ∈ E, ∀ u : V₀, ℓ u = 0 → e u = u ∨ e u = u + z) ∧
    (∀ e ∈ E, e ≠ 1 → ∀ u : V₀, (e u = u ∨ e u = u + z) → ℓ u = 0) ∧
    (∀ u : V₀, ℓ u = 0 → u ∈ AddSubgroup.closure {u : V₀ | ∃ e ∈ E, e ≠ 1 ∧ e u = u}) ∧
    ∃ e ∈ E, ∃ u : V₀, ℓ u = 0 ∧ e u ≠ u

private def s16c1c_ellHom {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    (ℓ : V₀ →ₗ[ZMod 2] ZMod 2) : W →* Multiplicative (ZMod 2) :=
  (AddMonoidHom.toMultiplicative ℓ.toAddMonoidHom).comp β.toMonoidHom

private theorem s16c1c_ellHom_apply {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (ℓ : V₀ →ₗ[ZMod 2] ZMod 2) (w : W) :
    s16c1c_ellHom β ℓ w = Multiplicative.ofAdd (ℓ (Multiplicative.toAdd (β w))) := by
  simp [s16c1c_ellHom]

private theorem s16c1c_mem_ker_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (ℓ : V₀ →ₗ[ZMod 2] ZMod 2) (w : W) :
    w ∈ (s16c1c_ellHom β ℓ).ker ↔ ℓ (Multiplicative.toAdd (β w)) = 0 := by
  rw [MonoidHom.mem_ker, s16c1c_ellHom_apply, ofAdd_eq_one]

private theorem s16c1c_kappa_fix_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (x : V₀ ≃ₗ[ZMod 2] V₀) (w : W) :
    s16c1G_kappa β x w = w ↔
      x (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β w) := by
  constructor
  · intro h
    have h1 := congrArg (fun y => Multiplicative.toAdd (β y)) h
    rw [s16c1G_kappa_apply, toAdd_ofAdd] at h1
    exact h1
  · intro h
    apply β.injective
    rw [s16c1G_kappa_apply, h]
    exact ofAdd_toAdd (β w)

private theorem s16c1c_kappa_eq_mul_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (x : V₀ ≃ₗ[ZMod 2] V₀) (w : W) (z : V₀) :
    s16c1G_kappa β x w = w * β.symm (Multiplicative.ofAdd z) ↔
      x (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β w) + z := by
  constructor
  · intro h
    have h1 := congrArg (fun y => Multiplicative.toAdd (β y)) h
    rw [s16c1G_kappa_apply, map_mul, MulEquiv.apply_symm_apply, toAdd_ofAdd,
      toAdd_mul, toAdd_ofAdd] at h1
    exact h1
  · intro h
    apply β.injective
    rw [s16c1G_kappa_apply, map_mul, MulEquiv.apply_symm_apply, h, ofAdd_add,
      ofAdd_toAdd (β w)]

private theorem s16c1c_kappa_or_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (x : V₀ ≃ₗ[ZMod 2] V₀) (w : W) (z : V₀) :
    (s16c1G_kappa β x w = w ∨
        s16c1G_kappa β x w = w * β.symm (Multiplicative.ofAdd z)) ↔
      (x (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β w) ∨
        x (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (β w) + z) :=
  or_congr (s16c1c_kappa_fix_iff β x w) (s16c1c_kappa_eq_mul_iff β x w z)

private theorem s16c1c_kappa_ne_one_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (x : V₀ ≃ₗ[ZMod 2] V₀) :
    s16c1G_kappa β x ≠ 1 ↔ x ≠ 1 := by
  constructor
  · intro h hx
    exact h (by rw [hx, map_one])
  · intro h hk
    exact h (s16c1G_kappa_injective β (by rw [hk, map_one]))

private theorem s16c1c_toAdd_eq_zero_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (w : W) :
    Multiplicative.toAdd (β w) = 0 ↔ w = 1 := by
  rw [toAdd_eq_zero]
  exact MulEquiv.map_eq_one_iff β

private theorem s16c1c_toAdd_eq_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (w : W) (z : V₀) :
    Multiplicative.toAdd (β w) = z ↔ w = β.symm (Multiplicative.ofAdd z) := by
  rw [← Multiplicative.ofAdd.injective.eq_iff, ofAdd_toAdd]
  exact (MulEquiv.eq_symm_apply β).symm

private theorem s16c1c_forall_mem_iff {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) {E : Subgroup (MulAut W)} (φ : MulAut W → Prop) :
    (∀ e ∈ E, φ e) ↔ ∀ x ∈ E.comap (s16c1G_kappa β), φ (s16c1G_kappa β x) := by
  constructor
  · intro h x hx
    exact h _ hx
  · intro h e he
    obtain ⟨x, rfl⟩ := s16c1G44_kappa_surjective β e
    exact h x he

private theorem s16c1c_closure_transport {W : Type} [CommGroup W]
    (β : W ≃* Multiplicative V₀) (E : Subgroup (MulAut W)) (u : V₀)
    (hu : u ∈ AddSubgroup.closure {v : V₀ | ∃ x ∈ E.comap (s16c1G_kappa β),
      x ≠ 1 ∧ x v = v}) :
    β.symm (Multiplicative.ofAdd u) ∈
      Subgroup.closure {w : W | ∃ e ∈ E, e ≠ 1 ∧ e w = w} := by
  refine AddSubgroup.closure_induction (p := fun u _ =>
      β.symm (Multiplicative.ofAdd u) ∈
        Subgroup.closure {w : W | ∃ e ∈ E, e ≠ 1 ∧ e w = w}) ?_ ?_ ?_ ?_ hu
  · intro v hv
    obtain ⟨x, hx, hx1, hxv⟩ := hv
    refine Subgroup.subset_closure ⟨s16c1G_kappa β x, hx, ?_, ?_⟩
    · intro hk
      exact hx1 (s16c1G_kappa_injective β (by rw [hk, map_one]))
    · rw [s16c1c_kappa_fix_iff]
      simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using hxv
  · rw [ofAdd_zero, map_one]
    exact Subgroup.one_mem _
  · intro a b _ _ iha ihb
    rw [ofAdd_add, map_mul]
    exact Subgroup.mul_mem _ iha ihb
  · intro a _ iha
    rw [ofAdd_neg, map_inv]
    exact Subgroup.inv_mem _ iha

theorem s16c1c_e16_transport {W : Type} [CommGroup W] (β : W ≃* Multiplicative V₀)
    {E : Subgroup (MulAut W)} (hE : s16c1cE16Lin (E.comap (s16c1G_kappa β))) :
    ∃ z : W, z ≠ 1 ∧ ∃ P : Subgroup W, P.index = 2 ∧
      (∀ w : W, (∀ e ∈ E, e w = w) ↔ (w = 1 ∨ w = z)) ∧
      (∀ e ∈ E, ∀ w ∈ P, e w = w ∨ e w = w * z) ∧
      (∀ e ∈ E, e ≠ 1 → ∀ w : W, (e w = w ∨ e w = w * z) → w ∈ P) ∧
      P ≤ Subgroup.closure {w : W | ∃ e ∈ E, e ≠ 1 ∧ e w = w} ∧
      ∃ e ∈ E, ∃ w ∈ P, e w ≠ w := by
  obtain ⟨z, hz, ℓ, hℓ, hE1, hE2, hE3, hE4, hE5⟩ := hE
  set zW : W := β.symm (Multiplicative.ofAdd z) with hzW
  set P : Subgroup W := (s16c1c_ellHom β ℓ).ker with hP
  have hsurj : Function.Surjective (s16c1c_ellHom β ℓ) := by
    obtain ⟨u₀, hu₀1⟩ : ∃ u₀ : V₀, ℓ u₀ = 1 := by
      obtain ⟨u₀, hu₀⟩ : ∃ u : V₀, ℓ u ≠ 0 := by
        by_contra h
        exact hℓ (LinearMap.ext fun u => by
          simpa using not_not.mp (not_exists.mp h u))
      rcases zmod2_eq_zero_or_eq_one (ℓ u₀) with h | h
      · exact absurd h hu₀
      · exact ⟨u₀, h⟩
    intro y
    rcases zmod2_eq_zero_or_eq_one (Multiplicative.toAdd y) with h | h
    · refine ⟨1, ?_⟩
      rw [map_one, ← ofAdd_toAdd y, h]
      rfl
    · refine ⟨β.symm (Multiplicative.ofAdd u₀), ?_⟩
      rw [s16c1c_ellHom_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd, hu₀1,
        ← ofAdd_toAdd y, h]
  refine ⟨zW, ?_, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hzW]
    intro h
    apply hz
    have h1 := congrArg β h
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    exact ofAdd_eq_one.mp h1
  · rw [hP, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj,
      Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  · intro w
    rw [s16c1c_forall_mem_iff β (fun e => e w = w)]
    simp only [s16c1c_kappa_fix_iff]
    rw [hE1 (Multiplicative.toAdd (β w)), hzW]
    simp only [s16c1c_toAdd_eq_zero_iff β w, s16c1c_toAdd_eq_iff β w z]
  · rw [s16c1c_forall_mem_iff β (fun e => ∀ w ∈ P, e w = w ∨ e w = w * zW)]
    intro x hx w hw
    rw [hP] at hw
    have hℓu : ℓ (Multiplicative.toAdd (β w)) = 0 := (s16c1c_mem_ker_iff β ℓ w).mp hw
    rw [hzW, s16c1c_kappa_or_iff β x w z]
    exact hE2 x hx (Multiplicative.toAdd (β w)) hℓu
  · rw [s16c1c_forall_mem_iff β (fun e => e ≠ 1 → ∀ w : W,
        (e w = w ∨ e w = w * zW) → w ∈ P)]
    intro x hx hx1 w hw
    rw [s16c1c_kappa_ne_one_iff β x] at hx1
    rw [hzW] at hw
    rw [s16c1c_kappa_or_iff β x w z] at hw
    have hℓu : ℓ (Multiplicative.toAdd (β w)) = 0 :=
      hE3 x hx hx1 (Multiplicative.toAdd (β w)) hw
    rw [hP]
    exact (s16c1c_mem_ker_iff β ℓ w).mpr hℓu
  · intro w hw
    rw [hP] at hw
    have hℓu : ℓ (Multiplicative.toAdd (β w)) = 0 := (s16c1c_mem_ker_iff β ℓ w).mp hw
    have hmem := hE4 (Multiplicative.toAdd (β w)) hℓu
    have hcl := s16c1c_closure_transport β E (Multiplicative.toAdd (β w)) hmem
    simpa only [ofAdd_toAdd, MulEquiv.symm_apply_apply] using hcl
  · obtain ⟨x, hx, u, hℓu, hxu⟩ := hE5
    refine ⟨s16c1G_kappa β x, hx, β.symm (Multiplicative.ofAdd u), ?_, ?_⟩
    · rw [hP]
      exact (s16c1c_mem_ker_iff β ℓ _).mpr (by
        simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using hℓu)
    · intro h
      refine hxu ?_
      have h' := (s16c1c_kappa_fix_iff β x (β.symm (Multiplicative.ofAdd u))).mp h
      simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using h'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

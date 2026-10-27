module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {X : Type*} [Group X]

@[expose] def ItemC (p : ℕ) (f : MulAut X) : Prop :=
  IsPGroup p (fixingSubgroup (MulAut X) (signalizerFixedSubgroup f : Set X))

@[expose] def ItemG (p : ℕ) (f : MulAut X) : Prop :=
  ∀ g : MulAut X, Nat.Coprime p (orderOf g) →
    (∀ m ∈ fixedNormalizer f, g m ∈ fixedNormalizer f) →
    (∀ m ∈ fixedNormalizer f, m⁻¹ * g m ∈ CFSG.fittingSubgroupOf (fixedNormalizer f)) →
    ∃ m ∈ fixedNormalizer f, g = MulAut.conj m

@[expose] def ItemO (f : MulAut X) : Prop :=
  (∃ r : ℕ, r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer f)) ∧
    ∀ r : ℕ, r.Prime → r ∣ Nat.card X → ¬ r ∣ Nat.card (fixedNormalizer f) →
      ∀ R : Sylow r X, IsMulCommutative (R : Subgroup X)

section Transport

variable {p : ℕ}

theorem ItemC.of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f') (h : ItemC p f') :
    ItemC p f := by
  unfold ItemC at h ⊢
  rw [hC]
  exact h

theorem ItemG.of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f') (h : ItemG p f') :
    ItemG p f := by
  unfold ItemG at h ⊢
  rw [fixedNormalizer_eq_of_fixed_eq hC]
  exact h

theorem ItemO.of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f') (h : ItemO f') :
    ItemO f := by
  unfold ItemO at h ⊢
  rw [fixedNormalizer_eq_of_fixed_eq hC]
  exact h

theorem ItemC.of_congr {Y : Type*} [Group Y] (e : X ≃* Y) {f : MulAut X}
    (h : ItemC p (MulAut.congr e f)) : ItemC p f := by
  unfold ItemC at h ⊢
  rw [signalizerFixedSubgroup_congr] at h
  have hle : (fixingSubgroup (MulAut X) (signalizerFixedSubgroup f : Set X)).map
      (MulAut.congr e).toMonoidHom ≤ fixingSubgroup (MulAut Y)
        (((signalizerFixedSubgroup f).map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hg' := (mem_fixingSubgroup_iff (MulAut X)).mp hg (e.symm y)
      (by simpa using Subgroup.mem_map_equiv.mp hy)
    rw [MulAut.smul_def] at hg' ⊢
    change e (g (e.symm y)) = y
    simp [hg']
  exact isPGroup_of_map_equiv (MulAut.congr e) (h.to_le hle)

theorem ItemG.of_congr {Y : Type*} [Group Y] (e : X ≃* Y) {f : MulAut X}
    (h : ItemG p (MulAut.congr e f)) : ItemG p f := by
  intro g hg hgM hgF
  have hM := fixedNormalizer_congr e f
  have hFM := fittingSubgroupOf_map_equiv e (fixedNormalizer f)
  have h1 : ∀ m ∈ fixedNormalizer (MulAut.congr e f),
      (MulAut.congr e g) m ∈ fixedNormalizer (MulAut.congr e f) := by
    intro m' hm'
    rw [hM] at hm' ⊢
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hm'
    have : (MulAut.congr e g) (e.toMonoidHom m) = e.toMonoidHom (g m) := by simp
    rw [this]
    exact Subgroup.mem_map_of_mem _ (hgM m hm)
  have h2 : ∀ m ∈ fixedNormalizer (MulAut.congr e f),
      m⁻¹ * (MulAut.congr e g) m ∈ CFSG.fittingSubgroupOf (fixedNormalizer (MulAut.congr e f)) := by
    intro m' hm'
    rw [hM] at hm'
    rw [hM, hFM]
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hm'
    have : (e.toMonoidHom m)⁻¹ * (MulAut.congr e g) (e.toMonoidHom m) =
        e.toMonoidHom (m⁻¹ * g m) := by simp
    rw [this]
    exact Subgroup.mem_map_of_mem _ (hgF m hm)
  obtain ⟨m', hm', hgm'⟩ := h (MulAut.congr e g) (by rwa [orderOf_congr]) h1 h2
  rw [hM] at hm'
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hm'
  refine ⟨m, hm, (MulAut.congr e).injective ?_⟩
  rw [hgm']
  ext y
  simp

theorem ItemO.of_congr {Y : Type*} [Group Y] [Finite X] [Finite Y] (e : X ≃* Y) {f : MulAut X}
    (h : ItemO (MulAut.congr e f)) : ItemO f := by
  have hcard : Nat.card (fixedNormalizer (MulAut.congr e f)) = Nat.card (fixedNormalizer f) := by
    rw [fixedNormalizer_congr, Subgroup.card_map_of_injective e.injective]
  have hX : Nat.card Y = Nat.card X := (Nat.card_congr e.toEquiv).symm
  unfold ItemO at h ⊢
  rw [hcard, hX] at h
  refine ⟨h.1, fun r hr hrX hrM R => ?_⟩
  have := Fact.mk hr
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have h2 : IsMulCommutative ((R.mapSurjective hsurj : Sylow r Y) : Subgroup Y) :=
    h.2 r hr hrX hrM _
  rw [Sylow.coe_mapSurjective] at h2
  exact isMulCommutative_of_map_equiv e h2

end Transport

end CFSG.SignalizerFunctorTheorem.McBride

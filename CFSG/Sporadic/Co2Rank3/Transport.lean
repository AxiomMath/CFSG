module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Sporadic.Co2Rank3

open MulAction

theorem exists_equiv_of_stabilizers {K L X Y ι : Type*} [Group K] [Group L] [MulAction K X]
    [MulAction L Y] [Finite X] (φ : K ≃* L) (z : ι → Y) (q : ι → X)
    (hcov : ∀ y : Y, ∃ i, ∃ l : L, l • z i = y)
    (hlen : ∀ i j, (orbit L (z i)).ncard = (orbit L (z j)).ncard → i = j)
    (hstab : ∀ i (k : K), k • q i = q i ↔ φ k • z i = z i)
    (hcard : Nat.card Y = Nat.card X) :
    ∃ Θ : Y ≃ X, (∀ i, Θ (z i) = q i) ∧ ∀ (k : K) (y : Y), Θ (φ k • y) = k • Θ y := by
  classical
  choose idx l hl using hcov
  let Θ₀ : Y → X := fun y => φ.symm (l y) • q (idx y)
  have hlenX : ∀ i, (orbit K (q i)).ncard = (orbit L (z i)).ncard := by
    intro i
    rw [← index_stabilizer, ← index_stabilizer]
    have : stabilizer K (q i) = (stabilizer L (z i)).comap φ.toMonoidHom := by
      ext k
      rw [mem_stabilizer_iff, Subgroup.mem_comap, mem_stabilizer_iff]
      exact hstab i k
    rw [this, Subgroup.index_comap_of_surjective _ φ.surjective]
  have hfix : ∀ i (m : L), m • z i = z i → φ.symm m • q i = q i := fun i m hm =>
    (hstab i (φ.symm m)).2 (by rw [MulEquiv.apply_symm_apply]; exact hm)
  have hwd : ∀ i (m : L), Θ₀ (m • z i) = φ.symm m • q i := by
    intro i m
    obtain ⟨y, hy⟩ : ∃ y, m • z i = y := ⟨_, rfl⟩
    rw [hy]
    have h1 := hl y
    have horb : z (idx y) ∈ orbit L (z i) :=
      mem_orbit_iff.2 ⟨(l y)⁻¹ * m, by rw [mul_smul, hy, inv_smul_eq_iff]; exact h1.symm⟩
    have hi : idx y = i := hlen _ _ (by rw [orbit_eq_iff.2 horb])
    change φ.symm (l y) • q (idx y) = φ.symm m • q i
    rw [hi] at h1 ⊢
    have h2 : (m⁻¹ * l y) • z i = z i := by rw [mul_smul, h1, ← hy, inv_smul_smul]
    have h3 := hfix i _ h2
    rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff] at h3
    exact h3
  have hz : ∀ i, Θ₀ (z i) = q i := fun i => by
    have := hwd i 1
    rwa [one_smul, map_one, one_smul] at this
  have hequiv : ∀ (k : K) (y : Y), Θ₀ (φ k • y) = k • Θ₀ y := by
    intro k y
    conv_lhs => rw [← hl y, ← mul_smul]
    rw [hwd, map_mul, MulEquiv.symm_apply_apply, mul_smul]
  have hinj : Function.Injective Θ₀ := by
    intro y y' h
    change φ.symm (l y) • q (idx y) = φ.symm (l y') • q (idx y') at h
    have hq : q (idx y') ∈ orbit K (q (idx y)) :=
      mem_orbit_iff.2 ⟨(φ.symm (l y'))⁻¹ * φ.symm (l y), by rw [mul_smul, h, inv_smul_smul]⟩
    have hi : idx y = idx y' := hlen _ _ (by rw [← hlenX, ← hlenX, orbit_eq_iff.2 hq])
    rw [← hl y, ← hl y']
    rw [← hi] at h ⊢
    have h2 : (φ.symm ((l y')⁻¹ * l y)) • q (idx y) = q (idx y) := by
      rw [map_mul, map_inv, mul_smul, h, inv_smul_smul]
    have h3 := (hstab (idx y) _).1 h2
    rw [MulEquiv.apply_symm_apply, mul_smul, inv_smul_eq_iff] at h3
    exact h3
  have hbij : Function.Bijective Θ₀ := (Nat.bijective_iff_injective_and_card Θ₀).2 ⟨hinj, hcard⟩
  exact ⟨Equiv.ofBijective Θ₀ hbij, hz, hequiv⟩

end CFSG.Sporadic.Co2Rank3

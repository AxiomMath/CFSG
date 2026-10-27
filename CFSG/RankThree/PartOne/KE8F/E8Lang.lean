module

public import CFSG.RankThree.PartOne.KE8F.E8Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


section Descent

theorem fixed_pgroup_le_range (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (P : Subgroup (ModGL .E8 L)) [Finite P]
    (hPC : P ≤ adjointGroup .E8 L)
    (hPF : ∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x)
    (hPp : IsPGroup p P) : P ≤ (adjEmb .E8 K L).range := by
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) (iterateFrobenius L ℓ f) hFr P hPC hPF).2.1 p hp hp3 P le_rfl hPp
  rwa [adjEmb_range]

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem exists_hom_to_C (D : E8P4Frame0 K L ℓ f) {M : Type} [Group M] [Finite M]
    (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤) (e : M →* ModGL .E8 L)
    (hadj : ∀ m, e m ∈ adjointGroup .E8 L)
    (hfix : ∀ m, D.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (e m) * D.n⁻¹ = e m) :
    ∃ ι : M →* adjointGroup .E8 K, ∀ m, adjEmb .E8 K L (ι m) = D.g0 * e m * D.g0⁻¹ := by
  classical
  set Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom (iterateFrobenius L ℓ f))
    with hΦ
  let e' : M →* ModGL .E8 L := (MulAut.conj D.g0).toMonoidHom.comp e
  have he' : ∀ m, e' m = D.g0 * e m * D.g0⁻¹ := fun m => by
    simp [e', MulAut.conj_apply]
  have hP'fin : Finite e'.range :=
    Finite.of_surjective e'.rangeRestrict e'.rangeRestrict_surjective
  have hP'adj : e'.range ≤ adjointGroup .E8 L := by
    rintro _ ⟨m, rfl⟩
    rw [he']
    exact mul_mem (mul_mem D.hg0C (hadj m)) (inv_mem D.hg0C)
  have hP'fix : ∀ x ∈ e'.range, Φ x = x := by
    rintro _ ⟨m, rfl⟩
    rw [he', map_mul, map_mul, map_inv, D.hg0]
    calc D.g0 * D.n * Φ (e m) * (D.g0 * D.n)⁻¹ = D.g0 * (D.n * Φ (e m) * D.n⁻¹) * D.g0⁻¹ := by
          group
      _ = D.g0 * e m * D.g0⁻¹ := by rw [hfix m]
  have hP'perf : ⁅e'.range, e'.range⁆ = e'.range := by
    have h1 : e'.range = (⊤ : Subgroup M).map e' := MonoidHom.range_eq_map e'
    rw [h1, ← Subgroup.map_commutator, hM]
  have hle := D.hperf e'.range hP'fin hP'adj hP'fix hP'perf
  have hmem : ∀ m, e' m ∈ (adjEmb .E8 K L).range := fun m => hle ⟨m, rfl⟩
  let ι₀ : M →* (adjEmb .E8 K L).range := e'.codRestrict _ hmem
  refine ⟨((MonoidHom.ofInjective (adjEmb_injective (τ := .E8) (K := K) (L := L))).symm :
    (adjEmb .E8 K L).range ≃* adjointGroup .E8 K).toMonoidHom.comp ι₀, fun m => ?_⟩
  have h := (MonoidHom.ofInjective (adjEmb_injective (τ := .E8) (K := K) (L := L))).apply_symm_apply
    (ι₀ m)
  have h2 := congrArg Subtype.val h
  rw [MonoidHom.ofInjective_apply] at h2
  rw [← he']
  exact h2

end Descent

end CFSG.RankThree.PartOne.KE8F

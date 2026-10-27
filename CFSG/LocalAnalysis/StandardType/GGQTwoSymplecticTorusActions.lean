module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticPlaneActions
public import CFSG.LinearAlgebra.CubeRootBlock
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.SymplecticPilot (permSp)
open CFSG.StandardType.WitSpNs
open CFSG.LieType.Chevalley (WSL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem WSL_conj_pow_val (hK : Nat.card K = 2)
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    (a : Multiplicative (ZMod 3)) :
    (WSL : Matrix.SpecialLinearGroup (Fin 2) K) *
        mkSL M hdet ^ (Multiplicative.toAdd a).val * WSL⁻¹ =
      mkSL M hdet ^ (Multiplicative.toAdd a⁻¹).val := by
  let T : Matrix.SpecialLinearGroup (Fin 2) K := mkSL M hdet
  have h3 : T ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, coe_mkSL]
    exact SymplecticPlaneActions.pow_three_eq_one_of_sq_add_self_add_one hM
  have hflip : (WSL : Matrix.SpecialLinearGroup (Fin 2) K) * T * WSL⁻¹ = T⁻¹ :=
    SymplecticPlaneActions.WSL_conj_mkSL_eq_inv hK hdet hM
  change WSL * T ^ (Multiplicative.toAdd a).val * WSL⁻¹ =
    T ^ (Multiplicative.toAdd a⁻¹).val
  calc WSL * T ^ (Multiplicative.toAdd a).val * WSL⁻¹ =
      (WSL * T * WSL⁻¹) ^ (Multiplicative.toAdd a).val := by
        exact map_pow (MulAut.conj (WSL : Matrix.SpecialLinearGroup (Fin 2) K))
          T (Multiplicative.toAdd a).val
    _ = (T⁻¹) ^ (Multiplicative.toAdd a).val := by rw [hflip]
    _ = (T ^ (Multiplicative.toAdd a).val)⁻¹ := inv_pow T _
    _ = T ^ (Multiplicative.toAdd a⁻¹).val :=
        ((CFSG.LinearAlgebra.cubePowHom T h3).map_inv a).symm

theorem exists_conj_longBlock_of_full_frame
    (hK : Nat.card K = 2) {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (i : Fin n) (g : ↥E) :
    ∃ g' : ↥E, (∀ j, k j g' = if j = i then (k j g)⁻¹ else k j g) ∧
      (A₀ * longBlock K n i WSL * A₀⁻¹) * g *
        (A₀ * longBlock K n i WSL * A₀⁻¹)⁻¹ = g' := by
  classical
  obtain ⟨g', hg'⟩ := hsurj (fun j => if j = i then (k j g)⁻¹ else k j g)
  refine ⟨g', hg', ?_⟩
  apply (MulAut.conj A₀⁻¹).injective
  apply mat_injective
  change mat n K (A₀⁻¹ * ((A₀ * longBlock K n i WSL * A₀⁻¹) * g *
    (A₀ * longBlock K n i WSL * A₀⁻¹)⁻¹) * A₀) = mat n K (A₀⁻¹ * g' * A₀)
  rw [show A₀⁻¹ * ((A₀ * longBlock K n i WSL * A₀⁻¹) * (g : StatedSp n K) *
      (A₀ * longBlock K n i WSL * A₀⁻¹)⁻¹) * A₀ =
      longBlock K n i WSL * (A₀⁻¹ * g * A₀) * (longBlock K n i WSL)⁻¹ by group]
  rw [SymplecticPlaneActions.mat_longBlock_conj_planeMat (hframe g), hframe g']
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl, hg', if_pos rfl]
    have h := congrArg (fun T : Matrix.SpecialLinearGroup (Fin 2) K =>
      (T : Matrix (Fin 2) (Fin 2) K)) (WSL_conj_pow_val hK hdet hM (k i g))
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_mkSL] using h
  · rw [if_neg hji, hg', if_neg hji]

theorem exists_conj_permSp_of_full_frame
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (π : Equiv.Perm (Fin n)) (g : ↥E) :
    ∃ g' : ↥E, (∀ j, k j g' = k (π.symm j) g) ∧
      (A₀ * permSp K π * A₀⁻¹) * g * (A₀ * permSp K π * A₀⁻¹)⁻¹ = g' := by
  obtain ⟨g', hg'⟩ := hsurj (fun j => k (π.symm j) g)
  refine ⟨g', hg', ?_⟩
  apply (MulAut.conj A₀⁻¹).injective
  apply mat_injective
  change mat n K (A₀⁻¹ * ((A₀ * permSp K π * A₀⁻¹) * g *
    (A₀ * permSp K π * A₀⁻¹)⁻¹) * A₀) = mat n K (A₀⁻¹ * g' * A₀)
  rw [show A₀⁻¹ * ((A₀ * permSp K π * A₀⁻¹) * (g : StatedSp n K) *
      (A₀ * permSp K π * A₀⁻¹)⁻¹) * A₀ =
      permSp K π * (A₀⁻¹ * g * A₀) * (permSp K π)⁻¹ by group]
  rw [SymplecticPlaneActions.mat_permSp_conj_planeMat (hframe g), hframe g']
  congr 1
  funext j
  rw [hg']

theorem longBlock_mem_normalizer_of_full_frame
    (hK : Nat.card K = 2) {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) (hM : M * M + M + 1 = 0)
    {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (i : Fin n) :
    A₀ * longBlock K n i WSL * A₀⁻¹ ∈ Subgroup.normalizer (E : Set (StatedSp n K)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨g', -, h⟩ := exists_conj_longBlock_of_full_frame hK hdet hM hframe hsurj i ⟨g, hg⟩
  rw [h]
  exact g'.property

theorem permSp_mem_normalizer_of_full_frame
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (π : Equiv.Perm (Fin n)) :
    A₀ * permSp K π * A₀⁻¹ ∈ Subgroup.normalizer (E : Set (StatedSp n K)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨g', -, h⟩ := exists_conj_permSp_of_full_frame hframe hsurj π ⟨g, hg⟩
  rw [h]
  exact g'.property


theorem eq_one_of_permSp_frame_centralizes
    {E : Subgroup (StatedSp n K)} {A₀ : StatedSp n K}
    {M : Matrix (Fin 2) (Fin 2) K} {k : Fin n → ↥E →* Multiplicative (ZMod 3)}
    (hframe : ∀ g : ↥E, mat n K (A₀⁻¹ * g * A₀) =
      planeMat (fun j => M ^ (Multiplicative.toAdd (k j g)).val))
    (hsurj : ∀ v : Fin n → Multiplicative (ZMod 3), ∃ g : ↥E, ∀ j, k j g = v j)
    (π : Equiv.Perm (Fin n))
    (hcen : ∀ g ∈ E, (A₀ * permSp K π * A₀⁻¹) * g *
      (A₀ * permSp K π * A₀⁻¹)⁻¹ = g) : π = 1 := by
  classical
  apply Equiv.ext
  intro i
  have hinv : π.symm i = i := by
    by_contra hne
    let α : Multiplicative (ZMod 3) := Multiplicative.ofAdd (1 : ZMod 3)
    obtain ⟨g, hg⟩ := hsurj (fun j => if j = i then α else 1)
    obtain ⟨g', hg', heq⟩ := exists_conj_permSp_of_full_frame hframe hsurj π g
    have hgg : g' = g := Subtype.ext (heq.symm.trans (hcen g g.property))
    have h1 : k i g = α := by simpa using hg i
    have h2 : k (π.symm i) g = 1 := by simpa only [if_neg hne] using hg (π.symm i)
    have h := hg' i
    rw [hgg, h1, h2] at h
    exact (show α ≠ 1 by decide +kernel) h
  have h := congrArg π hinv
  rw [π.apply_symm_apply] at h
  exact h.symm.trans (Equiv.Perm.one_apply i).symm

end CFSG.StandardType.QTwoSymplecticCav

end

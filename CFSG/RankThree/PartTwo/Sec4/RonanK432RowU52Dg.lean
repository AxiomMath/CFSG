module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVTorus
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434KitWreath

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Assembly.RankThreeEven (projSU)

abbrev U52Field : Type := GaloisField 2 (2 * 1)

@[expose] noncomputable def u52Zeta (ω : U52Fieldˣ) (a : ZMod 3) : U52Fieldˣ := ω ^ a.val

section Zeta

variable {ω : U52Fieldˣ}

theorem zeta_add (h3 : ω ^ 3 = 1) (a b : ZMod 3) : u52Zeta ω (a + b) = u52Zeta ω a * u52Zeta ω b :=
  CFSG.RankThree.PartTwo.Sec4.Item434Kit.pow_val_add h3 a b

theorem zeta_zero : u52Zeta ω 0 = 1 := by
  simp [u52Zeta]

theorem zeta_pow_three (h3 : ω ^ 3 = 1) (a : ZMod 3) : u52Zeta ω a ^ 3 = 1 := by
  unfold u52Zeta
  rw [← pow_mul, mul_comm a.val 3, pow_mul, h3, one_pow]

theorem zeta_injective (hω : orderOf ω = 3) : Function.Injective (u52Zeta ω) := by
  intro a b hab
  have h1 : ω ^ a.val = ω ^ b.val := hab
  rw [pow_inj_mod, hω, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h1
  exact ZMod.val_injective 3 h1

theorem zeta_prod_fin5 (h3 : ω ^ 3 = 1) (β : Fin 5 → ZMod 3) :
    ∏ j, u52Zeta ω (β j) = u52Zeta ω (∑ j, β j) := by
  simp only [Fin.prod_univ_five, Fin.sum_univ_five, zeta_add h3]

end Zeta

@[expose] noncomputable def dg (ω : U52Fieldˣ) (β : Fin 5 → ZMod 3) : GL (Fin 5) U52Field :=
  diagHom (fun j => u52Zeta ω (β j))

section Dg

variable {ω : U52Fieldˣ}

theorem dg_apply (β : Fin 5 → ZMod 3) :
    ((dg ω β : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field) =
      diagonal (fun j => ((u52Zeta ω (β j) : U52Fieldˣ) : U52Field)) :=
  rfl

theorem dg_mul (h3 : ω ^ 3 = 1) (β γ : Fin 5 → ZMod 3) :
    dg ω (β + γ) = dg ω β * dg ω γ := by
  unfold dg
  rw [← map_mul]
  congr 1
  funext j
  exact zeta_add h3 (β j) (γ j)

theorem dg_zero : dg ω 0 = 1 := by
  unfold dg
  have h : (fun j => u52Zeta ω ((0 : Fin 5 → ZMod 3) j)) = 1 := by
    funext j
    simp [zeta_zero]
  rw [h, map_one]

@[expose] noncomputable def dgHom (h3 : ω ^ 3 = 1) : Multiplicative (Fin 5 → ZMod 3) →* GL (Fin 5) U52Field where
  toFun x := dg ω (Multiplicative.toAdd x)
  map_one' := dg_zero
  map_mul' x y := dg_mul h3 _ _

theorem dg_zpow (h3 : ω ^ 3 = 1) (β : Fin 5 → ZMod 3) (k : ℤ) :
    dg ω β ^ k = dg ω (k • β) := by
  have h := map_zpow (dgHom h3) (Multiplicative.ofAdd β) k
  rw [← ofAdd_zsmul] at h
  exact h.symm

end Dg

@[expose] noncomputable def pg : Equiv.Perm (Fin 5) →* GL (Fin 5) U52Field :=
  (permMatrixHom : Equiv.Perm (Fin 5) →* Matrix (Fin 5) (Fin 5) U52Field).toHomUnits

theorem pg_apply (σ : Equiv.Perm (Fin 5)) (i j : Fin 5) :
    ((pg σ : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field) i j =
      if σ⁻¹ i = j then 1 else 0 := by
  simp [pg, permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]

theorem permMatrix_mul_diagonal_mul (τ : Equiv.Perm (Fin 5)) (d : Fin 5 → U52Field) :
    (τ.permMatrix U52Field) * diagonal d * (τ⁻¹.permMatrix U52Field) =
      diagonal (fun i => d (τ i)) := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ i)]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.mul_diagonal,
      Matrix.diagonal_apply]
  · intro k _ hk
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.mul_diagonal,
      Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

section Pg

variable {ω : U52Fieldˣ}

theorem pg_mul_dg_mul_inv (σ : Equiv.Perm (Fin 5)) (β : Fin 5 → ZMod 3) :
    pg σ * dg ω β * (pg σ)⁻¹ = dg ω (fun j => β (σ⁻¹ j)) := by
  rw [← map_inv pg σ]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, dg_apply]
  exact permMatrix_mul_diagonal_mul σ⁻¹ (fun j => ((u52Zeta ω (β j) : U52Fieldˣ) : U52Field))

theorem mk_pg_mul_dg_mul_inv (σ : Equiv.Perm (Fin 5)) (β : Fin 5 → ZMod 3) :
    (ProjGenLinGroup.mk (pg σ) : ProjGenLinGroup (Fin 5) U52Field) *
        ProjGenLinGroup.mk (dg ω β) * (ProjGenLinGroup.mk (pg σ))⁻¹ =
      ProjGenLinGroup.mk (dg ω (fun j => β (σ⁻¹ j))) := by
  rw [← map_inv ProjGenLinGroup.mk (pg σ), ← map_mul, ← map_mul, pg_mul_dg_mul_inv]

theorem sign_cast_eq_one (τ : Equiv.Perm (Fin 5)) :
    (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : U52Field) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · rw [h]
    simp
  · rw [h]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    exact CharTwo.neg_eq 1

theorem pg_transpose_mul (σ : Equiv.Perm (Fin 5)) :
    ((pg σ : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field)ᵀ *
      ((pg σ : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field) = 1 := by
  have h : (permMatrixHom σ⁻¹ : Matrix (Fin 5) (Fin 5) U52Field) * permMatrixHom σ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  change ((σ⁻¹).permMatrix U52Field)ᵀ * (σ⁻¹).permMatrix U52Field = 1
  rw [Matrix.transpose_permMatrix, inv_inv]
  simpa [permMatrixHom_apply, inv_inv] using h

theorem mk_pg_mem (σ : Equiv.Perm (Fin 5)) :
    (ProjGenLinGroup.mk (pg σ) : ProjGenLinGroup (Fin 5) U52Field) ∈ projSU 5 2 1 := by
  unfold projSU CFSG.PGLModel.projImage
  refine Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨?_, ?_⟩)
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    change Matrix.det ((σ⁻¹).permMatrix U52Field) = 1
    rw [Matrix.det_permutation]
    exact sign_cast_eq_one _
  · have hmap : ((pg σ : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field).map
        (fun x => x ^ 2 ^ 1) = ((pg σ : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field) := by
      ext i j
      rw [Matrix.map_apply, pg_apply]
      split_ifs <;> simp
    rw [hmap]
    exact pg_transpose_mul σ

theorem mk_dg_mem (h3 : ω ^ 3 = 1) {β : Fin 5 → ZMod 3} (hβ : ∑ j, β j = 0) :
    (ProjGenLinGroup.mk (dg ω β) : ProjGenLinGroup (Fin 5) U52Field) ∈ projSU 5 2 1 := by
  unfold projSU CFSG.PGLModel.projImage
  refine Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ?_)
  have hdet : ∏ j, u52Zeta ω (β j) = 1 := by
    rw [zeta_prod_fin5 h3, hβ, zeta_zero]
  have hd : ∀ j, u52Zeta ω (β j) ^ (2 ^ 1 + 1) = 1 := fun j => by
    rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num]
    exact zeta_pow_three h3 _
  exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.diagHom_mem_su 2 1 hdet hd

theorem mk_dg_eq_iff (h3 : ω ^ 3 = 1) (hω : orderOf ω = 3) {β γ : Fin 5 → ZMod 3}
    (h : (ProjGenLinGroup.mk (dg ω β) : ProjGenLinGroup (Fin 5) U52Field) =
      ProjGenLinGroup.mk (dg ω γ)) :
    ∃ c : ZMod 3, ∀ j, γ j = β j + c := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hent : ∀ j, u52Zeta ω (β j) * u = u52Zeta ω (γ j) := by
    intro j
    apply Units.ext
    have := congrArg (fun g : GL (Fin 5) U52Field =>
      ((g : GL (Fin 5) U52Field) : Matrix (Fin 5) (Fin 5) U52Field) j j) hu
    simpa [dg_apply, Matrix.diagonal_mul, Matrix.scalar_apply] using this
  have hdiff : ∀ j, u52Zeta ω (γ j - β j) = u := by
    intro j
    apply mul_left_cancel (a := u52Zeta ω (β j))
    have e : β j + (γ j - β j) = γ j := by abel
    rw [← zeta_add h3, e, hent j]
  have key : ∀ j, γ j - β j = γ 0 - β 0 := fun j =>
    zeta_injective hω ((hdiff j).trans (hdiff 0).symm)
  exact ⟨γ 0 - β 0, fun j => by linear_combination key j⟩

theorem mk_dg_comm (h3 : ω ^ 3 = 1) (β γ : Fin 5 → ZMod 3) :
    (ProjGenLinGroup.mk (dg ω β) : ProjGenLinGroup (Fin 5) U52Field) *
        ProjGenLinGroup.mk (dg ω γ) =
      ProjGenLinGroup.mk (dg ω γ) * ProjGenLinGroup.mk (dg ω β) := by
  rw [← map_mul, ← map_mul, ← dg_mul h3, ← dg_mul h3, add_comm]

end Pg

end CFSG.RankThree.PartTwo.Sec4.RonanK432

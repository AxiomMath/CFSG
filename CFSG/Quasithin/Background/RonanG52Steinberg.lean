module

public import CFSG.Quasithin.H13.GoldschmidtG52Module
public import CFSG.Quasithin.Background.RonanG52Higman
public import CFSG.Quasithin.Background.RonanG52Coset

public section

namespace CFSG.Quasithin.RonanG52

open Equiv CFSG.Quasithin.H13.A6.G52 CFSG.CharacterTheory.SteinbergBY.AlternatingSix Matrix

@[expose] def sA : Perm (Fin 6) := swap 0 1

@[expose] def sB : Perm (Fin 6) := swap 2 3

@[expose] def sT : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def sC : Perm (Fin 6) := swap 4 5

@[expose] def pList : List (Perm (Fin 6)) :=
  [0, 1].flatMap fun a => [0, 1].flatMap fun b => [0, 1].flatMap fun c => [0, 1].map fun d =>
    sA ^ a * sB ^ b * sT ^ c * sC ^ d

theorem pList_nodup : pList.Nodup := by decide +kernel

theorem pList_length : pList.length = 16 := by decide +kernel

theorem pList_one_mem : (1 : Perm (Fin 6)) ∈ pList := by decide +kernel

theorem pList_mul : ∀ a ∈ pList, ∀ b ∈ pList, a * b ∈ pList := by decide +kernel

theorem pList_inv : ∀ a ∈ pList, a⁻¹ ∈ pList := by decide +kernel

@[expose] def P₂ : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ pList}
  mul_mem' := fun {a b} ha hb => pList_mul a ha b hb
  one_mem' := pList_one_mem
  inv_mem' := fun {a} ha => pList_inv a ha

theorem card_P₂ : Nat.card P₂ = 16 := by
  rw [CFSG.Quasithin.H13.A6.natCard_eq_length pList_nodup fun _ => Iff.rfl, pList_length]

theorem index_P₂ : P₂.index = 45 := by
  have h := P₂.card_mul_index
  rw [card_P₂, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  have h6 : (Nat.factorial 6) = 720 := by decide
  omega

theorem not_two_dvd_index_P₂ : ¬ 2 ∣ P₂.index := by
  rw [index_P₂]
  decide

@[expose] def vSt : Fin 16 → ZMod 2 := Pi.single 13 1

@[expose] def wSt : Fin 16 → ZMod 2 := ![1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1]

theorem higman_matrix :
    (pList.map fun p => kronHom p * Matrix.vecMulVec vSt wSt * kronHom p⁻¹).sum = 1 := by
  decide +kernel

@[expose] noncomputable def φSt : (Fin 16 → ZMod 2) →ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  Matrix.toLin' (Matrix.vecMulVec vSt wSt)

theorem St_eq_toLin' (g : Perm (Fin 6)) : St g = Matrix.toLin' (kronHom g) :=
  LinearMap.ext fun x => (St_apply g x).trans (Matrix.toLin'_apply _ _).symm

theorem sum_St_conj_P₂ :
    ∑ p ∈ pList.toFinset, St p ∘ₗ φSt ∘ₗ St p⁻¹ = LinearMap.id := by
  have h1 : ∀ p : Perm (Fin 6), St p ∘ₗ φSt ∘ₗ St p⁻¹ =
      Matrix.toLin' (kronHom p * Matrix.vecMulVec vSt wSt * kronHom p⁻¹) := by
    intro p
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, St_eq_toLin', St_eq_toLin', φSt, LinearMap.comp_assoc]
  simp only [h1]
  rw [← map_sum, List.sum_toFinset _ pList_nodup, higman_matrix, Matrix.toLin'_one]

section Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {τ : Representation (ZMod 2) (Perm (Fin 6)) V}

theorem sum_conj_transport_P₂ (ψ : (Fin 16 → ZMod 2) ≃ₗ[ZMod 2] V)
    (hψ : ∀ g y, τ g (ψ y) = ψ (St g y)) :
    ∑ p ∈ pList.toFinset, τ p ∘ₗ (ψ.toLinearMap ∘ₗ φSt ∘ₗ ψ.symm.toLinearMap) ∘ₗ τ p⁻¹ =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := ψ.surjective x
  have h := LinearMap.congr_fun sum_St_conj_P₂ y
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at h ⊢
  simp only [LinearEquiv.coe_coe, hψ, LinearEquiv.symm_apply_apply]
  rw [← map_sum, h]

theorem projective_of_equiv_St (e : Representation.Equiv St τ) :
    Module.Projective (MonoidAlgebra (ZMod 2) (Perm (Fin 6))) τ.asModule :=
  projective_asModule_of_higman τ _
    (sum_conj_eq_id_of_odd_index τ P₂ pList.toFinset (fun x => by rw [List.mem_toFinset]; rfl)
      not_two_dvd_index_P₂ _
      (sum_conj_transport_P₂ e.toLinearEquiv fun g y =>
        (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g y).symm))

end Transport

end CFSG.Quasithin.RonanG52

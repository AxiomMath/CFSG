module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Cube

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open Representation
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor frobTensor_isIrreducible
  frobTensor_nonisomorphic)

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def e0 (J : Finset ℕ) : (J → Fin 2) → K :=
  Pi.single (fun _ => 0) 1

theorem e0_ne_zero (J : Finset ℕ) : e0 (K := K) J ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [e0] at this

@[expose] noncomputable def slotEmb (J : Fin 3 → Finset ℕ) :
    (s : Fin 3) → ((J s → Fin 2) → K) →ₗ[K] CubeSpace K J
  | 0 => (TensorProduct.mk K _ _).flip (e0 (J 1) ⊗ₜ e0 (J 2))
  | 1 => TensorProduct.mk K _ _ (e0 (J 0)) ∘ₗ (TensorProduct.mk K _ _).flip (e0 (J 2))
  | 2 => TensorProduct.mk K _ _ (e0 (J 0)) ∘ₗ TensorProduct.mk K _ _ (e0 (J 1))

theorem slotEmb_comm (J : Fin 3 → Finset ℕ) (s : Fin 3) (g : SL(2, K)) (x : (J s → Fin 2) → K) :
    slotEmb J s (frobTensor K K (J s) g x) = cubeRep K J (slot K s g) (slotEmb J s x) := by
  fin_cases s <;>
    simp [slotEmb, cubeRep_tmul, slot_apply_self, slot_apply_of_ne, map_one]

theorem slotEmb_ne_zero (J : Fin 3 → Finset ℕ) (s : Fin 3) : slotEmb (K := K) J s ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (e0 (J s))
  rw [LinearMap.zero_apply] at h1
  fin_cases s
  · exact tmul_ne_zero_of_ne_zero (e0_ne_zero _)
      (tmul_ne_zero_of_ne_zero (e0_ne_zero _) (e0_ne_zero _)) h1
  · exact tmul_ne_zero_of_ne_zero (e0_ne_zero _)
      (tmul_ne_zero_of_ne_zero (e0_ne_zero _) (e0_ne_zero _)) h1
  · exact tmul_ne_zero_of_ne_zero (e0_ne_zero _)
      (tmul_ne_zero_of_ne_zero (e0_ne_zero _) (e0_ne_zero _)) h1

variable [Fintype K] {n : ℕ} {W : Type} [AddCommGroup W] [Module K W]

theorem eq_of_slot_maps (hK : Fintype.card K = 2 ^ n) {J J' : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) (hJ' : IsLabel n J') {B : Representation K (Cube K) W}
    (e : B.Equiv (cubeRep K J'))
    (hs : ∀ s, ∃ f : ((J s → Fin 2) → K) →ₗ[K] W, f ≠ 0 ∧
      ∀ g x, f (frobTensor K K (J s) g x) = B (slot K s g) (f x)) : J = J' := by
  funext s
  obtain ⟨f, hf0, hf⟩ := hs s
  obtain ⟨φ⟩ := cubeRep_slot_equiv hK hJ' s (frobTensor_isIrreducible hK (hJ s))
    (e.toLinearMap ∘ₗ f)
    (fun g x => by
      rw [LinearMap.comp_apply, hf]
      exact LinearMap.congr_fun (e.isIntertwining' (slot K s g)) (f x))
    fun h => hf0 (by
      refine LinearMap.ext fun x => ?_
      have h1 : e.toLinearMap (f x) = 0 := LinearMap.congr_fun h x
      exact e.toLinearEquiv.map_eq_zero_iff.mp h1)
  exact frobTensor_nonisomorphic hK (hJ s) (hJ' s) φ

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

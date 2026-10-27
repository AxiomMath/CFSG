module

public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.Monster.B.TwoA

open Equiv

@[expose] def sym5s : Perm (Fin 5) := swap 0 1

@[expose] def sym5c : Perm (Fin 5) := finRotate 5

theorem closure_sym5 : Subgroup.closure ({sym5c, sym5s} : Set (Perm (Fin 5))) = ⊤ :=
  Equiv.Perm.closure_prime_cycle_swap (by decide) isCycle_finRotate support_finRotate
    ⟨0, 1, by decide, rfl⟩

@[expose] def GoodPair (t d : Perm (Fin 5)) : Prop :=
  t * t = 1 ∧ d ^ 5 = 1 ∧ d ≠ 1 ∧ (t * d) ^ 4 = 1 ∧ (t * d) ^ 2 ≠ 1

instance (t d : Perm (Fin 5)) : Decidable (GoodPair t d) := by
  unfold GoodPair
  infer_instance

@[expose] def ConjPair (t d : Perm (Fin 5)) : Prop :=
  ∃ g : Perm (Fin 5), g * sym5s * g⁻¹ = t ∧ g * sym5c * g⁻¹ = d

instance (t d : Perm (Fin 5)) : Decidable (ConjPair t d) := by
  unfold ConjPair
  infer_instance

theorem pairs_conj : ∀ t d : Perm (Fin 5), GoodPair t d → ConjPair t d := by
  decide +kernel

theorem eq_one_of_comm_sym5 :
    ∀ g : Perm (Fin 5), g * sym5s = sym5s * g → g * sym5c = sym5c * g → g = 1 := by
  decide +kernel

theorem goodPair_sym5 : GoodPair sym5s sym5c := by decide

theorem sym5_conj_surjective :
    Function.Surjective (MulAut.conj : Perm (Fin 5) →* MulAut (Perm (Fin 5))) := by
  intro φ
  obtain ⟨h1, h2, h3, h4, h5⟩ := goodPair_sym5
  have hgood : GoodPair (φ sym5s) (φ sym5c) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, h1, map_one]
    · rw [← map_pow, h2, map_one]
    · intro h
      exact h3 (φ.injective (h.trans (map_one φ).symm))
    · rw [← map_mul, ← map_pow, h4, map_one]
    · intro h
      exact h5 (φ.injective (by rw [map_pow, map_mul, h, map_one]))
  obtain ⟨g, hgs, hgc⟩ := pairs_conj _ _ hgood
  refine ⟨g, ?_⟩
  have e : (MulAut.conj g).toMonoidHom = φ.toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense closure_sym5 ?_
    rintro x (rfl | rfl)
    · exact hgc
    · exact hgs
  exact MulEquiv.ext fun x => DFunLike.congr_fun e x

theorem sym5_conj_injective :
    Function.Injective (MulAut.conj : Perm (Fin 5) →* MulAut (Perm (Fin 5))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcomm : ∀ x : Perm (Fin 5), g * x = x * g := by
    intro x
    have h := congrArg (fun f : MulAut (Perm (Fin 5)) => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  exact eq_one_of_comm_sym5 g (hcomm _) (hcomm _)

theorem sym5_conj_bijective :
    Function.Bijective (MulAut.conj : Perm (Fin 5) →* MulAut (Perm (Fin 5))) :=
  ⟨sym5_conj_injective, sym5_conj_surjective⟩

end CFSG.Monster.B.TwoA

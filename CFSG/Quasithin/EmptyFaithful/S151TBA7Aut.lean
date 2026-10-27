module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.Quasithin.S151TB

open Equiv Equiv.Perm

theorem exists_conj_of_ker_eq {K : Type*} [Group K] (a : K →* alternatingGroup (Fin 7))
    (ha : Function.Surjective a) (f : K →* Equiv.Perm (Fin 7)) (hker : f.ker = a.ker) :
    ∃ g : Equiv.Perm (Fin 7),
      ∀ k : K, f k = g * ((a k : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * g⁻¹ := by
  let θ : alternatingGroup (Fin 7) →* Equiv.Perm (Fin 7) :=
    MonoidHom.liftOfSurjective a ha ⟨f, hker.ge⟩
  have hθ : ∀ k, θ (a k) = f k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply a (Function.surjInv ha)
      (Function.rightInverse_surjInv ha) ⟨f, hker.ge⟩ k
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨k, rfl⟩ := ha x
    rw [hθ] at hx
    have hk : k ∈ f.ker := hx
    rw [hker] at hk
    exact hk
  have hsign : ∀ x, Equiv.Perm.sign (θ x) = 1 := by
    intro x
    have hx : x ∈ commutator (alternatingGroup (Fin 7)) := by
      rw [commutator_alternatingGroup_eq_top (by simp)]
      exact Subgroup.mem_top x
    exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp θ) hx
  let θ' : alternatingGroup (Fin 7) →* alternatingGroup (Fin 7) :=
    θ.codRestrict (alternatingGroup (Fin 7)) (fun x => by
      rw [mem_alternatingGroup]
      exact hsign x)
  have hθ'inj : Function.Injective θ' := fun x y hxy => hθinj (congrArg Subtype.val hxy)
  have hθ'bij : Function.Bijective θ' := Finite.injective_iff_bijective.1 hθ'inj
  obtain ⟨g, hg⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 (MulEquiv.ofBijective θ' hθ'bij)
  refine ⟨g, fun k => ?_⟩
  rw [← hθ k]
  have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) =>
    (((φ (a k) : alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7))) hg
  simpa [θ', MulAut.conjNormal_apply] using h1.symm

end CFSG.Quasithin.S151TB

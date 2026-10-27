module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Model
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Slot
public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Pattern

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module CFSG.Open
open scoped MatrixGroups
open Representation
open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal (block)
open CFSG.Semidihedral.Principal (repMultiplicity_congr_right)
open CFSG.QuasithinUnique.Setup.X7b (isIrreducible_comp repMultiplicity_comp_surjective)

section Perm

variable {K : Type} [Field K]

@[expose] def cubePerm (σ : Equiv.Perm (Fin 3)) : Cube K ≃* Cube K :=
  MulEquiv.arrowCongr σ.symm (MulEquiv.refl _)

theorem cubePerm_slot (σ : Equiv.Perm (Fin 3)) (s : Fin 3) (g : SL(2, K)) :
    cubePerm σ (slot K s g) = slot K (σ.symm s) g :=
  Pi.mulSingle_comp_equiv σ s g

end Perm

section CubeRep

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}

theorem isLabel_comp_perm {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) (σ : Equiv.Perm (Fin 3)) :
    IsLabel n (J ∘ σ) :=
  fun s => hJ (σ s)

theorem cubeRep_perm_equiv (hK : Fintype.card K = 2 ^ n) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) (σ : Equiv.Perm (Fin 3)) :
    Nonempty ((cubeRep K J).Equiv ((cubeRep K (J ∘ σ)).comp (cubePerm σ).toMonoidHom)) := by
  have hirr : Representation.IsIrreducible ((cubeRep K (J ∘ σ)).comp (cubePerm σ).toMonoidHom) :=
    isIrreducible_comp (cubePerm σ).toMonoidHom (cubePerm σ).surjective _
      (cubeRep_isIrreducible hK (isLabel_comp_perm hJ σ))
  obtain ⟨J', hJ', ⟨e⟩⟩ := cube_classification hK _ hirr
  obtain rfl : J = J' := eq_of_slot_maps hK hJ hJ' e fun s => by
    obtain ⟨t, rfl⟩ := σ.surjective s
    refine ⟨slotEmb (J ∘ σ) t, slotEmb_ne_zero _ _, fun g x => ?_⟩
    change _ = cubeRep K (J ∘ σ) (cubePerm σ (slot K (σ t) g)) _
    rw [cubePerm_slot, Equiv.symm_apply_apply]
    exact slotEmb_comm (J ∘ σ) t g x
  exact ⟨e.symm⟩

variable {V : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem pat_comp_cubePerm (hK : Fintype.card K = 2 ^ n) (τ : Representation K (Cube K) V)
    {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) (σ : Equiv.Perm (Fin 3)) :
    pat (τ.comp (cubePerm σ).toMonoidHom) J = pat τ (J ∘ σ) := by
  obtain ⟨e⟩ := cubeRep_perm_equiv hK hJ σ
  rw [pat, pat, repMultiplicity_congr_right _ e]
  exact repMultiplicity_comp_surjective _ (cubePerm σ).surjective τ _

theorem pat_perm_of_equiv (hK : Fintype.card K = 2 ^ n) {τ : Representation K (Cube K) V}
    {σ : Equiv.Perm (Fin 3)} (φ : τ.Equiv (τ.comp (cubePerm σ).toMonoidHom))
    {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) : pat τ (J ∘ σ) = pat τ J := by
  rw [← pat_comp_cubePerm hK τ hJ σ, pat_congr φ]

end CubeRep

section Sp6

variable {K : Type} [Field K] {Y : Type} [AddCommGroup Y] [Module K Y]

@[expose] noncomputable def blockPermEquiv (ρ : Representation K (StatedSp 3 K) Y)
    (σ : Equiv.Perm (Fin 3)) :
    Representation.Equiv (ρ.comp block) ((ρ.comp block).comp (cubePerm σ).toMonoidHom) :=
  Representation.Equiv.mk
    (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom (levi (permGL σ)))) fun g => by
    change ρ (levi (permGL σ)) ∘ₗ ρ (block g) = ρ (block (g ∘ σ)) ∘ₗ ρ (levi (permGL σ))
    rw [← levi_permGL_conj_block σ g, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp,
      ← map_mul, ← map_mul, inv_mul_cancel_right]

variable [Fintype K] [CharP K 2] {n : ℕ} [Module.Finite K Y]

theorem pat_block_perm (hK : Fintype.card K = 2 ^ n) (ρ : Representation K (StatedSp 3 K) Y)
    {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) (σ : Equiv.Perm (Fin 3)) :
    pat (ρ.comp block) (J ∘ σ) = pat (ρ.comp block) J :=
  pat_perm_of_equiv hK (blockPermEquiv ρ σ) hJ

variable (hK : Fintype.card K = 2 ^ n) (ρ : Representation K (StatedSp 3 K) Y) {A B C : Finset ℕ}
  (hA : ∀ i ∈ A, i < n) (hB : ∀ i ∈ B, i < n) (hC : ∀ i ∈ C, i < n)
include hK hA hB hC

end Sp6

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

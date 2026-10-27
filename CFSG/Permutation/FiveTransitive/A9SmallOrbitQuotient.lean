module

public import CFSG.Permutation.FiveTransitive.SimpleFiniteKernelImage
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.A9SmallOrbitQuotient
open MulAction

theorem false_of_small_orbits
    {G X F : Type} [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (rho : G →* Equiv.Perm F) (hAlt : alternatingGroup F ≤ rho.range)
    (hsmall : ∀ x : X, Nat.card (orbit G x) ≤ 8) : False := by
  classical
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let B := fun x : X => Equiv.Perm (orbit G x)
  let g := fun x : X => toPermHom G (orbit G x)
  have hn (x : X) : ¬ Nat.card (alternatingGroup F) ∣ Nat.card (B x) := by
    intro hd
    have hB : Nat.card (B x) ≤ (8 : ℕ).factorial := by
      rw [Nat.card_perm]
      exact Nat.factorial_le (hsmall x)
    have hA := Nat.le_of_dvd (Nat.card_pos (α := B x)) hd
    rw [nat_card_alternatingGroup,hF] at hA
    norm_num at hA hB
    omega
  have hi (u : G) (hu : ∀ x, g x u = 1) : u = 1 := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    have hu' : (toPermHom G (orbit G x)) u = 1 := hu x
    have he : u • (⟨x,mem_orbit_self x⟩ : orbit G x) = ⟨x,mem_orbit_self x⟩ := by
      rw [← toPerm_apply, ← toPermHom_apply, hu']
      rfl
    simpa only [orbit.coe_smul, one_smul] using congrArg Subtype.val he

  have hb := SimpleFiniteKernelImage.eq_bot_of_jointly_faithful B rho g
    (alternatingGroup F) hAlt hn hi
  have hcard : Nat.card (alternatingGroup F) = 1 := Subgroup.card_eq_one.mpr hb
  rw [nat_card_alternatingGroup,hF] at hcard
  norm_num at hcard

end FiveTransitive.A9SmallOrbitQuotient

end CFSG

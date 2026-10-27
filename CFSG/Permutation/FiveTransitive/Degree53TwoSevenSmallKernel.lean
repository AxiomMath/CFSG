module

public import CFSG.Permutation.FiveTransitive.SimpleIteratedKernelImage
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenSmallKernel

theorem exists_five_in_kernel
    {N F Y : Type} [Group N] [Finite N] [Fintype F] [DecidableEq F] [Finite Y]
    (hF : Nat.card F = 7) (hY : Nat.card Y = 5)
    (f : N →* Equiv.Perm F) (hf : alternatingGroup F ≤ f.range) (g : N →* Equiv.Perm Y) :
    ∃ z : N, orderOf z = 5 ∧ g z = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let A := alternatingGroup F
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by omega)
  have hA : Nat.card A = 2520 := by
    change Nat.card (alternatingGroup F) = 2520
    rw [nat_card_alternatingGroup,hF]
    norm_num
  have hAf : A ≤ f.range := hf
  have hnot : ¬ Nat.card A ∣ Nat.card (Equiv.Perm Y) := by
    rw [hA,Nat.card_perm,hY]
    norm_num
  have hAK := SimpleIteratedKernelImage.le_kernel_image f g A hAf hnot
  have hd : 5 ∣ Nat.card g.ker :=
    (show 5 ∣ Nat.card A by rw [hA]; norm_num).trans
      ((Subgroup.card_dvd_of_le hAK).trans (Subgroup.card_range_dvd (f.comp g.ker.subtype)))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := g.ker) 5 hd
  exact ⟨z.val,(Subgroup.orderOf_coe z).trans hz,z.property⟩

end FiveTransitive.Degree53TwoSevenSmallKernel

end CFSG

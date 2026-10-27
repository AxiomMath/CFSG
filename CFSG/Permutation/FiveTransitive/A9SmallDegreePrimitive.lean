module

public import CFSG.Permutation.FiveTransitive.A9SmallOrbitQuotient
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG

namespace FiveTransitive.A9SmallDegreePrimitive
open MulAction
open scoped Pointwise

theorem isPreprimitive
    {G X F : Type} [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X] [IsPretransitive G X]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (rho : G →* Equiv.Perm F) (hAlt : alternatingGroup F ≤ rho.range)
    (hX : Nat.card X ≤ 14) : IsPreprimitive G X := by
  classical
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  constructor
  intro B hB
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  by_cases htop : B = Set.univ
  · exact Or.inr htop
  have htwo : 2 ≤ B.ncard := by
    have hn := (Set.ncard_le_one_iff_subsingleton (s := B)).not.mpr hsub
    omega
  obtain ⟨x,hx⟩ := Set.nonempty_of_ncard_ne_zero (by omega : B.ncard ≠ 0)
  have hprod := hB.ncard_block_mul_ncard_orbit_eq ⟨x,hx⟩
  have hbn : B.ncard < Nat.card X := by
    have hb := Set.ncard_le_card B
    have hne : B.ncard ≠ Nat.card X := (Set.eq_univ_iff_ncard B).not.mp htop
    omega
  have hk : 2 ≤ (orbit G B).ncard := by nlinarith
  have hb7 : B.ncard ≤ 7 := by nlinarith
  have hk7 : (orbit G B).ncard ≤ 7 := by nlinarith
  let C := orbit G B
  let sigma := toPermHom G C
  let K := sigma.ker
  have hn : ¬ Nat.card (alternatingGroup F) ∣ Nat.card (Equiv.Perm C) := by
    intro hd
    have hsmall : Nat.card (Equiv.Perm C) ≤ (7 : ℕ).factorial := by
      rw [Nat.card_perm]
      exact Nat.factorial_le (by simpa only [C,Nat.card_coe_set_eq] using hk7)
    have hlarge := Nat.le_of_dvd (Nat.card_pos (α := Equiv.Perm C)) hd
    rw [nat_card_alternatingGroup,hF] at hlarge
    norm_num at hlarge hsmall
    omega
  have hAK : alternatingGroup F ≤ (rho.comp K.subtype).range :=
    SimpleIteratedKernelImage.le_kernel_image rho sigma (alternatingGroup F) hAlt hn
  have hpres (k : K) (c : C) : k.val • c.val = c.val := by
    have he : sigma k.val = 1 := k.property
    exact congrArg Subtype.val (congrArg (fun e : Equiv.Perm C => e c) he)
  have horbit (y : X) : Nat.card (orbit K y) ≤ 8 := by
    obtain ⟨g,hg⟩ := exists_smul_eq G x y
    let c : C := ⟨g • B,mem_orbit_iff.mpr ⟨g,rfl⟩⟩
    have hy : y ∈ c.val := by
      change y ∈ g • B
      rw [← hg]
      exact Set.smul_mem_smul_set hx
    have hle : orbit K y ⊆ c.val := by
      intro z hz
      obtain ⟨k,rfl⟩ := mem_orbit_iff.mp hz
      have hm : k.val • y ∈ k.val • c.val := Set.smul_mem_smul_set hy
      rwa [hpres k c] at hm
    have hcard : c.val.ncard = B.ncard := by exact Set.ncard_smul_set g B
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hle).trans (by rw [hcard]; omega)
  exact (A9SmallOrbitQuotient.false_of_small_orbits hF (rho.comp K.subtype) hAK horbit).elim

end FiveTransitive.A9SmallDegreePrimitive

end CFSG

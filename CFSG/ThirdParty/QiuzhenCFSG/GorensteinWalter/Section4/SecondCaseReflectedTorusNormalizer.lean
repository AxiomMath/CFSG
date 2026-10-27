module
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic subgroups in a reflected dihedral centralizer

A cyclic subgroup of a reflected dihedral centralizer that contains the
central involution is contained in the rotation torus.  This is the
normality/uniqueness step used when transporting the Section-4 torus through
a semilinear centralizer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In a reflected dihedral pair `(T,s)` with `C(t)=T ⊔ ⟨s⟩`, every cyclic
subgroup of `C(t)` containing the involution `t` lies in `T`. -/
public theorem cyclic_subgroup_containing_involution_le_reflected_torus
    {G : Type u} [Group G] [Finite G]
    {t : G} (ht : IsInvolution t)
    (T : Subgroup G) (s : G)
    (hTcyc : IsCyclic T) (htT : t ∈ T)
    (hsI : IsInvolution s) (hs_not_T : s ∉ T)
    (hinvT : ∀ x : G, x ∈ T → s * x * s⁻¹ = x⁻¹)
    (hC : Subgroup.centralizer ({t} : Set G) = T ⊔ Subgroup.zpowers s)
    {X : Subgroup G} (hXcyc : IsCyclic X)
    (hXcent : X ≤ Subgroup.centralizer ({t} : Set G))
    (htX : t ∈ X) :
    X ≤ T := by
  classical
  intro x hx
  by_contra hxT
  have hxsup : x ∈ T ⊔ Subgroup.zpowers s := by
    rw [← hC]
    exact hXcent hx
  have hwsq : s * s = 1 := by
    simpa [pow_two] using hsI.2
  have hcyclic_unique :
      ∀ a b : X, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 → a = b := by
    let : IsCyclic X := hXcyc
    let : Fintype X := Fintype.ofFinite X
    intro a b ha ha2 hb hb2
    by_contra hab
    let S : Finset X := {1, a, b}
    have hSsub : S ⊆ ({z : X | z ^ 2 = 1} : Finset X) := by
      intro z hz
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simp
      · simpa using ha2
      · simpa using hb2
    have hcard : S.card ≤ 2 := by
      exact le_trans (Finset.card_le_card hSsub)
        (IsCyclic.card_pow_eq_one_le (α := X) (n := 2) (by norm_num))
    have h1a : (1 : X) ≠ a := by
      intro h
      exact ha h.symm
    have h1b : (1 : X) ≠ b := by
      intro h
      exact hb h.symm
    have hbad : 3 ≤ 2 := by
      simpa [S, h1a, h1b, ha, hb, hab] using hcard
    omega
  rcases (mem_sup_zpowers_of_involution_inverts hs_not_T hwsq hinvT).mp hxsup with
    ⟨u, hu, hxu | hxu⟩
  · exfalso
    apply hxT
    rw [hxu]
    exact hu
  · have hx2 : x ^ 2 = 1 := by
      rw [hxu]
      calc
        (u * s) ^ 2 = (u * s) * (u * s) := by rw [pow_two]
        _ = u * (s * u * s⁻¹) * (s * s) := by group
        _ = u * u⁻¹ * (s * s) := by rw [hinvT u hu]
        _ = u * u⁻¹ * 1 := by rw [hwsq]
        _ = 1 := by simp
    have hx_ne : x ≠ 1 := by
      intro hx1
      apply hxT
      simpa [hx1] using T.one_mem
    have ht_ne : t ≠ 1 := ht.1
    have heq : (⟨x, hx⟩ : X) = (⟨t, htX⟩ : X) := by
      apply hcyclic_unique
      · intro h1
        apply hx_ne
        exact congrArg Subtype.val h1
      · apply Subtype.ext
        simpa [pow_two] using hx2
      · intro h1
        apply ht_ne
        exact congrArg Subtype.val h1
      · apply Subtype.ext
        simpa [pow_two] using ht.2
    have hxt : x = t := congrArg Subtype.val heq
    exact hxT (hxt ▸ htT)

end CFSG.GorensteinWalter

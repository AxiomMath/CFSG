module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.Congruence
public import CFSG.ThirdParty.BrauerInduction.Background.LinearAlgebra.IntegerLattice
public import CFSG.ThirdParty.BrauerInduction.Bernstein.Ideal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's global ideal and lattice argument

This file combines the fixed-prime ideals `JIdeal p` into the global ideal
`JGlobalIdeal`.

The global ideal is mapped into the finite free lattice of integer-valued class
functions. Bernstein's prime-power congruences and the lattice local-to-global
criterion then show that the unit belongs to `JGlobalIdeal`.
-/


universe u

namespace CFSG.BrauerInduction.Bernstein

variable {k G : Type u} [Field k] [Group G] [Finite G]

section JGlobalIdeal

/-!
## The global Bernstein span

This section combines the prime-local ideals `JIdeal p` into the global integral
`JGlobalIdeal`

-/

/--
The global Bernstein ideal.

This is the supremum, over all primes `p`, of the fixed-prime ideals `JIdeal p`
in the ring of integer-valued cyclotomic characters.
-/
@[expose] def JGlobalIdeal :
    Ideal (ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)) :=
  ⨆ (p : ℕ) (_ : Fact p.Prime),
    JIdeal (k := k) (G := G) p


/--
Each fixed-prime Bernstein ideal is contained in the global Bernstein ideal.
-/
lemma JIdeal.le_JGlobalIdeal
    (p : ℕ) [Fact p.Prime] :
    JIdeal (k := k) (G := G) p ≤ JGlobalIdeal := by
  exact le_iSup_of_le p
    (le_iSup_of_le (inferInstance : Fact p.Prime) le_rfl)

/--
The global Bernstein ideal regarded as a `ℤ`-submodule of the integral
cyclotomic character ring.
-/
private def JGlobalIntSubmodule :
    Submodule ℤ
      (ClassFun.IntegralCyclotomicCharacterRing
        (k := k) (G := G)) where
  carrier := JGlobalIdeal (k := k) (G := G)
  zero_mem' := (JGlobalIdeal (k := k) (G := G)).zero_mem
  add_mem' := fun hx hy =>
    (JGlobalIdeal (k := k) (G := G)).add_mem hx hy
  smul_mem' := by
    intro n f hf
    exact zsmul_mem hf n

end JGlobalIdeal

section JGlobalLattice

/--
The image of the global Bernstein ideal in the full lattice of integer-valued
class functions.
-/
def JGlobalLattice :
    Submodule ℤ (ClassFun.IntegerValued (k := k) (G := G)) :=
  (JGlobalIntSubmodule (k := k) (G := G)).map
    ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFunLinear

namespace JIdeal


lemma mem_JGlobalLattice_of_mem
    {f : ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)}
    (hf : f ∈ JGlobalIdeal) :
    ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFun f ∈
      JGlobalLattice (k := k) (G := G) := by
  exact ⟨f, hf, rfl⟩

/--
Bernstein's prime-power congruences imply that the constant function `1`
belongs to the global Bernstein lattice.
-/
theorem one_mem_JGlobalLattice [CharZero k] [IsAlgClosed k] :
    (1 : ClassFun.IntegerValued (k := k) (G := G)) ∈ JGlobalLattice := by
  apply Submodule.mem_of_forall_primePow_congr
  intro p hp N
  letI : Fact p.Prime := ⟨hp⟩
  let F := localSumPower (k := k) (G := G) p N
  let d : ClassFun.IntegerValued :=
    ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFun (F - 1)
  have hn :
      (((p ^ N : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero N hp.ne_zero
  have hdvd :
      ∀ g : G,
        (((p ^ N : ℕ) : ℤ)) ∣
          ClassFun.IntegerValuedClassFun.intLift d g := by
    intro g
    apply
      localSumPower_sub_one_values_dvd (k := k) (G := G) p N g
    exact
      ClassFun.IntegerValuedClassFun.intValue_spec d g
  obtain ⟨y, hy⟩ :=
    ClassFun.IntegerValuedClassFun.exists_zsmul_eq_of_intLift_dvd (((p ^ N : ℕ) : ℤ)) hn d hdvd
  refine ⟨-y, ?_⟩
  have hF :
      ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFun F ∈ JGlobalLattice := by
    apply mem_JGlobalLattice_of_mem
    apply JIdeal.le_JGlobalIdeal p
    exact localSumPower_mem_JIdeal p N
  have heq :
      (1 : ClassFun.IntegerValued) - (((p ^ N : ℕ) : ℤ) • (-y)) =
        ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFun F := by
    let ι :=
      ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFun (k := k) (G := G)
    calc
      1 - (((p ^ N : ℕ) : ℤ) • (-y))
        = 1 + (((p ^ N : ℕ) : ℤ) • y) := by rw [smul_neg, sub_neg_eq_add]
      _ = 1 + d := congrArg (fun z => 1 + z) hy
      _ = ι 1 + ι (F - 1) := congrArg₂ (· + ·) ι.map_one.symm rfl
      _ = ι (1 + (F - 1)) := (ι.map_add 1 (F - 1)).symm
      _ = ι F := congrArg ι (by abel)
  rw [heq]
  exact hF

end JIdeal
end JGlobalLattice

/--
The unit belongs to the global Bernstein ideal.

The prime-power congruences first show that the unit belongs to the image of
`JGlobalIdeal` in the lattice of integer-valued class functions. Injectivity of
the inclusion of the integral cyclotomic character ring then gives the result.
-/
theorem one_mem_JGlobalIdeal [CharZero k] [IsAlgClosed k] :
    (1 : ClassFun.IntegralCyclotomicCharacterRing
        (k := k) (G := G)) ∈ JGlobalIdeal := by
  have h :=
    JIdeal.one_mem_JGlobalLattice (k := k) (G := G)
  rcases h with ⟨f, hf, hfone⟩
  have hf_eq_one :
      f = (1 : ClassFun.IntegralCyclotomicCharacterRing ) := by
    apply
      ClassFun.IntegralCyclotomicCharacterRing.toIntegerValuedClassFun_injective
    simpa using hfone
  change f ∈ JGlobalIdeal  at hf
  simpa [hf_eq_one] using hf

end CFSG.BrauerInduction.Bernstein

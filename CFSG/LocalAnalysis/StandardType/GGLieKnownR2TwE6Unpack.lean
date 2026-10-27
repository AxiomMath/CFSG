module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Data

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

private theorem twE6_e6Certificate_check : e6Certificate.check = true := by
  decide +kernel

private theorem twE6Lift_index :
    ∀ i : Fin 8, ∃ k : Fin e6Certificate.roots.length, e6Certificate.root k = twE6Lift i := by
  decide +kernel

private theorem twE6Long_index :
    ∀ j : Fin 12, ∃ k : Fin e6Certificate.roots.length, e6Certificate.root k = twE6Long j := by
  decide +kernel

private theorem twE6_isRoot_of_index {v : Fin (Tag.rank .E6) → ℤ}
    (k : Fin e6Certificate.roots.length) (hk : e6Certificate.root k = v) : IsRoot .E6 v :=
  hk ▸ RootCertificate.isRoot_root twE6_e6Certificate_check k k.2

theorem twE6Lift_isRoot (i : Fin 8) : IsRoot .E6 (twE6Lift i) := by
  obtain ⟨k, hk⟩ := twE6Lift_index i
  exact twE6_isRoot_of_index k hk

theorem twE6Lift_ne_rho (i : Fin 8) : rho (twE6Lift i) ≠ twE6Lift i := by
  have h : ∀ i : Fin 8, rho (twE6Lift i) ≠ twE6Lift i := by decide +kernel
  exact h i

theorem twE6_proj_lift (i : Fin 8) : proj (twE6Lift i) = twE6Gamma i := by
  have h : ∀ i : Fin 8, proj (twE6Lift i) = twE6Gamma i := by decide +kernel
  exact h i

theorem twE6Long_isRoot (j : Fin 12) : IsRoot .E6 (twE6Long j) := by
  obtain ⟨k, hk⟩ := twE6Long_index j
  exact twE6_isRoot_of_index k hk

theorem twE6Long_rho (j : Fin 12) : rho (twE6Long j) = twE6Long j := by
  have h : ∀ j : Fin 12, rho (twE6Long j) = twE6Long j := by decide +kernel
  exact h j

theorem twE6_proj_long (j : Fin 12) : proj (twE6Long j) = twE6Delta j := by
  have h : ∀ j : Fin 12, proj (twE6Long j) = twE6Delta j := by decide +kernel
  exact h j

@[expose] def twE6PairRoot (i : Fin 8) : Fin (Tag.rank .E6) → ℤ :=
  twE6Lift i + rho (twE6Lift i.rev)

private theorem twE6PairRoot_index :
    ∀ i : Fin 8, ∃ k : Fin e6Certificate.roots.length,
      e6Certificate.root k = twE6PairRoot i := by
  decide +kernel

theorem twE6PairRoot_isRoot (i : Fin 8) : IsRoot .E6 (twE6PairRoot i) := by
  obtain ⟨k, hk⟩ := twE6PairRoot_index i
  exact twE6_isRoot_of_index k hk

theorem twE6PairRoot_ne_rho (i : Fin 8) : rho (twE6PairRoot i) ≠ twE6PairRoot i := by
  have h : ∀ i : Fin 8, rho (twE6PairRoot i) ≠ twE6PairRoot i := by decide +kernel
  exact h i

theorem twE6_proj_pairRoot (i : Fin 8) : proj (twE6PairRoot i) = twE6Alpha := by
  have h : ∀ i : Fin 8, proj (twE6PairRoot i) = twE6Alpha := by decide +kernel
  exact h i

end CFSG.StandardType.LieKnownR2.Short

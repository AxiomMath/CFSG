module

public import CFSG.SignalizerFunctorTheorem.MinimalAction.Thompson
public import CFSG.SignalizerFunctorTheorem.MinimalAction.EightCyclic
public import CFSG.SignalizerFunctorTheorem.MinimalAction.EightNoncyclic
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G] [Finite G]

theorem thompson_semidirect_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P Q X : Subgroup G} (hP : IsPGroup p P) (hQ : Nat.Coprime p (Nat.card Q))
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hX : IsPGroup p X)
    (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hQX : Q ≤ Subgroup.normalizer (X : Set G))
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (Q : Set G)) :
    X ≤ Subgroup.centralizer (Q : Set G) :=
  thompson_main hp hp2 hP hQ hPQ hX hPX hQX hC

theorem exists_elemAbelian_eight [Group.IsSolvable G]
    (hcore : CFSG.SignalizerFunctor.Helpers.primeSetCore (GroupType := G) ({2}ᶜ : Set ℕ) = ⊥)
    (hsix : ∃ x : G, orderOf x = 6) {d : G} (hd : IsPGroup 3 (Subgroup.zpowers d)) (hd1 : d ≠ 1)
    {W : Subgroup G} (hW : W ≠ ⊥) (hWe : IsElemAbelian 2 W)
    (hdW : d ∈ Subgroup.normalizer (W : Set G)) (hfree : ∀ w ∈ W, d * w * d⁻¹ = w → w = 1) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  by_contra hno
  have hno' : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≠ 8 := fun E hE h8 =>
    hno ⟨E, hE, h8⟩
  have hrank := card_le_four_of_forall_ne_eight hno'
  have hset : EightSetting (CFSG.SignalizerFunctor.Helpers.primeSetCore (GroupType := G) {2})
      d W :=
    { normal := CFSG.SignalizerFunctor.Helpers.prime_set_core_normal {2}
      pgroup := CFSG.SignalizerFunctor.Helpers.prime_core_isPGroup 2 Nat.prime_two
      selfCentralizing := fun g hg =>
        CFSG.SignalizerFunctor.Helpers.solvable_prime_core_self_centralizing 2 Nat.prime_two
          hcore (Subgroup.mem_centralizer_iff.mpr hg)
      rank := hrank
      three := hd
      ne_one := hd1
      ne_bot := hW
      elem := hWe
      normalizes := hdW
      free := hfree }
  obtain ⟨D, hdD⟩ := hd.exists_le_sylow
  have hdD' : d ∈ (D : Subgroup G) := hdD (Subgroup.mem_zpowers d)
  by_cases hcyc : IsCyclic (D : Subgroup G)
  · exact hset.cyclic_case hsix D hdD' hcyc
  · exact hset.noncyclic_case D hdD' hcyc

end CFSG.SignalizerFunctorTheorem.MinimalAction

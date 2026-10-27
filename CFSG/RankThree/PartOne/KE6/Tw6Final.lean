module

public import CFSG.RankThree.PartOne.KE6.Tw6Plane
public import CFSG.RankThree.PartOne.KE.PlaneToral

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.E6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE (OddEndpoint cycloVal planeLocalCoreOdd_of_toral_kernels_abstract
  twistedE6_outer_commutator_odd localCoreTrivialOn_noninner_twistedE6
  component_odd_conclusion_of_native)
open scoped Matrix MatrixGroups Pointwise commutatorElement

theorem planeLocalCoreOdd_twE6_six {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K]
    [Finite K] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1) :
    PlaneLocalCoreOdd p (twistedE6RootGroup K σ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have hout := twistedE6_outer_commutator_odd hℓ hf hK σ hσ
  have hcore := localCoreTrivialOn_noninner_twistedE6 hℓ hf hK σ hσ hp hp3
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3
    (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (e6_tw_six_toral K hf hK σ hσ hp hp3 hpq Ω) hout hcore
    (fun B hB A _ hA hcard hAin => by
      rw [e6_tw_six_I_trivial K hf hK σ hσ hp hp3 hpq Ω hB A hA hcard hAin, Subgroup.card_bot]
      exact odd_one)

theorem oddEndpoint_twE6_phi6 :
    OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 6 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  have hm' : TwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (ℓ ^ f) := hmod.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm'
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := hK
  have hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    simpa [cycloVal, exhaustionPhi] using hc
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e.symm
    (planeLocalCoreOdd_twE6_six hℓ K hf hK2 σ hσ hp hp3 hpq)).1

end CFSG.RankThree.PartOne.KE6

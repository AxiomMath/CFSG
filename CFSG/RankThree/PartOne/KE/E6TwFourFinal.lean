module

public import CFSG.RankThree.PartOne.KE.E6TwFourPlane
public import CFSG.RankThree.PartOne.KE.PlaneToral

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec e6Rho)
open scoped Matrix MatrixGroups

abbrev e6NegRho : WeylGroup Tag.E6 := e6HRReflProd

theorem e6TwFour_weylImage (x : Fin Tag.E6.rank → ℤ) :
    (e6F4U * e6NegRho) • x = e6SM (-1) *ᵥ permLattice e6Rho x := by
  have h := e6HRReflProd_smul x
  have h' : e6NegRho • x = -permLattice e6Rho x := h
  rw [mul_smul, h', smul_neg, e6SM, Matrix.smul_mulVec, ← weylMatrix_mulVec, neg_one_smul]

theorem planeLocalCoreOdd_twE6_four {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1) :
    PlaneLocalCoreOdd p (twistedE6RootGroup K σ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.E6.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have hout := twistedE6_outer_commutator_odd hℓ hf hK σ hσ
  have hcore := localCoreTrivialOn_noninner_twistedE6 hℓ hf hK σ hσ hp hp3
  have hcm := canonicalRep_mem_monomialSubgroup L (e6F4U * e6NegRho)
  have hπ : weylQuotientHom Tag.E6 L ⟨canonicalRep (coxeterSystem Tag.E6) L
      (e6F4U * e6NegRho), hcm⟩ =
        e6F4U * e6NegRho :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨canonicalRep (coxeterSystem Tag.E6) L
      (e6F4U * e6NegRho), hcm⟩ • x =
        e6SM (-1) *ᵥ permLattice e6Rho x := fun x => by
    rw [hπ]
    exact e6TwFour_weylImage x
  exact planeLocalCoreOdd_of_toral_kernels_abstract hp hp3
    (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (e6_tw_four_solvable K hf hK σ hσ hp hp3 hpq L _ hcm hnW) hout hcore
    (e6_tw_four_hI K hf hK σ hσ hp hp3 hpq L _ hcm hnW)

theorem oddEndpoint_twE6_phi4 :
    OddEndpoint .twistedE6 fun p ℓ f => (p : ℤ) ∣ cycloVal 4 ℓ f := by
  intro G _ _ p ℓ f hp hp3 hℓ hℓp hf hc E hE hEc t ht ht1 L hL hmod hEL hSL
  have hm' : TwistedChevalleyModel (L ⧸ Subgroup.center L) .E6 (ℓ ^ f) := hmod.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hℓ hf hm'
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := hK
  exact (component_odd_conclusion_of_native hp (by omega) hE hEc ht ht1 hL hEL hSL e.symm
    (planeLocalCoreOdd_twE6_four hℓ K hf hK2 σ hσ hp hp3
      (by simpa [cycloVal, exhaustionPhi] using hc))).1

end CFSG.RankThree.PartOne.KE

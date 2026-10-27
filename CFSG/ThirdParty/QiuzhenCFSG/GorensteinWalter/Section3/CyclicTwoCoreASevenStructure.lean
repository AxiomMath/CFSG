module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreLayerASeven

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic first-case layer structure: A₇ quotient with oriented prime `3`

The component layer of the chosen maximal subgroup is forced to have
`A₇` as its odd-core quotient, and the oriented prime of the inverted odd
subgroup is then `3`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic two-core subcase, the selected component layer has
`A₇` quotient by its odd core and the oriented prime is `3`, while the
full inverted-odd and Klein-four package is retained. -/
public theorem firstCase_cyclic_layer_aSeven_and_prime_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0) :
    ∃ od : FirstCaseOrientedPrimeData c,
      ∃ hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B,
        ∃ fd : FirstCaseFourData c od.d,
          ∃ Q : Sylow od.p ↥od.d.bg.B,
            ∃ M : Subgroup G, ∃ X : Subgroup G,
              IsCoatom M ∧
                Subgroup.normalizer
                  (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
                  (c.S : Subgroup G) ≤ M ∧
                    fd.V2 ≤ componentLayerOf M ∧
                      X ≤ componentLayerOf M ∧ X ≠ ⊥ ∧ IsCyclic X ∧
                        IsPGroup od.p X ∧
                        X ≤ qCoreOf od.d.bg.U od.p ∧
                        BenderGlauberman.IsInvertedBy od.d.bg.t2 X ∧
                          X ≤ Subgroup.centralizer (fd.V1 : Set G) ∧
                            IsDGroup (↥(componentLayerOf M)) ∧
                              Nonempty ((componentLayerOf M) ⧸
                                pPrimeCore 2 (componentLayerOf M) ≃*
                                  alternatingGroup (Fin 7)) ∧
                                    od.p = 3 := by
  classical
  obtain ⟨od, hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXcent, hDE, hA7⟩ :=
    firstCase_cyclic_layer_quotient_isASeven hmin c hfirst hcyclic
  refine ⟨od, hU, fd, Q, M, X, hMmax, hMN, hSM, hV2, hXleE, hXne,
    hXcyc, hXp, hXleP, hXinv, hXcent, hDE, hA7, ?_⟩
  exact firstCase_cyclic_oriented_prime_eq_three_of_aSeven_layer
    hmin c hfirst hcyclic od fd M X hMmax hV2 hXleE hXne
    hXp hXinv hXcent hA7

end CFSG.GorensteinWalter

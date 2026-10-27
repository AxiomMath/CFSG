module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem ggKGRt_recipeEquiv
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ n)) ∧
      Nonempty (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) ≃*
        CFSG.LieType.Chevalley.twistedE6RootGroup K σ) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := fun c => iterateFrobeniusEquiv_def K 2 n c
  have hperf := (CFSG.LieType.Chevalley.finite_fixed_root_group_perfect TwistTag.E6
    Nat.prime_two hn K hK σ.toRingHom (fun c => hσ c)).2.2.1
  have hZ : Subgroup.center
      (CFSG.LieType.Chevalley.graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.exceptional_fixed_center_trivial TwistTag.E6 K σ
  obtain ⟨e₁⟩ := CFSG.LieType.Chevalley.nonempty_derivedCentralQuotient_equiv (t := TwistTag.E6)
    (K := K) (σ := σ.toRingHom) hperf hZ
  obtain ⟨e₀⟩ := centerQuot_twistedH_equiv (K := K) TwistTag.E6 n σ.toRingHom (fun c => hσ c)
  exact ⟨σ, hσ, ⟨e₀.trans e₁⟩⟩

theorem ggKGTwoOn_twE6
    (hS : GGKGTwE6InputSplit 4) (hN : GGKGTwE6InputNonsplit 5) :
    GGKGTwoOn fun p lab => lab.tag = .twE6 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) := by
  intro p lab hp hlab hl hs
  obtain ⟨ht, hdvd⟩ := hs
  refine TwE6Delta.labelAll ht ?_
  intro K _ _ hK
  have hn : 1 ≤ lab.n := hlab.1
  have hp5 : 5 ≤ p := hl.1
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨σ, hσ, ⟨e⟩⟩ := ggKGRt_recipeEquiv hn hK
  have hZ : Subgroup.center (TwE6Delta.RecipeR K lab.n) = ⊥ :=
    TwE6Delta.center_recipeR_eq_bot hn hK
  have hIp : GGOutdiagPrime p (TwE6Delta.RecipeR K lab.n) (TwE6Delta.RecipeI K lab.n) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hcp : GGCenterPrime p (TwE6Delta.RecipeR K lab.n) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3
  have hIp' : ∀ φ ∈ TwE6Delta.RecipeI K lab.n, φ ^ p = 1 →
      φ ∈ Set.range
        (MulAut.conj : TwE6Delta.RecipeR K lab.n →* MulAut (TwE6Delta.RecipeR K lab.n)) :=
    fun φ hφ hφp => hIp φ hφ hφp
  rcases hdvd with h | h
  · refine ⟨4, ggTorusLift_twE6Dvd_holds hn hK hp hp2 h, ?_⟩
    exact ggTorusLattice_of_latticeElt hp hIp' hZ hcp
      (ggKGLatticeElt_of_mulEquiv e
        (ggKGTwE6_latticeElt hK hσ hp hp5 (Or.inl h)
          (hS K σ lab.n p hp hp5 hK hσ h)))
  · have hlift := ggTorusLift_twE6Add_holds hn hK hp h
    rw [TwE6Delta.liftRank_of_ne hp3] at hlift
    refine ⟨5, hlift, ?_⟩
    exact ggTorusLattice_of_latticeElt hp hIp' hZ hcp
      (ggKGLatticeElt_of_mulEquiv e
        (ggKGTwE6_latticeElt hK hσ hp hp5 (Or.inr h)
          (hN K σ lab.n p hp hp5 hK hσ h)))

theorem ggKGOneOn_twE6
    (hN : GGKGTwE6InputNonsplit 5) :
    GGKGOneOn fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 := by
  intro p lab hp hlab hl hs
  obtain ⟨ht, hdvd⟩ := hs
  refine TwE6Delta.labelAll ht ?_
  intro K _ _ hK
  have hn : 1 ≤ lab.n := hlab.1
  have hp5 : 5 ≤ p := hl.1
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨σ, hσ, ⟨e⟩⟩ := ggKGRt_recipeEquiv hn hK
  have hZ : Subgroup.center (TwE6Delta.RecipeR K lab.n) = ⊥ :=
    TwE6Delta.center_recipeR_eq_bot hn hK
  have hIp : GGOutdiagPrime p (TwE6Delta.RecipeR K lab.n) (TwE6Delta.RecipeI K lab.n) :=
    TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hcp : GGCenterPrime p (TwE6Delta.RecipeR K lab.n) :=
    TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3
  have hIp' : ∀ φ ∈ TwE6Delta.RecipeI K lab.n, φ ^ p = 1 →
      φ ∈ Set.range
        (MulAut.conj : TwE6Delta.RecipeR K lab.n →* MulAut (TwE6Delta.RecipeR K lab.n)) :=
    fun φ hφ hφp => hIp φ hφ hφp
  have hlift := ggTorusLift_twE6Add_holds hn hK hp hdvd
  rw [TwE6Delta.liftRank_of_ne hp3] at hlift
  refine ⟨5, hlift, ?_⟩
  exact ggTorusRootSL2_of_rootDatum hp hIp' hZ hcp
    (ggKGRootDatum_of_mulEquiv e
      (ggKGTwE6_rootDatum hK hσ hp hp5 hdvd
        (hN K σ lab.n p hp hp5 hK hσ hdvd)))

end CFSG.StandardType

end

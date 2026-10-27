module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCoverPairTwoDReference
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILongRootConj
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.ModelFacts CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType CFSG.StandardType.GGFinModel
open scoped MatrixGroups


theorem rckTwoD_pair_of_canonicalData
    {τ : Tag} {p₀ h : ℕ} {S : LangSetup τ GGL p₀} {a : Fin τ.rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)} (P : RCKTwoDCanonicalData S a i h)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∀ β ∈ (ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h).D.roots,
      GGLongRoot (ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h).D β →
      ∃ γ ∈ componentRoots (rootCharHom a) i,
        ∃ z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)),
        ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
            (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ∧
        ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
            (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ∧
        ((ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h).D.rootGroup β).map P.φ =
          (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) ∧
        ((ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h).D.rootGroup (-β)).map P.φ =
          (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) := by
  classical
  let n := compRank (componentRoots (rootCharHom a) i)
  let M := ggU .POmegaMinus n h
  let k : Fin (n - 1) := ⟨0, by have := P.rank_four_le; omega⟩
  have hk : k.val + 1 < n - 1 := by have := P.rank_four_le; dsimp [k, n]; omega
  have hct := minusDatum_isCTGroupDatum n (minusCoeffs_irr 2 h) P.rank_four_le
  have hirr : IsIrreducible M.D.cartan :=
    isIrreducible_cartanB (by change 0 < n - 1; have := P.rank_four_le; omega)
  have hdiv : M.D.divisible = ∅ := rfl
  have hratio : ∀ j ∈ M.D.divisible, ∀ l,
      symmetrizer M.D.isFiniteType l < 4 * symmetrizer M.D.isFiniteType j := by
    simp only [hdiv, Set.notMem_empty, false_implies, implies_true]
  have hlong0 : IsLongestRoot M.D (Pi.single k 1) :=
    isLongest_single_cartanB (by have := P.rank_four_le; omega) rfl M.D.isFiniteType hk
  have hφmodel : P.φ.range ≤ S.D.model := by
    rw [P.range_eq]
    exact (Subgroup.commutator_le_self _).trans
      ((inf_le_right : _ ≤ S.Γ).trans (Subgroup.commutator_le_self _))
  have hφspan : P.φ.range ≤
      torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
    rw [P.range_eq]
    exact rationalComponent_le_torusGroup_sup_rootSpan_kernelRoots S i hs
  obtain ⟨γ, hγΨ, σ, hzstep, hX, hX'⟩ := rckTwoD_reference_pair P
  have hγ : IsRoot τ γ := (isRootComponent_componentRoots i).isRoot γ hγΨ
  intro β _hβ hlong
  have hlongβ : IsLongestRoot M.D β :=
    RCKK1I.rckK1Ilrc_isLongestRoot_of_longRoot hirr hdiv hlong
  obtain ⟨u, hu, hu'⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hratio hlong0 hlongβ
  obtain ⟨z, hzad, hstab, hstab', hfix, hfix'⟩ :=
    rckPair_assemble S σ P.z P.z_mem hzstep M.D.rootGroup P.φ hφmodel hφspan hγ
      (by simp only [Set.mem_insert_iff, true_or, true_implies])
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true])
      hX hX' u hu hu'
  exact ⟨γ, hγΨ, z, hzad, hstab, hstab', hfix, hfix'⟩

theorem rckPairTwoD_holds : RCKPairTwoD := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hk _hQS
  let P := rckTwoD_canonicalData S hT hp hp2 hTp i hq hk
  obtain ⟨_hstd, hfin, hperf, hsplit, _hlong⟩ := rckTwoD_ggU_facts P.rank_four_le P.field_pos
  have hs1 := (rckTwoD_graph_labelled S hT i hk).2.1
  rw [RCKFrameCoverPair, hs1, mul_one]
  refine ⟨ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h, P.φ,
    rfl, ?_, P.range_eq, P.ker_le_center, hfin, hperf, hsplit, ?_⟩
  · refine Or.inl ⟨.POmegaMinus, compRank (componentRoots (rootCharHom a) i),
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_, rfl⟩
    change Nat.Prime 2 ∧ 1 ≤ h ∧ 4 ≤ compRank (componentRoots (rootCharHom a) i)
    exact ⟨Nat.prime_two, P.field_pos, P.rank_four_le⟩
  · intro _hs β hβ hlong
    exact rckTwoD_pair_of_canonicalData P hs1 β hβ hlong

end CFSG.StandardType.RCKRP

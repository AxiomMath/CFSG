module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.SectionRank.LocalDet

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

private theorem ggTBJXAux_rootChar_eq_one (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    {τ : Tag} {ζ : Kˣ} (hζ : orderOf ζ = p) (f : Multiplicative (Fin τ.rank → ZMod p))
    (α : Fin τ.rank → ℤ) (hf : ggTBJXFun p τ α (Multiplicative.toAdd f) = 0) :
    rootChar (ggTBJXa p τ ζ f) α = 1 := by
  have hzpow : ∀ i : Fin τ.rank,
      (ζ ^ (Multiplicative.toAdd f i).val) ^ (α i) =
        ζ ^ (((Multiplicative.toAdd f i).val : ℤ) * α i) := fun i => by
    rw [← zpow_natCast ζ (Multiplicative.toAdd f i).val, ← zpow_mul]
  have hprod : ∀ s : Finset (Fin τ.rank),
      ∏ i ∈ s, ζ ^ (((Multiplicative.toAdd f i).val : ℤ) * α i) =
        ζ ^ (∑ i ∈ s, ((Multiplicative.toAdd f i).val : ℤ) * α i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih]
  have hcalc : rootChar (ggTBJXa p τ ζ f) α =
      ζ ^ (∑ i : Fin τ.rank, ((Multiplicative.toAdd f i).val : ℤ) * α i) := by
    simp only [rootChar, ggTBJXa]
    refine (Finset.prod_congr rfl fun i _ => hzpow i).trans ?_
    exact hprod Finset.univ
  rw [hcalc]
  have hz4 : ((∑ i : Fin τ.rank, ((Multiplicative.toAdd f i).val : ℤ) * α i : ℤ) :
      ZMod p) = 0 := by
    have h := hf
    rw [ggTBJXFun_apply] at h
    rw [← h]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [ZMod.natCast_zmod_val, mul_comm]
  have hz : ((∑ i : Fin τ.rank, ((Multiplicative.toAdd f i).val : ℤ) * α i : ℤ) :
      ZMod p) = 0 := hz4
  have hdvd : (orderOf ζ : ℤ) ∣ ∑ i : Fin τ.rank,
      ((Multiplicative.toAdd f i).val : ℤ) * α i := by
    rw [hζ]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hz
  exact (orderOf_dvd_iff_zpow_eq_one (x := ζ)).1 hdvd

theorem ggTBJX_kernel
    {τ : Tag} {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {ζ : Kˣ}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL τ K}
    {σ : Multiplicative (Fin τ.rank → ZMod p) →* L'} (hstd : GGTBJXStd p τ ζ ψ σ)
    (f₀ : Multiplicative (Fin τ.rank → ZMod p)) {J : Subgroup L'}
    (hJ : IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')))
    (i : KernelComponent (rootCharHom (ggTBJXa p τ ζ f₀)))
    (hJi : J.map ψ = componentRootSpan K (rootCharHom (ggTBJXa p τ ζ f₀)) i)
    (f : Multiplicative (Fin τ.rank → ZMod p))
    (hf : ∀ β ∈ componentRoots (rootCharHom (ggTBJXa p τ ζ f₀)) i,
      ggTBJXFun p τ β (Multiplicative.toAdd f) = 0) :
    ∀ j ∈ J, σ f * j = j * σ f := by
  have hS : componentRoots (rootCharHom (ggTBJXa p τ ζ f₀)) i ⊆
      rootCharKernel (ggTBJXa p τ ζ f) := by
    intro α hα
    obtain ⟨h, hi⟩ := hα
    exact ⟨h.1, ggTBJXAux_rootChar_eq_one p hstd.2.2.1 f α (hf α ⟨h, hi⟩)⟩
  have hcent : componentRootSpan K (rootCharHom (ggTBJXa p τ ζ f₀)) i ≤
      Subgroup.centralizer ({rootDiagUnit τ (ggTBJXa p τ ζ f)} : Set (ModGL τ K)) := by
    have h := rootSpan_le_centralizer (τ := τ) (K := K) (ggTBJXa p τ ζ f) hS
    simpa only [componentRootSpan, componentRoots] using h
  have hw : ∀ d ∈ J, ⁅σ f, d⁆ ∈ Subgroup.center L' := by
    intro d hd
    refine hstd.1 (MonoidHom.mem_ker.2 ?_)
    rw [map_commutatorElement, hstd.2.2.2 f]
    refine commutatorElement_eq_one_iff_mul_comm.2 ?_
    refine Subgroup.mem_centralizer_iff.1 (hcent ?_) (rootDiagUnit τ (ggTBJXa p τ ζ f))
      (Set.mem_singleton _)
    rw [← hJi]
    exact Subgroup.mem_map_of_mem ψ hd
  have : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  exact CFSG.SectionRank.commute_of_perfect_of_central_commutator J (σ f) hw

end CFSG.StandardType

end

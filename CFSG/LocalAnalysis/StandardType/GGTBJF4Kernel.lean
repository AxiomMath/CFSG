module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
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

private theorem ggTBJ_rootChar_ggTBJa_eq_one_aux (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    {ζ : Kˣ} (hζ : orderOf ζ = p) (f : Multiplicative (Fin 4 → ZMod p))
    (α : Fin 4 → ℤ) (hf : ggTBJFun p α (Multiplicative.toAdd f) = 0) :
    rootChar (ggTBJa p ζ f) α = 1 := by
  have hzpow : ∀ i : Fin 4,
      (ζ ^ (Multiplicative.toAdd f i).val) ^ (α i) =
        ζ ^ (((Multiplicative.toAdd f i).val : ℤ) * α i) := fun i => by
    rw [← zpow_natCast ζ (Multiplicative.toAdd f i).val, ← zpow_mul]
  have hprod : ∀ s : Finset (Fin Tag.F4.rank),
      ∏ i ∈ s, ζ ^ (((Multiplicative.toAdd f i).val : ℤ) * α i) =
        ζ ^ (∑ i ∈ s, ((Multiplicative.toAdd f i).val : ℤ) * α i) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro i s hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih]
  have hcalc : rootChar (ggTBJa p ζ f) α =
      ζ ^ (∑ i : Fin Tag.F4.rank, ((Multiplicative.toAdd f i).val : ℤ) * α i) := by
    simp only [rootChar, ggTBJa]
    refine (Finset.prod_congr rfl fun i _ => hzpow i).trans ?_
    exact hprod Finset.univ
  rw [hcalc]
  have hz4 : ((∑ i : Fin 4, ((Multiplicative.toAdd f i).val : ℤ) * α i : ℤ) : ZMod p) = 0 := by
    have h := hf
    rw [ggTBJFun_apply] at h
    rw [← h]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [ZMod.natCast_zmod_val, mul_comm]
  have hz : ((∑ i : Fin Tag.F4.rank, ((Multiplicative.toAdd f i).val : ℤ) * α i : ℤ) :
      ZMod p) = 0 := hz4
  have hdvd : (orderOf ζ : ℤ) ∣ ∑ i : Fin Tag.F4.rank,
      ((Multiplicative.toAdd f i).val : ℤ) * α i := by
    rw [hζ]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hz
  exact (orderOf_dvd_iff_zpow_eq_one (x := ζ)).1 hdvd

theorem ggTBJ_f4_kernel
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {ζ : Kˣ}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL Tag.F4 K}
    {σ : Multiplicative (Fin 4 → ZMod p) →* L'} (hstd : GGTBJF4Std p ζ ψ σ)
    (f₀ : Multiplicative (Fin 4 → ZMod p)) {J : Subgroup L'}
    (hJ : IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')))
    (i : KernelComponent (rootCharHom (ggTBJa p ζ f₀)))
    (hJi : J.map ψ = componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i)
    (f : Multiplicative (Fin 4 → ZMod p))
    (hf : ∀ β ∈ componentRoots (rootCharHom (ggTBJa p ζ f₀)) i,
      ggTBJFun p β (Multiplicative.toAdd f) = 0) :
    ∀ j ∈ J, σ f * j = j * σ f := by
  have hS : componentRoots (rootCharHom (ggTBJa p ζ f₀)) i ⊆ rootCharKernel (ggTBJa p ζ f) := by
    intro α hα
    obtain ⟨h, hi⟩ := hα
    exact ⟨h.1, ggTBJ_rootChar_ggTBJa_eq_one_aux p hstd.2.2.1 f α (hf α ⟨h, hi⟩)⟩
  have hcent : componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i ≤
      Subgroup.centralizer ({rootDiagUnit Tag.F4 (ggTBJa p ζ f)} : Set (ModGL Tag.F4 K)) := by
    have h := rootSpan_le_centralizer (τ := Tag.F4) (K := K) (ggTBJa p ζ f) hS
    simpa only [componentRootSpan, componentRoots] using h
  have hw : ∀ d ∈ J, ⁅σ f, d⁆ ∈ Subgroup.center L' := by
    intro d hd
    refine hstd.1 (MonoidHom.mem_ker.2 ?_)
    rw [map_commutatorElement, hstd.2.2.2 f]
    refine commutatorElement_eq_one_iff_mul_comm.2 ?_
    refine Subgroup.mem_centralizer_iff.1 (hcent ?_) (rootDiagUnit Tag.F4 (ggTBJa p ζ f))
      (Set.mem_singleton _)
    rw [← hJi]
    exact Subgroup.mem_map_of_mem ψ hd
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  exact CFSG.SectionRank.commute_of_perfect_of_central_commutator J (σ f) hw

end CFSG.StandardType

end

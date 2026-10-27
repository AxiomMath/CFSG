module

public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KLCE.Sector

public section
namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Steinberg.Adjoint

private theorem famProper_iform_single_single
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) :
    iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single j 1) = τ.cartan i j := by
  rcases hτ with rfl | rfl | rfl <;>
    rw [iform_single_left, sum_cartan_mul_pi_single] <;>
    simp [Tag.symmetrizer]

private theorem famProper_reflect_eq_rootReflection_single
    {τ : Tag} (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i v = rootReflection (Pi.single i 1 : Fin τ.rank → ℤ) • v := by
  have h := rootReflection_eq_conj (τ := τ) (β := (Pi.single i 1 : Fin τ.rank → ℤ))
    (w := 1) (j := i) (by simp)
  simp only [one_mul, inv_one, mul_one] at h
  rw [← simple_smul, ← h]

private theorem famProper_compRank_all_roots {τ : Tag} :
    compRank ({α : Fin τ.rank → ℤ | IsRoot τ α}) = τ.rank := by
  unfold compRank
  have htop : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) ''
      {α : Fin τ.rank → ℤ | IsRoot τ α}) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v k • (Pi.single k (1 : ℚ) : Fin τ.rank → ℚ) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]
    rw [hv]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨Pi.single k 1, IsRoot.basis k, ?_⟩
    funext j
    simp [Pi.single_apply]
  rw [htop]
  simp

private theorem famProper_componentRoots_eq_of_kernelRoots_full
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : kernelRoots χ = {α : Fin τ.rank → ℤ | IsRoot τ α}) :
    ∀ i : KernelComponent χ, componentRoots χ i = {α : Fin τ.rank → ℤ | IsRoot τ α} := by
  classical
  have hr : 4 ≤ τ.rank := by rcases hτ with rfl | rfl | rfl <;> decide
  have hs : ∀ k : Fin τ.rank, (Pi.single k 1 : Fin τ.rank → ℤ) ∈ kernelRoots χ :=
    fun k => by rw [hker]; exact IsRoot.basis k
  set i0 : KernelComponent χ := ⟦⟨Pi.single 0 1, hs 0⟩⟧ with hi0
  have hC0 : IsRootComponent (componentRoots χ i0) := isRootComponent_componentRoots i0
  have hsimple : ∀ k : Fin τ.rank,
      (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots χ i0 := by
    intro k
    let S : Finset (Fin τ.rank) := Finset.univ.filter fun j =>
      (Pi.single j 1 : Fin τ.rank → ℤ) ∈ componentRoots χ i0
    have hS : S.Nonempty := ⟨0, by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, componentRoots,
        Set.mem_setOf_eq]
      exact ⟨hs 0, rfl⟩⟩
    have hcl : ∀ i ∈ S, ∀ j, Tag.cartanE τ.rank i j ≠ 0 → j ∈ S := by
      intro i hiS j hne
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hiS ⊢
      have hif : iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single j 1) ≠ 0 := by
        rw [famProper_iform_single_single hτ]
        rcases hτ with rfl | rfl | rfl <;> simpa [Tag.cartan, Tag.rank] using hne
      have hjeq : (⟦⟨Pi.single j 1, hs j⟩⟧ : KernelComponent χ) =
          ⟦⟨Pi.single i 1, hs i⟩⟧ :=
        (mk_eq_of_iform_ne_zero (α := ⟨Pi.single i 1, hs i⟩)
          (β := ⟨Pi.single j 1, hs j⟩) hif).symm
      have hxii : (⟦⟨Pi.single i 1, hs i⟩⟧ : KernelComponent χ) = i0 :=
        (eq_of_mem_componentRoots hiS ⟨hs i, rfl⟩).symm
      exact ⟨hs j, hjeq.trans hxii⟩
    have hSuniv := NbrInnerRest.cartanE_connected (r := τ.rank) hr S hS hcl
    have hkS : k ∈ S := by rw [hSuniv]; exact Finset.mem_univ k
    exact (Finset.mem_filter.1 hkS).2
  have hC0all : componentRoots χ i0 = {α : Fin τ.rank → ℤ | IsRoot τ α} := by
    ext v
    constructor
    · intro hv
      exact (Set.ext_iff.mp hker v).1 hv.1
    · intro hv
      induction hv with
      | basis j => exact hsimple j
      | reflect i hv ih =>
        rw [famProper_reflect_eq_rootReflection_single i]
        exact hC0.reflection_mem _ ih (Pi.single i 1) (hsimple i)
  intro i
  obtain ⟨x, rfl⟩ := Quotient.exists_rep i
  have hxC0 : (x : Fin τ.rank → ℤ) ∈ componentRoots χ i0 := by
    rw [hC0all]
    exact (Set.ext_iff.mp hker x).1 x.2
  have hthis : (⟦x⟧ : KernelComponent χ) = i0 :=
    eq_of_mem_componentRoots ⟨x.2, rfl⟩ hxC0
  rw [hthis]
  exact hC0all

theorem exists_nontrivial_member_of_component_rank_lt
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) < τ.rank) :
    ∃ u, rootDiagUnit τ (a u) ≠ 1 := by
  by_contra h
  push Not at h
  have hker : kernelRoots (famCharHom a) = {α : Fin τ.rank → ℤ | IsRoot τ α} := by
    ext γ
    constructor
    · intro hγ; exact hγ.1
    · intro hγ
      refine (mem_kernelRoots_famChar a).2 ⟨hγ, fun u => ?_⟩
      have hau : a u = 1 := by
        apply rootDiagUnit_injective
        rw [h u, rootDiagUnit_one]
      rw [hau, rootChar_one_tuple']
  have hall := famProper_componentRoots_eq_of_kernelRoots_full hτ hker i
  have hrank : compRank (componentRoots (famCharHom a) i) = τ.rank := by
    rw [hall]
    exact famProper_compRank_all_roots
  omega

end CFSG.StandardType.TableCRes

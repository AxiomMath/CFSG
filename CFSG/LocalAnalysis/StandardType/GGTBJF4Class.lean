module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJCentralizer
public import CFSG.LocalAnalysis.StandardType.GGTBJLift

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTBJ_f4_class
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    {ζ : Kˣ} {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL Tag.F4 K}
    {σ : Multiplicative (Fin 4 → ZMod p) →* L'} (hstd : GGTBJF4Std p ζ ψ σ)
    (f₀ : Multiplicative (Fin 4 → ZMod p)) {J : Subgroup L'}
    (hJ : IsComponentOf J (Subgroup.centralizer ({σ f₀} : Set L')))
    (hJl : ∀ Q : Subgroup L',
      IsComponentOf Q (Subgroup.centralizer ({σ f₀} : Set L')) → Q ≤ J) :
    ∃ i : KernelComponent (rootCharHom (ggTBJa p ζ f₀)),
      J.map ψ = componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i := by
  have hp : p.Prime := Fact.out
  have hζ : orderOf ζ = p := hstd.2.2.1
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hK : 4 ≤ Nat.card K := by
    have h1 : orderOf ζ ≤ Nat.card Kˣ := orderOf_le_card
    rw [hζ, Nat.card_units] at h1
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    omega
  have ha : ∀ i : Fin Tag.F4.rank, ggTBJa p ζ f₀ i ^ p = 1 := by
    intro i
    show (ζ ^ (Multiplicative.toAdd f₀ i).val) ^ p = 1
    rw [← pow_mul, pow_mul', hζp, one_pow]
  have hCX : ∀ c ∈ Subgroup.centralizer ({σ f₀} : Set L'),
      ψ c ∈ toralCentralizer Tag.F4 K (ggTBJa p ζ f₀) := by
    intro c hc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← hstd.2.1]
      exact ⟨c, rfl⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← hstd.2.2.2 f₀, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hc]
  have hne : (kernelRoots (rootCharHom (ggTBJa p ζ f₀))).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hspan : rootSpan Tag.F4 K (rootCharKernel (ggTBJa p ζ f₀)) = ⊥ :=
      ((root_character_kernel_orthogonal_central_product Tag.F4 K
        (rootCharHom (ggTBJa p ζ f₀))).2.2.2.2.2 hempty).1
    have hP : J.map ψ ≤ toralCentralizer Tag.F4 K (ggTBJa p ζ f₀) := by
      rintro x ⟨c, hc, rfl⟩
      exact hCX c (hJ.1 hc)
    have hperfmap : ⁅J.map ψ, J.map ψ⁆ = J.map ψ := by
      rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp ⟨hJ.2.2.1⟩]
    have hP' : J.map ψ ≤ rootSpan Tag.F4 K (rootCharKernel (ggTBJa p ζ f₀)) :=
      ggTBJ_perfect_le_rootSpan Tag.F4 hK hp (ggTBJa p ζ f₀) ha (J.map ψ) hP hperfmap
    have hbot : J.map ψ = ⊥ := le_bot_iff.mp (hP'.trans (le_of_eq hspan))
    have hJleker : J ≤ ψ.ker := (Subgroup.map_eq_bot_iff (H := J) (f := ψ)).mp hbot
    have hJcen : J ≤ Subgroup.center L' := hJleker.trans hstd.1
    have hcenter : Subgroup.center J = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hJcen x.2) (y : L'))
    have hsub : Subsingleton (J ⧸ Subgroup.center J) := by
      rw [hcenter]
      exact QuotientGroup.subsingleton_quotient_top
    haveI := hsub
    obtain ⟨x, y, hxy⟩ := (hJ.2.2.2.toNontrivial : Nontrivial (J ⧸ Subgroup.center J))
    exact hxy (Subsingleton.elim x y)
  obtain ⟨β, hβ⟩ := hne
  let i : KernelComponent (rootCharHom (ggTBJa p ζ f₀)) := ⟦⟨β, hβ⟩⟧
  refine ⟨i, ?_⟩
  have hS : IsComponentOf (componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i)
      (toralCentralizer Tag.F4 K (ggTBJa p ζ f₀)) :=
    ggTBJ_isComponentOf_componentRootSpan Tag.F4 hK (ggTBJa p ζ f₀) i
  have hSr : componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i ≤ ψ.range := by
    rw [hstd.2.1]
    exact (componentRootSpan_le K i).trans
      (rootSpan_le_adjointGroup K (kernelRoots (rootCharHom (ggTBJa p ζ f₀))))
  have hSu : componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i ≤
      Subgroup.centralizer ({ψ (σ f₀)} : Set (ModGL Tag.F4 K)) := by
    have h := hS.1.trans inf_le_right
    rwa [← hstd.2.2.2 f₀] at h
  exact ggTBJ_map_component_eq ψ hstd.1 (σ f₀) hS hSr hSu hCX hJ hJl

end CFSG.StandardType

end


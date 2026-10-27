module

public import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvFin
public import CFSG.LocalAnalysis.StandardType.GGKGLayersE6
public import CFSG.LocalAnalysis.StandardType.GGKGSigmaLayer
public import CFSG.LocalAnalysis.StandardType.GGKGOrthPairs
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.PartOne.KE.E6A3Sigma

public section

namespace CFSG.StandardType.KGL.TwLayer

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE
  CFSG.StandardType CFSG.StandardType.KGL CFSG.StandardType.LayerExc CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

theorem ggLayerOf_inf_eqLocus {G : Type} [Group G] (step : G →* G) {X U Γ : Subgroup G}
    (hU : GGLayerOf X U) (hΓ : Γ ≤ step.eqLocus (MonoidHom.id G))
    (hle : U ⊓ step.eqLocus (MonoidHom.id G) ≤ Γ)
    (hqs : CFSG.IsQuasisimple ↥(U ⊓ step.eqLocus (MonoidHom.id G))) :
    GGLayerOf (Γ ⊓ X) (U ⊓ step.eqLocus (MonoidHom.id G)) := by
  obtain ⟨hUX, hUn, -, hmax⟩ := hU
  have hfix : ∀ g ∈ Γ, step g = g := fun g hg => hΓ hg
  refine ⟨le_inf hle (inf_le_left.trans hUX), ?_, hqs, ?_⟩
  · refine Subgroup.Normal.mk ?_
    intro n hn g
    have hnU : (n : G) ∈ U := (Subgroup.mem_subgroupOf.mp hn).1
    have hnF : step (n : G) = (n : G) := (Subgroup.mem_subgroupOf.mp hn).2
    have hgΓ : (g : G) ∈ Γ := g.2.1
    have hgX : (g : G) ∈ X := g.2.2
    have hnX : (n : G) ∈ X := hUX hnU
    have hn' : (⟨(n : G), hnX⟩ : X) ∈ U.subgroupOf X := hnU
    have hc := hUn.conj_mem _ hn' (⟨(g : G), hgX⟩ : X)
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    refine ⟨hc, ?_⟩
    change step ((g : G) * (n : G) * (g : G)⁻¹) = (g : G) * (n : G) * (g : G)⁻¹
    rw [map_mul, map_mul, map_inv, hfix _ hgΓ, hnF]
  · intro P hPX hPperf
    have hPU : P ≤ U := hmax P (hPX.trans inf_le_right) hPperf
    exact le_inf hPU (fun x hx => hΓ (hPX hx).1)


theorem ggLayerOf_pair_A3 {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hαβ : iform α β = 0) :
    ∃ u : WeylGroup Tag.E6,
      rootSpan Tag.E6 L (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}) =
        (rhoSigmaE6A3 L u).range ∧
      GGLayerOf
        ((famCentralizer {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}).map
          (adjointGroup Tag.E6 L).subtype)
        (rootSpan Tag.E6 L (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)})) := by
  obtain ⟨u, hu⟩ := exists_weyl_sigmaSetE6A3_eq hα hβ hαβ
  have hS := famKernel_kgExpVec_pair hζo hζ hα hβ
  have hspan : rootSpan Tag.E6 L
      (famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)}) =
        (rhoSigmaE6A3 L u).range := by
    rw [hS, ← hu, ← rhoSigmaE6A3_range]
  refine ⟨u, hspan, ?_⟩
  have hF3 : ∀ a ∈ ({zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} :
      Set (Fin Tag.E6.rank → Lˣ)), ∃ n : ℕ, a ^ 3 ^ n = 1 := by
    intro a ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;>
    · refine ⟨1, ?_⟩
      funext i
      simp only [Pi.pow_apply, zetaVec_apply]
      rw [pow_one, ← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]
      rfl
  refine ggLayerOf_map_famCentralizer _
    (exists_ggDer_famStabilizerSubgroup_le_reflection_of_finite Nat.prime_three _
      (Set.toFinite _) hF3) ?_
  rw [hspan]
  exact (CFSG.IsQuasisimple.congr (MonoidHom.ofInjective (rhoSigmaE6A3_injective (L := L) u))).mp
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))

end CFSG.StandardType.KGL.TwLayer

end

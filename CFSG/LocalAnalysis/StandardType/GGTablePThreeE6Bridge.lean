module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem exists_component_of_induced {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) (δ : MulAut X) {M : Subgroup R}
    (hM : IsComponentOf M (ggAutFixedSubgroup (ggInducedAut θ δ))) :
    ∃ K : Subgroup X, IsComponentOf K (ggAutFixedSubgroup δ) ∧
      K.map (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))) = M := by
  classical
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  let f : X →* R := θ.toMonoidHom.comp π
  have hf : Function.Surjective f := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker ≤ Subgroup.center X := by
    intro x hx
    have hx1 : f x = 1 := MonoidHom.mem_ker.mp hx
    have hx2 : π x = 1 := θ.injective (by simpa [f] using hx1)
    have hx3 : x ∈ π.ker := MonoidHom.mem_ker.mpr hx2
    rwa [QuotientGroup.ker_mk'] at hx3
  have hαβ : ∀ k, f (δ k) = ggInducedAut θ δ (f k) := by
    intro k
    exact (ggInducedAut_apply θ δ k).symm
  have hfixσ : ggAutFixedSubgroup (ggInducedAut θ δ) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (ggInducedAut θ δ) := by
    ext r
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, mem_ggAutFixedSubgroup]
  have hfixδ : ggAutFixedSubgroup δ =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ := by
    ext r
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, mem_ggAutFixedSubgroup]
  have hM' : CFSG.Assembly.IsComponentOf M
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (ggInducedAut θ δ)) := by
    rw [← hfixσ]
    exact hM
  obtain ⟨K, hK, hKmap⟩ :=
    CFSG.StandardType.TCJ.tcjLin_component_lift f hf hker δ (ggInducedAut θ δ) hαβ hM'
  refine ⟨K, ?_, ?_⟩
  · rw [hfixδ]
    exact hK
  · simpa only [f, π] using hKmap

end CFSG.StandardType.TablePThreeKG

end

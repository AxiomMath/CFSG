module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SteinbergExtrasPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PerfectC3

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.Quasisimple

open CFSG.Assembly

theorem component_eq_of_central_ker
    {X U : Type*} [Group X] [Group U]
    (ψ : U →* X) (G₀ K : Subgroup X) (e : X)
    (hU : CFSG.IsQuasisimple U) (hrange : ψ.range = G₀)
    (hker : ψ.ker ≤ Subgroup.center U) (hKG : K ≤ G₀)
    (hK : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({e} : Set X)))
    (he : e ∈ Subgroup.centralizer (G₀ : Set X)) :
    K = G₀ := by
  have hG₀q : CFSG.IsQuasisimple G₀ := by
    rw [← hrange]
    exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center hU ψ hker
  have hG₀A : CFSG.Assembly.IsQuasisimple G₀ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G₀).2 hG₀q
  have hG₀cent : G₀ ≤ Subgroup.centralizer ({e} : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp he z hz).symm
  have hKcomp : CFSG.Assembly.IsComponentOf K G₀ :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hK hKG hG₀cent
  exact CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hG₀A hKcomp

end CFSG.StandardType.F4ExplicitPos.Quasisimple

end

public section

namespace CFSG.StandardType.F4ExplicitPos.Quasisimple

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.TitsSimplicity CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.F4ExplicitPos.SteinbergExtras

theorem f4_cartan_isIndecomposable : IsIndecomposable (Tag.cartan .F4) := by
  decide +kernel

theorem nontrivial_f4_native
    (k : Type) [Field k] [CharP k 2] :
    Nontrivial ↥(adjointGroup .F4 k) := by
  have hr : (f4Datum k).rank = 4 := rfl
  have hmem : Pi.single (⟨0, by rw [hr]; norm_num⟩ : Fin (f4Datum k).rank) 1 ∈
      (f4Datum k).roots :=
    Or.inl ⟨1, ⟨0, by rw [hr]; norm_num⟩, by simp⟩
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((f4_steinbergExtras_without117 (K := k)).ne_bot _ hmem)
  exact nontrivial_of_ne (x : ↥(adjointGroup .F4 k)) 1 fun h => hx (Subtype.ext h)

theorem isQuasisimple_f4_native_of_ct
    (k : Type) [Field k] [CharP k 2] [Finite k]
    (hct : IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (f4Datum k).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (f4Datum k).isFiniteType) (f4Datum k).roots
      (f4Datum k).rootGroup (CFSG.LieType.Chevalley.weylElement .F4 k) (torus (τ := .F4) k)) :
    CFSG.IsQuasisimple ↥(adjointGroup .F4 k) := by
  have := nontrivial_f4_native k
  exact CFSG.LieType.TitsSimplicity.isQuasisimple hct
    (f4_steinbergExtras_without117 (K := k))
    (f4_bruhatExtras_without117 (K := k))
    (f4_rootGroupCommutators_without117 (K := k))
    (f4_cartan_isIndecomposable)
    (CFSG.StandardType.F4ExplicitPos.PerfectC3.finiteF4perfection (K := k))

end CFSG.StandardType.F4ExplicitPos.Quasisimple

end

end

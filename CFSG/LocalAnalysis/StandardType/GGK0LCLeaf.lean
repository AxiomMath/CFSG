module

public import CFSG.LocalAnalysis.StandardType.GGK0LCBridge
public import CFSG.LocalAnalysis.StandardType.GGK0LCKacPt
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma lk0xlcleaf_toralCentralizer_eq_toralRootGroup
    {τ : Tag} {K : Type} [Field K] {a : Fin τ.rank → Kˣ}
    (h : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    toralCentralizer τ K a = toralRootGroup τ K a := by
  obtain ⟨hMX, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  refine le_antisymm (fun x hx => ?_) hMX
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨x, hx⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 :=
    (QuotientGroup.eq_one_iff w).2 (Subgroup.mem_subgroupOf.2 (h w.2))
  rw [hw1, map_one] at hq
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq.symm)

theorem k0_centralizer_generated {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R} (hlab : LargeEvenInLambda2 lab)
    (hpair : GGKacExcPair lab p) (A : K0LangMark Omega lab p R I phi)
    (hc : GGKacCentred lab p) :
    adjointGroup A.tau Omega ⊓ Subgroup.centralizer {rootDiagUnit A.tau A.a} ≤
      Subgroup.closure (Set.range (fun b : Fin A.tau.rank → Omegaˣ =>
        rootDiagUnit A.tau b)) ⊔
        rootSpan A.tau Omega (kernelRoots (rootCharHom A.a)) := by
  obtain ⟨K, d, hT, hc', hKp, hpr, hd, ha⟩ := CFSG.StandardType.GGK0LC.k0_kacPt hpair hc A
  have hζ : orderOf A.zeta = K.p := by
    rw [A.zeta_order, hKp]
  have hp : K.p.Prime := by
    rwa [hKp]
  have hd' : ¬ K.p ∣ d := by
    rwa [hKp]
  have hle := CFSG.StandardType.GGK0LC.rootCharStabilizerSubgroup_le_kernelReflectionGroup_kac
    A.a A.zeta K hζ ha hT hc' hp hd'
  have heq := lk0xlcleaf_toralCentralizer_eq_toralRootGroup hle
  change toralCentralizer A.tau Omega A.a ≤
    Subgroup.closure (Set.range (fun b : Fin A.tau.rank → Omegaˣ =>
      rootDiagUnit A.tau b)) ⊔
      rootSpan A.tau Omega (kernelRoots (rootCharHom A.a))
  rw [heq]
  change torusGroup A.tau Omega ⊔ rootSpan A.tau Omega (rootCharKernel A.a) ≤
    Subgroup.closure (Set.range (fun b : Fin A.tau.rank → Omegaˣ =>
      rootDiagUnit A.tau b)) ⊔
      rootSpan A.tau Omega (kernelRoots (rootCharHom A.a))
  refine sup_le ?_ ?_
  · intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_range_self b))
  · exact le_sup_right

end CFSG.StandardType.GGK0MarkedKacIface1587

end

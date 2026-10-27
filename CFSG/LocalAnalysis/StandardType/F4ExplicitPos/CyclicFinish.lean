module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OrbitSelectionPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicImplementersPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.CyclicFinish

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly

open scoped Pointwise

variable {L : Type} [Field L]

theorem f4_hgen
    {K : Type} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : Fin Tag.F4.rank → Kˣ) (ha : ∀ i, a i ^ p = 1) :
    toralCentralizer Tag.F4 K a ≤
      torusGroup Tag.F4 K ⊔ rootSpan Tag.F4 K (kernelRoots (rootCharHom a)) := by
  intro g hg
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    CFSG.StandardType.F4ExplicitPos.BruhatNo117.f4_hX a g hg
  have hwsub : w ∈ rootCharStabilizerSubgroup a := mem_rootCharStabilizerSubgroup.2 hw
  have hwker : w ∈ kernelReflectionGroup a :=
    CFSG.StandardType.F4ExplicitPos.CyclicImplementers.f4_stabilizer_le_kernel hp hp2 a ha hwsub
  have hwgood : canonicalRep (coxeterSystem Tag.F4) K w ∈ toralRootGroup Tag.F4 K a :=
    CyclicImplementers.kernelReflectionGroup_le_goodWeylSubgroup a hwker
  change h * u * canonicalRep (coxeterSystem Tag.F4) K w * v ∈ toralRootGroup Tag.F4 K a
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)))
      hwgood) (Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv))

theorem f4_componentRootSpan_commute
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (i j : KernelComponent χ) (hij : i ≠ j) :
    ∀ u ∈ componentRootSpan L χ i, ∀ v ∈ componentRootSpan L χ j, Commute u v := by
  intro u hu v hv
  exact (Subgroup.mem_centralizer_iff.1
    (CyclicImplementers.componentRootSpan_le_centralizer_good hij L hu) v hv).symm

theorem f4_orbit_commute_rootSpan_rationalRoots
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* Lˣ}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : rationalRoots ρ χ i ≠ rationalRoots ρ χ j) :
    ∀ x ∈ rootSpan Tag.F4 L (rationalRoots ρ χ i),
      ∀ y ∈ rootSpan Tag.F4 L (rationalRoots ρ χ j), Commute x y :=
  CFSG.StandardType.F4ExplicitPos.OrbitSelection.orbit_commute_rootSpan_rationalRoots
    (fun i j hij => f4_componentRootSpan_commute i j hij) hker hform hij

theorem f4_component_le_rationalRootSpan
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    [Finite D.model]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : Fin Tag.F4.rank → Lˣ) (ha : ∀ i, a i ^ p = 1)
    (haD : rootDiagUnit Tag.F4 a ∈ D.torus)
    (K : Subgroup (ModGL Tag.F4 L))
    (hK : IsComponentOf K (D.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a})) :
    ∃ i : KernelComponent (rootCharHom a),
      K ≤ rootSpan Tag.F4 L (rationalRoots ρ (rootCharHom a) i) :=
  CFSG.StandardType.F4ExplicitPos.OrbitSelection.component_le_rationalRootSpan D ρ hρ a haD
    (f4_hgen hp hp2 a ha)
    (fun _ _ hij => f4_componentRootSpan_commute _ _ hij) K hK

end CFSG.StandardType.F4ExplicitPos.CyclicFinish

end

end

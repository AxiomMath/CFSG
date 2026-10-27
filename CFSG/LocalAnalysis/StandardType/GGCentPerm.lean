module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentPerm

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ntpS2_componentRootSpan_injective
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) {i j : KernelComponent (rootCharHom a)}
    (h : componentRootSpan L (rootCharHom a) i = componentRootSpan L (rootCharHom a) j) :
    i = j :=
  eq_of_rootSpan_componentRoots_eq (K := L) (χ := rootCharHom a) h

theorem ntpS2_perm
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (g : ModGL .E6 L)
    (hg : g ∈ adjointGroup .E6 L) (hgd : rootDiagUnit .E6 a * g = g * rootDiagUnit .E6 a) :
    ∃ π : Equiv.Perm (KernelComponent (rootCharHom a)), ∀ i,
      (componentRootSpan L (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
        componentRootSpan L (rootCharHom a) (π i) := by
  classical
  have hgC : g ∈ toralCentralizer .E6 L a := by
    rw [mem_toralCentralizer]
    exact ⟨hg, by rw [hgd, mul_assoc, mul_inv_cancel, mul_one]⟩
  obtain ⟨w, hw, m, hm, hgmw⟩ :=
    exists_mul_canonicalRep_of_mem_toralCentralizer (K := L) a hgC
  have hex : ∀ i : KernelComponent (rootCharHom a),
      ∃ i', (componentRootSpan L (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
        componentRootSpan L (rootCharHom a) i' := by
    intro i
    obtain ⟨i', hi'⟩ := exists_weyl_image_component (K := L) a hw i
    exact ⟨i', by rw [hgmw]; exact map_conj_componentRootSpan (K := L) a hw hm hi'⟩
  let φ : KernelComponent (rootCharHom a) → KernelComponent (rootCharHom a) :=
    fun i => Classical.choose (hex i)
  have hφ : ∀ i : KernelComponent (rootCharHom a),
      (componentRootSpan L (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
        componentRootSpan L (rootCharHom a) (φ i) :=
    fun i => Classical.choose_spec (hex i)
  have hinj : Function.Injective φ := by
    intro i j hij
    refine ntpS2_componentRootSpan_injective (L := L) a ?_
    refine Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _) ?_
    rw [hφ i, hφ j, hij]
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product Tag.E6 L (rootCharHom a)).2.1
  refine ⟨Equiv.ofBijective φ ⟨hinj, Finite.surjective_of_injective hinj⟩, fun i => ?_⟩
  change (componentRootSpan L (rootCharHom a) i).map (MulAut.conj g).toMonoidHom =
    componentRootSpan L (rootCharHom a) (φ i)
  exact hφ i

end CFSG.StandardType.NTPlane

end

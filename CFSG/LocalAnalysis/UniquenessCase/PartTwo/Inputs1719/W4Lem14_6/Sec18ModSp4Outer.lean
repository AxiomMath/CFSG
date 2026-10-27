module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModSp4OuterRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Aut
public import CFSG.Quasithin.Background.SmithD37Lin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer

open CFSG.QuasithinUnique.Setup.X7b CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem three_mul_le_dispRank_of_not_inner {U : Type} [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (S : Subgroup (MulAut U)) (n : ℕ) (hSp : IsSp4 ↥S n)
    (hodd : Odd n) {t : MulAut U} (htS : t ∈ Subgroup.normalizer (S : Set (MulAut U)))
    (htord : orderOf t = 2)
    (hout : ¬ ∃ s : MulAut U, s ∈ S ∧ ∀ x ∈ S, t * x * t⁻¹ = s * x * s⁻¹) :
    letI : Module (ZMod 2) (Additive U) := CFSG.Quasithin.SmithD37.zmodModule hU
    3 * n ≤ dispRank (CFSG.Quasithin.SmithD37.autLin hU t) := by
  classical
  letI : Module (ZMod 2) (Additive U) := CFSG.Quasithin.SmithD37.zmodModule hU
  haveI : Finite (Additive U) := inferInstanceAs (Finite U)
  haveI : Module.Finite (ZMod 2) (Additive U) := Module.Finite.of_finite
  obtain ⟨hn2, K, hfield, hfin, hchar, hKcard, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  letI := hfield
  letI := hfin
  letI := hchar
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hKcard]
  let L := CFSG.Quasithin.SmithD37.autLin hU
  let ρS : ↥S →* (Additive U ≃ₗ[ZMod 2] Additive U) := L.toMonoidHom.comp S.subtype
  let π : Representation (ZMod 2) (antiSp K) (Additive U) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := Additive U)).comp
      (ρS.comp e.symm.toMonoidHom)
  have hπ : Function.Injective π := by
    intro g h hgh
    have h1 : ρS (e.symm g) = ρS (e.symm h) := LinearEquiv.toLinearMap_injective hgh
    have h2 : ((e.symm g : ↥S) : MulAut U) = (e.symm h : ↥S) := L.injective h1
    exact e.symm.injective (Subtype.ext h2)
  have ha : orderOf (L t) = 2 := by rw [MulEquiv.orderOf_eq]; exact htord
  let b : ↥(Subgroup.normalizer (S : Set (MulAut U))) := ⟨t, htS⟩
  let α : MulAut (antiSp K) := MulAut.congr e (K148.AutAux.condHom S b)
  have hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
    intro h
    obtain ⟨l, hl, hl'⟩ := K148.AutAux.inducesInnerOn_of_mem_inner e h
    exact hout ⟨l, hl, hl'⟩
  have hnorm : ∀ (g : antiSp K) (w : Additive U), L t (π g ((L t).symm w)) = π (α g) w := by
    intro g w
    have h1 : e.symm (α g) = K148.AutAux.condHom S b (e.symm g) := by
      simp [α, MulAut.congr_apply]
    have h2 : ((e.symm (α g) : ↥S) : MulAut U) = t * (e.symm g : MulAut U) * t⁻¹ := by
      rw [h1]
      rfl
    show L t (L (e.symm g : MulAut U) ((L t).symm w)) = L (e.symm (α g) : MulAut U) w
    rw [h2, map_mul, map_mul, map_inv]
    rfl
  exact outer_involution_displacement_ge hn2 (Nat.odd_iff.mp hodd) hKf π hπ (L t) ha α hα hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.Sp4Outer

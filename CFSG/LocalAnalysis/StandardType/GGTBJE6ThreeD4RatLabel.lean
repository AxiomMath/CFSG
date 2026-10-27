module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeD4Roots
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Reduce
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Base
public import CFSG.Models.Transport
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.TableCRes

theorem ggHasLabel_quotCenter_of_central_cover {J K : Type} [Group J] [Group K]
    (hJ : Group.IsPerfect J) (f : J →* K) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center J) {lab : LargeEvenLabel}
    (h : GGHasLabel lab (K ⧸ Subgroup.center K)) : GGHasLabel lab (J ⧸ Subgroup.center J) := by
  have hc : Subgroup.center J = ((QuotientGroup.mk' (Subgroup.center K)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hJ f hf hker).symm
  let e : J ⧸ Subgroup.center J ≃* K ⧸ Subgroup.center K :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨g⟩ => ⟨e.trans g⟩) h

theorem e6D4_label_of_rationalComponent
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.E6 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hqi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hD4 : ∃ v : WeylGroup Tag.E6, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 {j | j ∉ ({0, 5} : Finset (Fin 6))})
    (hkind : twistKindOf S.ρ (componentRoots (rootCharHom a) i) = TwistKind.inner) :
    ∃ m : ℕ, 1 ≤ m ∧ GGHasLabel (⟨.D, 4, m⟩ : LargeEvenLabel)
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  let a' : PUnit.{1} → Fin Tag.E6.rank → Lˣ := fun _ => a
  have hT' : ∀ u, rootDiagUnit Tag.E6 (a' u) ∈ S.D.torus := fun _ => hT
  have hap' : ∀ u j, a' u j ^ p = 1 := fun _ j => hap j
  have hK : CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : PUnit.{1} => rootDiagUnit Tag.E6 (a' u))) := by
    have hrange : (Set.range fun u : PUnit.{1} => rootDiagUnit Tag.E6 (a' u)) =
        {rootDiagUnit Tag.E6 a} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        rfl
      · intro hz
        exact ⟨PUnit.unit, hz.symm⟩
    rw [hrange]
    exact CFSG.HardMathSupport.Dickson.Sec6.isComponentOf_rationalComponent S hT i hqi
  obtain ⟨i', hi'⟩ := exists_componentRoots_eq (kernelRoots_famChar_punit_eq a).symm i
  have hspan : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (famOrbit S.ρ a' i') := by
    have hforb : famOrbit S.ρ a' i' = rationalRoots S.ρ (rootCharHom a) i := by
      ext γ
      simp only [famOrbit, rationalRoots, Set.mem_setOf_eq]
      rw [hi']
    rw [hforb]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨n, -, hlab⟩ := langFamilyCompLabel_exc (Or.inl rfl) S hp hp2 a' hT' hap' hK i' hspan
  have hΨ : componentRoots (famCharHom a') i' = componentRoots (rootCharHom a) i := hi'.symm
  rw [hΨ] at hlab
  obtain ⟨v, hv⟩ := hD4
  have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by
    rw [hv]
    exact e6D4_compRank_smul v
  have hN : (componentRoots (rootCharHom a) i).ncard = 24 := by
    rw [hv]
    exact e6D4_ncard_smul v
  rw [hr, hN, hkind] at hlab
  have hlabel : componentLabel 4 24 TwistKind.inner n = (⟨.D, 4, n⟩ : LargeEvenLabel) := by
    simp [componentLabel]
  rw [hlabel] at hlab
  obtain ⟨hΛ, -, hGL, -⟩ := hlab
  exact ⟨n, hΛ.1, hGL⟩

end CFSG.StandardType

end

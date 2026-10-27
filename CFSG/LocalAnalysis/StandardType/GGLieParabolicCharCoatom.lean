module

public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.StandardType

open Subgroup CFSG

variable {G : Type*} [Group G] {p : ℕ}

theorem isCharacteristicP_of_normalPSubgroup_centralizer_le {M Q : Subgroup G} (hQM : Q ≤ M)
    (hQn : (Q.subgroupOf M).Normal) (hQp : IsPGroup p Q)
    (hC : centralizer (Q : Set G) ⊓ M ≤ Q) : IsCharacteristicP p ↥M := by
  have hQcore : Q.subgroupOf M ≤ CFSG.pCore p ↥M :=
    le_sSup ⟨hQn, hQp.comap_of_injective _ M.subtype_injective⟩
  intro x hx
  apply hQcore
  refine Subgroup.mem_subgroupOf.2 (hC ⟨?_, x.2⟩)
  refine mem_centralizer_iff.2 fun u hu => ?_
  exact congrArg Subtype.val
    (mem_centralizer_iff.1 hx ⟨u, hQM hu⟩ (hQcore (Subgroup.mem_subgroupOf.2 hu)))

@[expose] def GGNormalizerOvergroupsChar (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ S X : Subgroup G, IsPGroup p S → ¬ p ∣ S.index → normalizer (S : Set G) ≤ X → X ≠ ⊤ →
    IsCharacteristicP p ↥X

theorem GGNormalizerOvergroupsChar.of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (h : GGNormalizerOvergroupsChar p H) : GGNormalizerOvergroupsChar p G := by
  intro S X hS hSi hNX hX
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hS' : IsPGroup p (S.map e.toMonoidHom) := hS.map _
  have hSi' : ¬ p ∣ (S.map e.toMonoidHom).index := by
    rwa [Subgroup.index_map_of_bijective e.bijective]
  have hNX' : normalizer ((S.map e.toMonoidHom : Subgroup H) : Set H) ≤ X.map e.toMonoidHom := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNX
  have hX' : X.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hX
    have h' := Subgroup.comap_map_eq_self_of_injective hinj X
    rw [htop, Subgroup.comap_top] at h'
    exact h'.symm
  exact CFSG.RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
    (X.equivMapOfInjective _ hinj).symm (h _ _ hS' hSi' hNX' hX')

theorem GGNormalizerOvergroupsChar.of_coatoms [Finite G] [Fact p.Prime]
    (h : ∀ S M : Subgroup G, IsPGroup p S → ¬ p ∣ S.index → normalizer (S : Set G) ≤ M →
      IsCoatom M → IsCharacteristicP p ↥M) : GGNormalizerOvergroupsChar p G := by
  intro S X hS hSi hNX hX
  obtain ⟨M, hM, hXM⟩ := (eq_top_or_exists_le_coatom X).resolve_left hX
  have hSX : S ≤ X := le_normalizer.trans hNX
  have hMchar : IsCharacteristicP p ↥M := h S M hS hSi (hNX.trans hXM) hM
  have hS' : IsPGroup p (S.subgroupOf M) := hS.comap_of_injective _ M.subtype_injective
  have hSi' : ¬ p ∣ (S.subgroupOf M).index := fun hd =>
    hSi (hd.trans (relIndex_dvd_index_of_le (hSX.trans hXM)))
  have hcore : CFSG.pCore p ↥M ≤ X.subgroupOf M := by
    refine (CFSG.fitting_pCore_le_sylow (hS'.toSylow hSi')).trans ?_
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.comap_mono hSX
  exact CFSG.RankThree.PartTwo.Sec14.isCharacteristicP_of_mulEquiv'
    (Subgroup.subgroupOfEquivOfLe hXM)
    (CFSG.RankThree.PartTwo.Sec14.isCharacteristicP_of_pCore_le (X.subgroupOf M) hMchar hcore)

end CFSG.StandardType

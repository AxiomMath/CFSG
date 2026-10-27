module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator

theorem ggTBJ_fixSubgroup_conj {G : Type*} [Group G] (g : G) :
    fixSubgroup (MulAut.conj g) = Subgroup.centralizer ({g} : Set G) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rw [MulAut.conj_apply] at h
    have h' : g * x = x * g := by
      have := congrArg (· * g) h
      simpa [mul_assoc] using this
    exact h'
  · intro h
    rw [MulAut.conj_apply]
    have hg := h g (Set.mem_singleton g)
    rw [hg]
    group

private theorem ggTBJ_native_quasisimple_aux {G : Type*} [Group G]
    (h : CFSG.Open.IsQuasisimple G) : CFSG.IsQuasisimple G :=
  ⟨⟨h.1⟩, h.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian G h⟩

private theorem ggTBJ_open_quasisimple_of_native_aux {G : Type*} [Group G]
    (h : CFSG.IsQuasisimple G) : CFSG.Open.IsQuasisimple G :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem ggTBJ_exists_component_lift_fix {L' H : Type} [Group L'] [Group H]
    (ψ : L' →* H) (hker : ψ.ker ≤ Subgroup.center L') (y : MulAut L') (d : H)
    (hyd : ∀ k, ψ (y k) = d * ψ k * d⁻¹) {S X : Subgroup H}
    (hS : IsComponentOf S X) (hSr : S ≤ ψ.range)
    (hSd : S ≤ Subgroup.centralizer ({d} : Set H))
    (hCX : ∀ c ∈ fixSubgroup y, ψ c ∈ X) :
    ∃ Q : Subgroup L', IsComponentOf Q (fixSubgroup y) ∧ Q.map ψ = S := by
  let C : Subgroup L' := fixSubgroup y
  let P : Subgroup L' := S.comap ψ
  let Q : Subgroup L' := ⁅P, P⁆
  haveI hSperf : Group.IsPerfect S := ⟨hS.2.2.1⟩
  have hCX' : C ≤ X.comap ψ := fun c hc => Subgroup.mem_comap.mpr (hCX c hc)
  have hPmap : P.map ψ = S := Subgroup.map_comap_eq_self hSr
  have hQle : Q ≤ C := by
    change ⁅P, P⁆ ≤ C
    rw [Subgroup.commutator_le]
    intro x hx z hz
    have hxS : ψ x ∈ S := Subgroup.mem_comap.mp hx
    have hzS : ψ z ∈ S := Subgroup.mem_comap.mp hz
    have h₁ : ψ x ∈ fixSubgroup (MulAut.conj d) := by
      rw [ggTBJ_fixSubgroup_conj]
      exact hSd hxS
    have h₂ : ψ z ∈ fixSubgroup (MulAut.conj d) := by
      rw [ggTBJ_fixSubgroup_conj]
      exact hSd hzS
    exact comm_mem_fixSubgroup ψ hker y (MulAut.conj d)
      (fun k => by rw [hyd k, MulAut.conj_apply]) h₁ h₂
  have hQmap : Q.map ψ = S := by
    change ⁅P, P⁆.map ψ = S
    rw [Subgroup.map_commutator, hPmap]
    exact Subgroup.commutator_eq_self
  have hQq : CFSG.Open.IsQuasisimple Q := by
    let r : P →* S := (ψ.domRestrict P).codRestrict S fun x => Subgroup.mem_comap.mp x.property
    have hsurj : Function.Surjective r := by
      intro s
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hSr s.property)
      refine ⟨⟨x, Subgroup.mem_comap.mpr (by rw [hx]; exact s.property)⟩, ?_⟩
      exact Subtype.ext hx
    have hker_r : r.ker ≤ Subgroup.center P := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      apply Subgroup.mem_center_iff.mpr
      intro y
      apply Subtype.ext
      have hxcenter : x.val ∈ Subgroup.center L' := by
        apply hker
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      exact Subgroup.mem_center_iff.mp hxcenter y.val
    have hder : CFSG.IsQuasisimple (commutator ↥P) :=
      CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective r hsurj hker_r
        (ggTBJ_native_quasisimple_aux hS.2.2)
    have hderOpen : CFSG.Open.IsQuasisimple (commutator ↥P) :=
      ggTBJ_open_quasisimple_of_native_aux hder
    rw [show Q = (commutator ↥P).map P.subtype from (Subgroup.map_subtype_commutator (H := P)).symm]
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      ((commutator ↥P).equivMapOfInjective P.subtype P.subtype_injective).symm hderOpen
  have hsub : IsSubnormal (P ⊓ C) C := by
    have h := (hS.2.1.comap ψ).inf C
    rw [inf_eq_right.mpr hCX'] at h
    exact h
  have hQnormalP : (Q.subgroupOf P).Normal := by
    change (⁅P, P⁆.subgroupOf P).Normal
    have hinst := (inferInstance : (⁅P, P⁆.subgroupOf (P ⊔ P)).Normal)
    rw [sup_idem] at hinst
    exact hinst
  have hQnormal : (Q.subgroupOf (P ⊓ C)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (le_inf (Subgroup.commutator_le_self P) hQle)]
    intro q hq g hg
    exact (Subgroup.normal_subgroupOf_iff (Subgroup.commutator_le_self P)).mp hQnormalP
      q hq g (Subgroup.mem_inf.mp hg).1
  have hQsub : IsSubnormal Q C :=
    IsSubnormal.step (le_inf (Subgroup.commutator_le_self P) hQle) hQnormal hsub
  exact ⟨Q, ⟨hQle, hQsub, hQq⟩, hQmap⟩

theorem ggTBJ_map_component_eq_fix {L' H : Type} [Group L'] [Group H]
    (ψ : L' →* H) (hker : ψ.ker ≤ Subgroup.center L') (y : MulAut L') (d : H)
    (hyd : ∀ k, ψ (y k) = d * ψ k * d⁻¹) {S X : Subgroup H}
    (hS : IsComponentOf S X) (hSr : S ≤ ψ.range)
    (hSd : S ≤ Subgroup.centralizer ({d} : Set H))
    (hCX : ∀ c ∈ fixSubgroup y, ψ c ∈ X)
    {J : Subgroup L'} (hJ : IsComponentOf J (fixSubgroup y))
    (hJl : ∀ Q : Subgroup L', IsComponentOf Q (fixSubgroup y) → Q ≤ J) :
    J.map ψ = S := by
  obtain ⟨Q, hQcomp, hQmap⟩ := ggTBJ_exists_component_lift_fix ψ hker y d hyd hS hSr hSd hCX
  have hQleJ : Q ≤ J := hJl Q hQcomp
  let e : Q.subgroupOf J ≃* Q := Subgroup.subgroupOfEquivOfLe hQleJ
  haveI : Group.IsPerfect Q := ⟨hQcomp.2.2.1⟩
  let : Group.IsPerfect (Q.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Nontrivial Q := CFSG.ComponentClassification.Quasisimple.nontrivial hQcomp.2.2
  haveI : Nontrivial (Q.subgroupOf J) := e.toEquiv.nontrivial
  have hQsubJ : IsSubnormal Q J := by
    have h := hQcomp.2.1.inf_of_le hJ.1
    rw [inf_eq_left.mpr hQleJ] at h
    exact h
  have htop : Q.subgroupOf J = ⊤ :=
    (CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hJ.2.2
      (Q.subgroupOf J)
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hQsubJ.subgroupOf)
      ).resolve_left ((Q.subgroupOf J).nontrivial_iff_ne_bot.mp inferInstance)
  have hQeqJ : Q = J := by
    have h := congrArg (Subgroup.map J.subtype) htop
    simpa only [Subgroup.map_subgroupOf_eq_of_le hQleJ, Subgroup.map_top,
      Subgroup.range_subtype] using h
  rw [← hQeqJ]
  exact hQmap

theorem ggTBJ_map_component_eq {L' H : Type} [Group L'] [Group H]
    (ψ : L' →* H) (hker : ψ.ker ≤ Subgroup.center L') (u : L') {S X : Subgroup H}
    (hS : IsComponentOf S X) (hSr : S ≤ ψ.range)
    (hSu : S ≤ Subgroup.centralizer ({ψ u} : Set H))
    (hCX : ∀ c ∈ Subgroup.centralizer ({u} : Set L'), ψ c ∈ X)
    {J : Subgroup L'} (hJ : IsComponentOf J (Subgroup.centralizer ({u} : Set L')))
    (hJl : ∀ Q : Subgroup L',
      IsComponentOf Q (Subgroup.centralizer ({u} : Set L')) → Q ≤ J) :
    J.map ψ = S := by
  rw [← ggTBJ_fixSubgroup_conj] at hJ hJl hCX
  exact ggTBJ_map_component_eq_fix ψ hker (MulAut.conj u) (ψ u)
    (fun k => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]) hS hSr hSu hCX hJ hJl

end CFSG.StandardType

end

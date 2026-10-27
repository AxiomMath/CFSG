module

public import CFSG.RankThree.PartOne.S11d.ThetaCalc
public import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
public import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.Timmesfeld.Final.Simple
public import CFSG.RankThree.PartOne.S11d.Common
public import CFSG.RankThree.PartOne.S12.InputsEleven

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fixedRes_isQuasisimple {p : ℕ} {J : Subgroup G} {u : G} (h : InducesFieldAut p u J) :
    CFSG.IsQuasisimple ↥(inSubgroup perfectResidual (J ⊓ centralizer ({u} : Set G))) := by
  obtain ⟨-, -, -, t, n, f, -, -, hfix⟩ := h
  refine S11d.isQuasisimple_of_perfect_of_simple
    (EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _) ?_
  rcases hfix with hL | ⟨-, -, -, hL⟩
  · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL
  · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL

omit [Finite G] in
theorem inSubgroup_perfectResidual_le (X : Subgroup G) : inSubgroup perfectResidual X ≤ X :=
  Subgroup.map_subtype_le _

theorem exists_thetaComponent_ge_fixedRes (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) {c f : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hfA : f ∈ A)
    (hf1 : f ≠ 1) {J : Subgroup G} (hJ : J ∈ thetaComponentsAt p c)
    (hq : CFSG.IsQuasisimple ↥(inSubgroup perfectResidual (J ⊓ centralizer ({f} : Set G)))) :
    ∃ K₀ ∈ thetaComponentsAt p f,
      inSubgroup perfectResidual (J ⊓ centralizer ({f} : Set G)) ≤ K₀ := by
  classical
  have hp : p.Prime := sectionTenSetup_prime h
  have hp3 : 3 < p := sectionTenSetup_three_lt h
  have hAe : IsElementaryAbelian p A := h.2.2.2.2.2.2.1
  have : IsSimpleGroup G := h.1
  set E := inSubgroup perfectResidual (J ⊓ centralizer ({f} : Set G)) with hE
  set H := centralizer ({f} : Set G) with hH
  have hcf : c * f = f * c := congrArg Subtype.val (hAe.is_comm.comm ⟨c, hcA⟩ ⟨f, hfA⟩)
  have hcH : c ∈ H := EmbeddingFixedResidual.commute_mem_centralizer hcf
  set x : H := ⟨c, hcH⟩ with hx
  have hxord : orderOf x = p := by
    rw [← Subgroup.orderOf_coe]
    exact EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hHK : CFSG.IsKGroup H :=
    h.2.2.1 _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple h.2.1 hf1)
  have hHE : CFSG.Assembly.evenRank H ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans (sectionTenSetup_evenRank_eq h).le
  have hJc : J ≤ centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.mp hJ).1
  have hEJ : E ≤ J ⊓ H := inSubgroup_perfectResidual_le _
  have hEH : E ≤ H := hEJ.trans inf_le_right
  have hEJ' : E ≤ J := hEJ.trans inf_le_left
  have hEc : E ≤ centralizer ({c} : Set G) := hEJ'.trans hJc
  set Cx := centralizer ({x} : Set H) with hCx
  have hle : E.subgroupOf H ≤ Cx := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEc (Subgroup.mem_subgroupOf.mp hg))
  have hmem : (E.subgroupOf H).subgroupOf Cx ∈ thetaComponents p ↥Cx := by
    apply mem_thetaComponents_of_quasisimple hp
    · let e : ↥((E.subgroupOf H).subgroupOf Cx) ≃* ↥E :=
        (Subgroup.subgroupOfEquivOfLe hle).trans (Subgroup.subgroupOfEquivOfLe hEH)
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    · have hJsn : (J.subgroupOf (centralizer ({c} : Set G))).IsSubnormal :=
        isSubnormal_of_mem_thetaComponentsAt hJ
      let ι' : ↥Cx →* ↥(centralizer ({c} : Set G)) :=
        ((H.subtype).comp Cx.subtype).codRestrict (centralizer ({c} : Set G)) (by
          intro g
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2)))
      set Z' : Subgroup ↥Cx := (J.subgroupOf (centralizer ({c} : Set G))).comap ι' with hZ'
      have hZ'sn : Z'.IsSubnormal := hJsn.comap ι'
      have hZ'mem : ∀ g : ↥Cx, g ∈ Z' ↔ ((g : H) : G) ∈ J := fun g => Iff.rfl
      set Z : Subgroup ↥Cx := (E.subgroupOf H).subgroupOf Cx with hZ
      have hZmem : ∀ g : ↥Cx, g ∈ Z ↔ ((g : H) : G) ∈ E := fun g => Iff.rfl
      have hZZ' : Z ≤ Z' := fun g hg => (hZ'mem g).mpr (hEJ' ((hZmem g).mp hg))
      have hnorm : (Z.subgroupOf Z').Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hn' : (((n : ↥Cx) : H) : G) ∈ E := (hZmem _).mp (Subgroup.mem_subgroupOf.mp hn)
        have hg' : (((g : ↥Cx) : H) : G) ∈ J ⊓ H :=
          ⟨(hZ'mem _).mp g.2, ((g : ↥Cx) : H).2⟩
        rw [Subgroup.mem_subgroupOf, hZmem]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact conj_mem_inSubgroup_perfectResidual hg' hn'
      exact Subgroup.IsSubnormal.trans hZZ' hnorm.isSubnormal hZ'sn
  have hY' : E.subgroupOf H ∈ thetaComponentsAt p x := mem_thetaComponentsAt_iff.mpr ⟨hle, hmem⟩
  obtain ⟨K₁, hK₁, hEK⟩ := local_theta_component_embedding_frontier hS H hHK hHE p hp hp3 x hxord _
    hY'
  refine ⟨K₁.map H.subtype, ⟨K₁, hK₁, rfl⟩, fun e he => ?_⟩
  exact ⟨⟨e, hEH he⟩, hEK (Subgroup.mem_subgroupOf.mpr he), rfl⟩

end CFSG.RankThree.PartOne

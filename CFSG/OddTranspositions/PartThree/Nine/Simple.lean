module

public import CFSG.OddTranspositions.PartThree.Nine.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.Foundations.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.RankThree.PartOne.FIS.VRelation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem commutator_le_of_forall_inv_mul_mem {M : Subgroup G} [M.Normal]
    (hgen : Subgroup.closure D = ⊤) {u : G} (hu : u ∈ D) (hcos : ∀ v ∈ D, u⁻¹ * v ∈ M) :
    commutator G ≤ M := by
  rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have himg : (QuotientGroup.mk' M) '' D = {QuotientGroup.mk' M u} := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [Set.mem_singleton_iff, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      simpa using M.inv_mem (hcos v hv)
    · rintro rfl
      exact ⟨u, hu, rfl⟩
  have htop : Subgroup.zpowers (QuotientGroup.mk' M u) = ⊤ := by
    rw [Subgroup.zpowers_eq_closure, ← himg, ← MonoidHom.map_closure, hgen,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective M)]
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : x ∈ Subgroup.zpowers (QuotientGroup.mk' M u) := htop ▸ Subgroup.mem_top x
  have hy : y ∈ Subgroup.zpowers (QuotientGroup.mk' M u) := htop ▸ Subgroup.mem_top y
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self _ i j).eq

theorem lemma9_2 : Lemma9_2 := by
  intro G _ _ D hC hH hsimple
  have hS := hC.setup
  have hrad := hH.solv
  obtain ⟨M, hM⟩ := exists_minimalNormal hS
  have := hM.1
  have hMs : IsSimpleGroup M := hsimple M hM
  have hMsol : ¬ Group.IsSolvable M := fun h => hM.2.1 (hrad M hM.1 h)
  have hMle : M ≤ commutator G :=
    CFSG.GroupTheory.ThreeTranspositions.le_commutator_of_isSimpleGroup_of_not_isSolvable hMs hMsol
  have hle : commutator G ≤ M := by
    rcases simple_minimal_cases hS hrad hM hMs with hDM | ⟨-, hcong⟩
    · have hMtop : M = ⊤ := by
        rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
        exact hDM
      rw [hMtop]
      exact le_top
    · obtain ⟨u, hu⟩ := hS.nonempty
      refine commutator_le_of_forall_inv_mul_mem hS.gen hu fun v hv => ?_
      have hclosed : ∀ x ∈ {x : G | x ∈ D ∧ u⁻¹ * x ∈ M}, ∀ y ∈ D, Commute x y →
          y ∈ {x : G | x ∈ D ∧ u⁻¹ * x ∈ M} := by
        rintro x ⟨hxD, hxM⟩ y hyD hxy
        refine ⟨hyD, ?_⟩
        have hxy' : u⁻¹ * y = (u⁻¹ * x) * (x⁻¹ * y) := by group
        rw [hxy']
        exact M.mul_mem hxM (hcong x hxD y hyD hxy)
      exact (mem_of_reach hclosed ⟨hu, by simp⟩
        (reach_of_not_disconnected hC.conn hu hv)).2
  rw [le_antisymm hle hMle]
  exact hMs

end CFSG.OddTranspositions.PartThree.Nine

module

import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S10.FiveCriticalOddCore
import CFSG.RankThree.GroupTheory.SteinbergBKOddCoreFixedResidual
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_fixedPointSubgroup_eq {L U : Subgroup G} [MulDistribMulAction U L]
    (hact : ∀ (u : U) (l : L), ((u • l : L) : G) = (u : G) * l * (u : G)⁻¹) :
    (fixedPointSubgroup U L).map L.subtype = L ⊓ centralizer (U : Set G) := by
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have h := congrArg Subtype.val (hl ⟨u, hu⟩)
    rw [hact] at h
    calc u * (l : G) = u * l * u⁻¹ * u := by group
      _ = l * u := by rw [h]
  · rintro ⟨hgL, hgC⟩
    refine ⟨⟨g, hgL⟩, fun u => Subtype.ext ?_, rfl⟩
    rw [hact]
    have h := Subgroup.mem_centralizer_iff.mp hgC u u.2
    calc (u : G) * g * (u : G)⁻¹ = g * u * (u : G)⁻¹ := by rw [h]
      _ = g := by group

theorem map_inSubgroup_perfectResidual_fixedPointSubgroup {L U : Subgroup G}
    [MulDistribMulAction U L]
    (hact : ∀ (u : U) (l : L), ((u • l : L) : G) = (u : G) * l * (u : G)⁻¹) :
    (inSubgroup perfectResidual (fixedPointSubgroup U L)).map L.subtype =
      inSubgroup perfectResidual (L ⊓ centralizer (U : Set G)) := by
  rw [SteinbergBY.map_inSubgroup_perfectResidual_of_injective L.subtype L.subtype_injective,
    map_fixedPointSubgroup_eq hact]

omit [Finite G] in
theorem isQuasisimple_of_map_subtype {L : Subgroup G} {P : Subgroup L}
    (h : CFSG.IsQuasisimple ↥(P.map L.subtype)) : CFSG.IsQuasisimple ↥P :=
  LocalCores.isQuasisimple_of_mulEquiv (P.equivMapOfInjective L.subtype L.subtype_injective).symm h

theorem odd_core_fixed_residual_ambient {p : ℕ} (hp : p.Prime) {L U : Subgroup G}
    (hUN : U ≤ normalizer (L : Set G)) (hLperf : Group.IsPerfect L)
    (hLO : haveI := oddThetaCore_subgroupOf_normal p L;
      CFSG.IsQuasisimple (L ⧸ (oddThetaCore p L).subgroupOf L))
    (hUp : IsPGroup p U) (hUO : U ≤ normalizer (oddThetaCore p L : Set G))
    (hUtriv : ∀ u ∈ U, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ oddThetaCore p L) :
    L = oddThetaCore p L ⊔ inSubgroup perfectResidual (L ⊓ centralizer (U : Set G)) ∧
    L ⊓ centralizer (U : Set G) = (oddThetaCore p L ⊓ centralizer (U : Set G)) ⊔
        inSubgroup perfectResidual (L ⊓ centralizer (U : Set G)) ∧
    (∀ R : Subgroup G, R ≤ L ⊓ centralizer (U : Set G) → IsPGroup 2 R →
        R ≤ inSubgroup perfectResidual (L ⊓ centralizer (U : Set G))) ∧
    (CFSG.IsQuasisimple ↥(inSubgroup perfectResidual (L ⊓ centralizer (U : Set G))) →
      ∀ {q : ℕ}, q.Prime → ∀ D : Subgroup G, D ≤ L → (D.subgroupOf L).Normal → IsPGroup q D →
        ⁅L, D⁆ ≠ ⊥ → ∀ z ∈ inSubgroup perfectResidual (L ⊓ centralizer (U : Set G)),
        (∃ k : ℕ, ∀ d ∈ D, (z * d * z⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D) →
        z ∈ centralizer (inSubgroup perfectResidual (L ⊓ centralizer (U : Set G)) : Set G)) := by
  classical
  have hOn := oddThetaCore_subgroupOf_normal p L
  let _ : MulDistribMulAction U L := conjActionOn hUN
  have hact : ∀ (u : U) (l : L), ((u • l : L) : G) = (u : G) * l * (u : G)⁻¹ := fun _ _ => rfl
  set O : Subgroup L := (oddThetaCore p L).subgroupOf L with hO
  have hOmap : O.map L.subtype = oddThetaCore p L :=
    Subgroup.map_subgroupOf_eq_of_le (oddThetaCore_le p L)
  have hUO' : ∀ u : U, ∀ y ∈ O, u • y ∈ O := by
    intro u y hy
    rw [hO, Subgroup.mem_subgroupOf] at hy ⊢
    rw [hact]
    exact (Subgroup.mem_normalizer_iff.mp (hUO u.2) y).mp hy
  have hUtriv' : ∀ u : U, ∀ y : L, y⁻¹ * (u • y) ∈ O := by
    intro u y
    apply hOn.mem_comm
    rw [hO, Subgroup.mem_subgroupOf]
    have h := hUtriv u u.2 y y.2
    have e : ((u • y * y⁻¹ : L) : G) = (u : G) * y * (u : G)⁻¹ * (y : G)⁻¹ := by
      rw [Subgroup.coe_mul, hact]
      rfl
    rw [e]
    exact h
  obtain ⟨h1, h2, h3, h4⟩ :=
    SteinbergBK.odd_core_fixed_residual_retains_two_subgroups_and_scalar_center hp hLperf O
      (oddThetaCore_subgroupOf_isSolvable hp L) (oddThetaCore_subgroupOf_odd p L)
      (oddThetaCore_subgroupOf_not_dvd hp L) hLO hUp hUO' hUtriv'
  have hFix := map_fixedPointSubgroup_eq (L := L) (U := U) hact
  have hP := map_inSubgroup_perfectResidual_fixedPointSubgroup (L := L) (U := U) hact
  have hTop : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := congrArg (Subgroup.map L.subtype) h1
    rw [Subgroup.map_sup, hOmap, hP, hTop] at h
    exact h.symm
  · have h := congrArg (Subgroup.map L.subtype) h2
    rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ L.subtype L.subtype_injective, hOmap, hP,
      hFix] at h
    have e : L ⊓ centralizer (U : Set G) ⊓ oddThetaCore p L =
        oddThetaCore p L ⊓ centralizer (U : Set G) := by
      rw [inf_comm (L ⊓ centralizer (U : Set G)), ← inf_assoc,
        inf_eq_left.mpr (oddThetaCore_le p L)]
    rw [e] at h
    exact h
  · intro R hRC hR2
    have hRL : R ≤ L := hRC.trans inf_le_left
    have hle : R.subgroupOf L ≤ fixedPointSubgroup U L := fun r hr =>
      (Subgroup.mem_map_iff_mem L.subtype_injective).mp (hFix ▸ hRC hr)
    have h := Subgroup.map_mono (f := L.subtype) (h3 (R.subgroupOf L) hle hR2.comap_subtype)
    rw [Subgroup.map_subgroupOf_eq_of_le hRL, hP] at h
    exact h
  · intro hPq q hq D hDL hDn hDq hLD z hz hk
    have hPq' : CFSG.IsQuasisimple ↥(inSubgroup perfectResidual (fixedPointSubgroup U L)) :=
      isQuasisimple_of_map_subtype (L := L) (by
        refine LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hP.symm) hPq)
    have hDmap : (D.subgroupOf L).map L.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDL
    have hLD' : ⁅(⊤ : Subgroup L), D.subgroupOf L⁆ ≠ ⊥ := by
      intro h
      apply hLD
      have h' := congrArg (Subgroup.map L.subtype) h
      rwa [Subgroup.map_commutator, hTop, hDmap, Subgroup.map_bot] at h'
    have hz' : z ∈ (inSubgroup perfectResidual (fixedPointSubgroup U L)).map L.subtype := by
      rw [hP]
      exact hz
    obtain ⟨z', hz'P, rfl⟩ := hz'
    obtain ⟨k, hk⟩ := hk
    have hΦ : (inSubgroup frattini (D.subgroupOf L)).map L.subtype = inSubgroup frattini D := by
      rw [← Torsion37.inSubgroup_frattini_map L.subtype L.subtype_injective, hDmap]
    have hcen := h4 hPq' hq (D.subgroupOf L) hDn hDq.comap_subtype hLD' z' hz'P
      ⟨k, fun d hd => by
        refine (Subgroup.mem_map_iff_mem L.subtype_injective).mp ?_
        rw [hΦ]
        exact hk d hd⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ hg
    rw [← hP] at hg
    obtain ⟨g', hg'P, rfl⟩ := hg
    have h := congrArg (fun w : inSubgroup perfectResidual (fixedPointSubgroup U L) =>
      (((w : L)) : G)) (Subgroup.mem_center_iff.mp hcen ⟨g', hg'P⟩)
    exact h

theorem theta_component_fixed_residual_ambient {p : ℕ} (hp : p.Prime) {L U : Subgroup G}
    (hUN : U ≤ normalizer (L : Set G))
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L)) (hUp : IsPGroup p U)
    (hUtriv : ∀ u ∈ U, ∀ l ∈ L,
      u * l * u⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) L) :
    (inSubgroup perfectResidual (L ⊓ centralizer (U : Set G))).subgroupOf
        (L ⊓ centralizer (U : Set G)) ∈ thetaComponents p ↥(L ⊓ centralizer (U : Set G)) := by
  let _ : MulDistribMulAction U L := conjActionOn hUN
  have hact : ∀ (u : U) (l : L), ((u • l : L) : G) = (u : G) * l * (u : G)⁻¹ := fun _ _ => rfl
  have hNn : (aschbacherSolvableCore p L).Normal := inferInstance
  have htriv : ∀ (u : U) (l : L),
      ((u • l : L) : L ⧸ aschbacherSolvableCore p L) = (l : L ⧸ aschbacherSolvableCore p L) := by
    intro u l
    rw [QuotientGroup.eq]
    apply hNn.mem_comm
    have h : (u • l) * l⁻¹ ∈ aschbacherSolvableCore p L :=
      (Subgroup.mem_map_iff_mem L.subtype_injective).mp (hUtriv u u.2 l l.2)
    have e : l * (u • l)⁻¹ = ((u • l) * l⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h
  obtain ⟨-, hmem⟩ := theta_component_trivial_quotient_action_fixed_residual hp hLq hUp htriv
  have hFix := map_fixedPointSubgroup_eq (L := L) (U := U) hact
  set F := fixedPointSubgroup U L with hF
  set Y := L ⊓ centralizer (U : Set G) with hY
  let e : ↥F ≃* ↥Y :=
    (F.equivMapOfInjective L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hFix)
  have h1 : (perfectResidual F).map e.toMonoidHom = perfectResidual Y :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq e.toMonoidHom e.surjective
  have h2 : (inSubgroup perfectResidual Y).subgroupOf Y = perfectResidual Y :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  rw [h2, ← h1]
  exact map_mulEquiv_mem_thetaComponents hp e hmem

end CFSG.RankThree.PartOne.FiveCritical

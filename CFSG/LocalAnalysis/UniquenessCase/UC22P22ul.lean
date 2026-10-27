module

import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22p22u_map_layer_le_commutator {Q : Type*} [Group Q] (H : Subgroup Q) :
    (CFSG.layer ↥H).map H.subtype ≤ ⁅H, H⁆ := by
  calc (CFSG.layer ↥H).map H.subtype
      = Subgroup.map H.subtype ⁅CFSG.layer ↥H, CFSG.layer ↥H⁆ := by rw [CFSG.LocalCores.layer_perfect]
    _ = ⁅(CFSG.layer ↥H).map H.subtype, (CFSG.layer ↥H).map H.subtype⁆ := map_commutator _ _ _
    _ ≤ ⁅H, H⁆ := commutator_mono (map_subtype_le _) (map_subtype_le _)

theorem uc22p22u_inf_centralizer_fstar_le {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q) :
    N ⊓ centralizer ((((CFSG.fittingSubgroup ↥N).map N.subtype) ⊔ ((CFSG.layer ↥N).map N.subtype) :
      Subgroup Q) : Set Q) ≤ (CFSG.fittingSubgroup ↥N).map N.subtype ⊔ (CFSG.layer ↥N).map N.subtype := by
  have h := CFSG.SignalizerFunctorTheorem.McBride.inf_centralizer_generalizedFitting_le N
  rwa [CFSG.generalizedFitting.eq_sup, Subgroup.map_sup] at h

theorem uc22p22u_isNilpotent_of_isPGroup_map {Q B : Type*} [Group Q] [Finite Q] [Group B] (f : Q →* B)
    (p : ℕ) [Fact p.Prime] (U : Subgroup Q) (hp : IsPGroup p ↥(U.map f))
    (hc : ∀ u ∈ U, f u = 1 → ∀ v ∈ U, v * u = u * v) : Group.IsNilpotent ↥U := by
  haveI : Finite ↥(U.map f) := Finite.of_surjective (f.subgroupMap U) (f.subgroupMap_surjective U)
  haveI : Group.IsNilpotent ↥(U.map f) := hp.isNilpotent
  refine Subgroup.isNilpotent_of_ker_le_center (f.subgroupMap U) fun x hx => ?_
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (hc x.1 x.2 (congrArg Subtype.val hx) y.1 y.2)

theorem uc22p22u_exists_le_pCore_map_eq {Q B : Type*} [Group Q] [Finite Q] [Group B] (f : Q →* B)
    (p : ℕ) [Fact p.Prime] (U : Subgroup Q) [U.Normal] (hU : Group.IsNilpotent ↥U)
    (hp : IsPGroup p ↥(U.map f)) :
    ∃ S : Subgroup Q, S ≤ U ∧ S ≤ CFSG.pCore p Q ∧ S.map f = U.map f := by
  haveI : Finite ↥(U.map f) := Finite.of_surjective (f.subgroupMap U) (f.subgroupMap_surjective U)
  let P : Sylow p ↥U := default
  let P' : Sylow p ↥(U.map f) := P.mapSurjective (f.subgroupMap_surjective U)
  have hPtop : (P' : Subgroup ↥(U.map f)) = ⊤ := (P'.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  refine ⟨P.map U.subtype, map_subtype_le _, Sylow.map_le_pCore inferInstance hU p P, ?_⟩
  refine le_antisymm (map_mono (map_subtype_le _)) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hmem : (⟨f u, mem_map_of_mem f hu⟩ : ↥(U.map f)) ∈ (P' : Subgroup ↥(U.map f)) := by
    rw [hPtop]
    exact mem_top _
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨a, ha, hfa⟩ := hmem
  exact ⟨a.1, ⟨a, ha, rfl⟩, congrArg Subtype.val hfa⟩

theorem uc22p22u_pCore_commutator_le_image {Q B : Type*} [Group Q] [Finite Q] [Group B] (φ : Q →* B)
    (hφ : Function.Surjective φ) (N : Subgroup Q) [N.Normal] (hN : φ.ker = N) (p : ℕ) (hp : p.Prime)
    (h118 : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤
      centralizer ((((CFSG.fittingSubgroup ↥N).map N.subtype) ⊔ ((CFSG.layer ↥N).map N.subtype) :
        Subgroup Q) : Set Q) ⊔ (CFSG.layer ↥N).map N.subtype) :
    ∀ b ∈ pCoreOf p ⁅(⊤ : Subgroup B), ⊤⁆,
      ∃ y ∈ CFSG.pCore p Q ⊓ ⁅(⊤ : Subgroup Q), ⊤⁆, φ y = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite B := Finite.of_surjective φ hφ
  haveI : (CFSG.layer ↥N).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : ((CFSG.layer ↥N).map N.subtype).Normal := inferInstance
  haveI : ((CFSG.fittingSubgroup ↥N).map N.subtype).Normal := inferInstance
  set F : Subgroup Q := (CFSG.fittingSubgroup ↥N).map N.subtype
  set E : Subgroup Q := (CFSG.layer ↥N).map N.subtype
  set C : Subgroup Q := centralizer ((F ⊔ E : Subgroup Q) : Set Q)
  set D : Subgroup B := ⁅(⊤ : Subgroup B), ⊤⁆
  set Op : Subgroup B := pCoreOf p D
  have hEN : E ≤ N := map_subtype_le _
  have hEQ : E ≤ ⁅(⊤ : Subgroup Q), ⊤⁆ :=
    (uc22p22u_map_layer_le_commutator N).trans (commutator_mono le_top le_top)
  haveI : Op.Normal := by
    change ((CFSG.pCore p ↥D).map D.subtype).Normal
    infer_instance
  have hOpp : IsPGroup p ↥Op := CFSG.pCore_isPGroup.map D.subtype
  have hOpD : Op ≤ D := map_subtype_le _
  let U : Subgroup Q := C ⊓ ⁅(⊤ : Subgroup Q), ⊤⁆ ⊓ Op.comap φ
  haveI : U.Normal := inferInstance
  have hUOp : U.map φ ≤ Op := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hpU : IsPGroup p ↥(U.map φ) := hOpp.to_le hUOp
  have hcent : ∀ u ∈ U, φ u = 1 → ∀ v ∈ U, v * u = u * v := by
    intro u hu hφu v hv
    have huN : u ∈ N := hN ▸ hφu
    have hmem : u ∈ F ⊔ E := uc22p22u_inf_centralizer_fstar_le N ⟨huN, hu.1.1⟩
    exact (mem_centralizer_iff.mp hv.1.1 u hmem).symm
  have hnil : Group.IsNilpotent ↥U := uc22p22u_isNilpotent_of_isPGroup_map φ p U hpU hcent
  have himg : ∀ b ∈ Op, ∃ u ∈ U, φ u = b := by
    intro b hb
    have hbD : b ∈ Subgroup.map φ ⁅(⊤ : Subgroup Q), ⊤⁆ := by
      rw [map_commutator, map_top_of_surjective φ hφ]
      exact hOpD hb
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hbD
    obtain ⟨c, hc, e, he, hce⟩ := mem_sup_of_normal_right.mp (h118 ha)
    have hφe : φ e = 1 := by
      have : e ∈ φ.ker := hN ▸ hEN he
      exact this
    have hφc : φ c = b := by
      rw [← hab, ← hce, map_mul, hφe, mul_one]
    have hcQ : c ∈ (⁅(⊤ : Subgroup Q), ⊤⁆ : Subgroup Q) := by
      rw [eq_mul_inv_of_mul_eq hce]
      exact mul_mem ha (inv_mem (hEQ he))
    have hcOp : c ∈ Op.comap φ := by
      rw [mem_comap, hφc]
      exact hb
    exact ⟨c, mem_inf.mpr ⟨mem_inf.mpr ⟨hc, hcQ⟩, hcOp⟩, hφc⟩
  intro b hb
  obtain ⟨S, hSU, hSp, hSmap⟩ := uc22p22u_exists_le_pCore_map_eq φ p U hnil hpU
  obtain ⟨u, hu, hub⟩ := himg b hb
  obtain ⟨y, hy, hyb⟩ : b ∈ S.map φ := by
    rw [hSmap]
    exact ⟨u, hu, hub⟩
  exact ⟨y, ⟨hSp hy, (hSU hy).1.2⟩, hyb⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

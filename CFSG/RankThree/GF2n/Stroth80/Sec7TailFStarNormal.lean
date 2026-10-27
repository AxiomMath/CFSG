module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailTIConfig
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.LocalAnalysis.SteinbergBQGeneralizedFittingSubnormal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG

theorem normal_subgroupOf_of_le_normalizer {X : Type*} [Group X] {H C L : Subgroup X}
    (hCH : ∀ h ∈ H, h ∈ Subgroup.normalizer (C : Set X)) (hLH : L ≤ H) :
    (C.subgroupOf L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact (Subgroup.mem_normalizer_iff.mp (hCH _ (hLH g.2)) (n : X)).mp hn

theorem map_generalizedFitting_subgroupOf {X : Type*} [Group X] {M L : Subgroup X} (hML : M ≤ L) :
    ((generalizedFitting ↥(M.subgroupOf L)).map (M.subgroupOf L).subtype).map L.subtype =
      (generalizedFitting ↥M).map M.subtype := by
  rw [← CFSG.WholeGroup.generalizedFitting_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hML),
    Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_normalizer_map_of_normal {X : Type*} [Group X] {H : Subgroup X} (Q : Subgroup H)
    [hQ : Q.Normal] {h : X} (hh : h ∈ H) :
    h ∈ Subgroup.normalizer ((Q.map H.subtype : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * q * (⟨h, hh⟩ : H)⁻¹, hQ.conj_mem q hq _, rfl⟩
  · intro hx
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
    have hq' : (q : X) = h * x * h⁻¹ := hqx
    refine Subgroup.mem_map.mpr
      ⟨⟨h⁻¹, H.inv_mem hh⟩ * q * (⟨h⁻¹, H.inv_mem hh⟩ : H)⁻¹, hQ.conj_mem q hq _, ?_⟩
    show h⁻¹ * (q : X) * h⁻¹⁻¹ = x
    rw [hq']
    group

theorem normal_eq_bot_of_fstar {X : Type*} [Group X] [Finite X] {H V N C : Subgroup X}
    (hCH : ∀ h ∈ H, h ∈ Subgroup.normalizer (C : Set X)) (hCHle : C ≤ H) (hCK : C ≤ NormIn H V)
    (hF : generalizedFitting ↥(NormIn H V) = N.subgroupOf (NormIn H V))
    (hN2 : IsPGroup 2 N) (hNK : N ≤ NormIn H V)
    (hO2 : ∀ P : Subgroup X, P ≤ H → (∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set X)) →
      IsPGroup 2 P → P = ⊥)
    (hO : ∀ P : Subgroup X, P ≤ H → (∀ h ∈ H, h ∈ Subgroup.normalizer (P : Set X)) →
      Odd (Nat.card P) → P = ⊥) : C = ⊥ := by
  have hKH : NormIn H V ≤ H := fun x hx => (mem_NormIn.mp hx).1
  haveI hBK : (C.subgroupOf (NormIn H V)).Normal :=
    normal_subgroupOf_of_le_normalizer hCH hKH
  haveI hAH : (C.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hCH le_rfl
  have hmono := CFSG.LocalAnalysis.SteinbergBQ.generalized_fitting_subnormal_monotone
    (G := ↥(NormIn H V)) (H := C.subgroupOf (NormIn H V)) hBK.isSubnormal
  rw [hF] at hmono
  have hPN : (generalizedFitting ↥C).map C.subtype ≤ N := by
    rw [← map_generalizedFitting_subgroupOf hCK]
    refine (Subgroup.map_mono (f := (NormIn H V).subtype) hmono).trans ?_
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  haveI hchar : (generalizedFitting ↥(C.subgroupOf H)).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥(C.subgroupOf H))).1
  haveI hQ : ((generalizedFitting ↥(C.subgroupOf H)).map (C.subgroupOf H).subtype).Normal :=
    inferInstance
  have hPH : (generalizedFitting ↥C).map C.subtype ≤ H :=
    (Subgroup.map_subtype_le _).trans hCHle
  have hPnorm : ∀ h ∈ H,
      h ∈ Subgroup.normalizer ((generalizedFitting ↥C).map C.subtype : Set X) := by
    intro h hh
    rw [← map_generalizedFitting_subgroupOf hCHle]
    exact mem_normalizer_map_of_normal _ hh
  have hP2 : IsPGroup 2 ↥((generalizedFitting ↥C).map C.subtype) :=
    IsPGroup.of_injective hN2 (Subgroup.inclusion hPN) (Subgroup.inclusion_injective hPN)
  have hPbot : (generalizedFitting ↥C).map C.subtype = ⊥ := hO2 _ hPH hPnorm hP2
  have hgf : generalizedFitting ↥C = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    have hmem : (c : X) ∈ (generalizedFitting ↥C).map C.subtype :=
      Subgroup.mem_map_of_mem C.subtype hc
    rw [hPbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  rw [eq_bot_iff]
  intro x hx
  have hcen := CFSG.centralizer_generalizedFitting_le ↥C
  have hc : (⟨x, hx⟩ : ↥C) ∈
      Subgroup.centralizer ((generalizedFitting ↥C : Subgroup ↥C) : Set ↥C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, hgf, Subgroup.mem_bot] at hg
    rw [hg, one_mul, mul_one]
  have h1 := hcen hc
  rw [hgf, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CentralCover
public import CFSG.GroupTheory.CommutingConjugatePair

public section
namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.Assembly CFSG.StandardType

theorem k2At_of_map_of_odd_central_ker
    {X C : Type} [Group X] [Group C] [Finite X] [Finite C] {K V : Subgroup X} {r : X}
    (ε : ↥K →* C) (hε : Function.Surjective ε) (hker : ε.ker ≤ Subgroup.center ↥K)
    (hodd : Odd (Nat.card ε.ker)) (hrK : r ∈ K) (hr2 : r ^ 2 = 1) (hVK : V ≤ K)
    (hV : IsPGroup 2 V)
    (h : pCoreOf 2 (Subgroup.centralizer ({ε ⟨r, hrK⟩} : Set C)) ≤
      Subgroup.normalizer ((V.subgroupOf K).map ε : Set C)) :
    K2At K V r := by
  intro y hy
  have hyK : y ∈ K := (GGRootNorm.pCoreOf_le _ hy).1
  let yK : ↥K := ⟨y, hyK⟩
  have hyInner : yK ∈ pCoreOf 2 (Subgroup.centralizer ({⟨r, hrK⟩} : Set ↥K)) := by
    have hMap := CFSG.GroupTheory.map_pCoreOf_inf_centralizer_mulEquiv
      (M := K) (MulEquiv.refl ↥K) hrK
    simp only [MulEquiv.refl_apply] at hMap
    rw [← hMap]
    exact Subgroup.mem_map_of_mem _ hy
  have hrK2 : (⟨r, hrK⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using hr2)
  have hεy : ε yK ∈ pCoreOf 2
      (Subgroup.centralizer ({ε ⟨r, hrK⟩} : Set C)) := by
    rw [← map_involution_centralizer_pCoreOf_of_odd_central_ker ε hε hker hodd
      (r := ⟨r, hrK⟩) hrK2]
    exact Subgroup.mem_map_of_mem ε hyInner
  have hyN : ε yK ∈
      Subgroup.normalizer ((V.subgroupOf K).map ε : Set C) := h hεy
  have hVK2 : IsPGroup 2 (V.subgroupOf K) :=
    hV.comap_of_injective K.subtype K.subtype_injective
  have hmapconj : (V.subgroupOf K).map (MulAut.conj yK).toMonoidHom = V.subgroupOf K := by
    refine CFSG.GroupTheory.eq_of_map_eq_map_of_isPGroup_of_odd_ker ε hker hodd
      (IsPGroup.map hVK2 (MulAut.conj yK).toMonoidHom) hVK2 ?_
    have hconjC : ((V.subgroupOf K).map (MulAut.conj yK).toMonoidHom).map ε =
        ((V.subgroupOf K).map ε).map (MulAut.conj (ε yK)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext v
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv]
    rw [hconjC]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN
  have hyNorm : yK ∈
      Subgroup.normalizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapconj
  exact (GGRootNorm.mem_normalizer_subgroupOf_iff hVK yK).mp hyNorm

end CFSG.StandardType.RCKC1

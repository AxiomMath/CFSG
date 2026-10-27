module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.SetwiseSylowNormalizer

open MulAction

theorem exists_correction
    {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
    (K:Subgroup G) (P:Sylow p K) (g:G)
    (hg:g∈Subgroup.normalizer (K:Set G)) :
    ∃k:K,(k:G)*g∈Subgroup.normalizer
      (((P:Subgroup K).map K.subtype):Set G) := by
  let E:MulAut K := K.normalizerMonoidHom ⟨g,hg⟩
  let T:Sylow p K := Sylow.mapSurjective (f:=E.toMonoidHom) E.surjective P
  obtain ⟨k,hk⟩ := exists_smul_eq K T P
  refine ⟨k,Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  have hT : (T:Subgroup K).map K.subtype =
      ((P:Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom := by
    change ((P:Subgroup K).map E.toMonoidHom).map K.subtype = _
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
  have hkmap : ((T:Subgroup K).map K.subtype).map (MulAut.conj (k:G)).toMonoidHom =
      (P:Subgroup K).map K.subtype := by
    calc
      _ = ((k • T:Sylow p K):Subgroup K).map K.subtype := by
        change ((T:Subgroup K).map K.subtype).map (MulAut.conj (k:G)).toMonoidHom =
          ((T:Subgroup K).map (MulAut.conj k).toMonoidHom).map K.subtype
        rw [Subgroup.map_map,Subgroup.map_map]
        congr 1
      _ = _ := by rw [hk]
  have hcomp : (MulAut.conj ((k:G)*g)).toMonoidHom =
      (MulAut.conj (k:G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    change ((k:G)*g)*x*((k:G)*g)⁻¹=(k:G)*(g*x*g⁻¹)*(k:G)⁻¹
    group
  change ((P:Subgroup K).map K.subtype).map
    (MulAut.conj ((k:G)*g)).toMonoidHom=(P:Subgroup K).map K.subtype
  rw [hcomp,←Subgroup.map_map,←hT]
  exact hkmap

theorem normalizes_fixer
    {G X:Type*} [Group G] [MulAction G X]
    (s:Set X) (g:G) (hg:∀x:X,x∈s ↔ g • x∈s) :
    g∈Subgroup.normalizer (fixingSubgroup G s:Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro k
  constructor
  · intro hk
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hginv:g⁻¹ • x∈s := (hg _).mpr (by simpa only [smul_inv_smul] using hx)
    have hkx := (mem_fixingSubgroup_iff G).mp hk _ hginv
    change (g*k*g⁻¹) • x=x
    simp only [mul_smul,hkx,smul_inv_smul]
  · intro hk
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hkx := (mem_fixingSubgroup_iff G).mp hk _ ((hg x).mp hx)
    have he := congrArg (fun y:X => g⁻¹ • y) hkx
    simpa only [mul_smul,inv_smul_smul] using he

theorem exists_same_restriction
    {G X:Type*} [Group G] [Finite G] [MulAction G X] {p:ℕ} [Fact p.Prime]
    (s:Set X) (P:Sylow p (fixingSubgroup G s)) (g:G)
    (hg:∀x:X,x∈s ↔ g • x∈s) :
    ∃n:G,n∈Subgroup.normalizer
      (((P:Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype):Set G) ∧
      ∀x∈s,n • x=g • x := by
  obtain ⟨k,hk⟩ := exists_correction (fixingSubgroup G s) P g (normalizes_fixer s g hg)
  refine ⟨(k:G)*g,hk,?_⟩
  intro x hx
  rw [mul_smul]
  exact (mem_fixingSubgroup_iff G).mp k.property _ ((hg x).mp hx)

theorem exists_sylow_intermediate
    {G:Type*} [Group G] [Finite G] {p:ℕ} [Fact p.Prime]
    (K H:Subgroup G) (hHK:H≤K) (P:Sylow p K)
    (hPH:(P:Subgroup K).map K.subtype≤H) :
    ∃S:Sylow p H,(S:Subgroup H).map H.subtype=(P:Subgroup K).map K.subtype := by
  let J := H.subgroupOf K
  have hPJ:(P:Subgroup K)≤J := by
    intro q hq
    exact hPH ⟨q,hq,rfl⟩
  let R := P.subtype hPJ
  let E:J ≃* H := Subgroup.subgroupOfEquivOfLe hHK
  let S := Sylow.mapSurjective (f:=E.toMonoidHom) E.surjective R
  refine ⟨S,?_⟩
  change ((R:Subgroup J).map E.toMonoidHom).map H.subtype=_
  have hm : H.subtype.comp E.toMonoidHom=K.subtype.comp J.subtype := rfl
  rw [Subgroup.map_map,hm,←Subgroup.map_map]
  change (((P:Subgroup K).subgroupOf J).map J.subtype).map K.subtype = _
  rw [Subgroup.map_subgroupOf_eq_of_le hPJ]

end FiveTransitive.SetwiseSylowNormalizer

end CFSG

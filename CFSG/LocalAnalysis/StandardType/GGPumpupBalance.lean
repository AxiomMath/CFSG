module

public import CFSG.LocalAnalysis.StandardType.GGPumpupQuot
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime

public section

namespace CFSG.StandardType

open CFSG CFSG.ComponentClassification Subgroup

namespace GGPumpup

variable {G : Type} [Group G]

theorem lBalanceIsKGroup_of_le {N C : Subgroup G} (hN : CFSG.Open.lBalanceIsKGroup ↥N)
    (hCN : C ≤ N) : CFSG.Open.lBalanceIsKGroup ↥C :=
  CFSG.Open.IsKGroup.of_le hN hCN

theorem inf_subgroupOf_inf_normal {A B D : Subgroup G} (hAB : A ≤ B)
    (hA : (A.subgroupOf B).Normal) : ((A ⊓ D).subgroupOf (B ⊓ D)).Normal := by
  rw [normal_subgroupOf_iff (inf_le_inf_right D hAB)]
  intro a k ha hk
  obtain ⟨haA, haD⟩ := mem_inf.mp ha
  obtain ⟨hkB, hkD⟩ := mem_inf.mp hk
  exact mem_inf.mpr ⟨(normal_subgroupOf_iff hAB).mp hA a k haA hkB,
    mul_mem (mul_mem hkD haD) (inv_mem hkD)⟩

theorem exists_lt_inv_pow_eq {x : G} {p : ℕ} (hp : 0 < p) (hx : x ^ p = 1) {i : ℕ}
    (hi : i < p) : ∃ j, j < p ∧ (x ^ i)⁻¹ = x ^ j := by
  refine ⟨(p - i) % p, Nat.mod_lt _ hp, ?_⟩
  rw [← pow_eq_pow_mod (p - i) hx]
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  rw [← pow_add, Nat.add_sub_cancel' hi.le, hx]

theorem orbitJoinLT_eq_iSup_map_conj {A : Subgroup G} {x : G} {p : ℕ} (hp : 0 < p)
    (hx : x ^ p = 1) :
    orbitJoinLT A x p = ⨆ (i : ℕ) (_ : i < p), A.map (MulAut.conj (x ^ i)).toMonoidHom := by
  apply le_antisymm
  · refine orbitJoinLT_le fun i hi => ?_
    obtain ⟨j, hj, hij⟩ := exists_lt_inv_pow_eq hp hx hi
    refine le_iSup₂_of_le j hj (le_of_eq ?_)
    rw [conjugate, hij]
  · refine iSup₂_le fun i hi => ?_
    obtain ⟨j, hj, hij⟩ := exists_lt_inv_pow_eq hp hx hi
    refine (le_of_eq ?_).trans (conjugate_le_orbitJoinLT A x hj)
    rw [conjugate, ← hij, inv_inv]

end GGPumpup

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggLayerClosure_eq_map {p : ℕ} [Fact p.Prime] {Y J : Subgroup G} (hJY : J ≤ Y) :
    ggLayerClosure p Y J =
      (GGPumpup.closureIn (pLayer (↥Y) p) (J.subgroupOf Y)).map Y.subtype := by
  rw [ggLayerClosure, LBalance.Asm.lBalancePLayer_eq_map, GGPumpup.closureIn, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    obtain ⟨g, hg, rfl⟩ := mem_map.mp ha
    refine le_iSup_of_le g ?_
    rw [Subgroup.map_iSup]
    refine le_iSup_of_le hg (le_of_eq ?_)
    rw [GGPumpup.map_conjugate, map_subgroupOf_eq_of_le hJY]
    rfl
  · refine iSup_le fun g => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hg => ?_
    refine le_iSup₂_of_le (g : G) (mem_map_of_mem _ hg) (le_of_eq ?_)
    rw [GGPumpup.map_conjugate, map_subgroupOf_eq_of_le hJY]
    rfl

theorem GGPumpup.lBalanceIsPComponent_inf_of_pLayer {p : ℕ} [Fact p.Prime] {X Y J : Subgroup G}
    (hJ : CFSG.Open.lBalanceIsPComponent p
      (CFSG.Open.lBalancePLayer p (CFSG.Open.lBalancePLayer p X ⊓ Y)) J) :
    CFSG.Open.lBalanceIsPComponent p (Y ⊓ X) J := by
  set Z := CFSG.Open.lBalancePLayer p X ⊓ Y with hZdef
  have hJZ : CFSG.Open.lBalanceIsPComponent p Z J := by
    have : ((CFSG.Open.lBalancePLayer p Z).subgroupOf Z).Normal :=
      lBalancePLayer_subgroupOf_normal p Z
    exact lBalanceIsPComponent_of_normal (lBalancePLayer_le p Z) (LBalance.subnormal_le hJ.1) hJ
  have hZXY : Z ≤ X ⊓ Y := inf_le_inf_right Y (lBalancePLayer_le p X)
  have : (Z.subgroupOf (X ⊓ Y)).Normal :=
    GGPumpup.inf_subgroupOf_inf_normal (lBalancePLayer_le p X)
      (lBalancePLayer_subgroupOf_normal p X)
  rw [inf_comm]
  exact lBalanceIsPComponent_of_normal hZXY (LBalance.subnormal_le hJZ.1) hJZ

theorem GGPumpup.isPComponent_subgroupOf_centralizer {p : ℕ} [Fact p.Prime] {Y J : Subgroup G}
    {x : G} (hxY : x ∈ Y)
    (hJ : CFSG.Open.lBalanceIsPComponent p (Y ⊓ centralizer ({x} : Set G)) J) :
    J.subgroupOf Y ≤ centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) ∧
      IsPComponent p ((J.subgroupOf Y).subgroupOf
        (centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y))) := by
  have hJle : J ≤ Y ⊓ centralizer ({x} : Set G) := LBalance.subnormal_le hJ.1
  have hC' : (Y ⊓ centralizer ({x} : Set G)).subgroupOf Y =
      centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) := by
    ext z
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, true_and,
      mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hTC : J.subgroupOf Y ≤ centralizer ({(⟨x, hxY⟩ : ↥Y)} : Set ↥Y) := by
    rw [← hC']
    intro z hz
    exact mem_subgroupOf.mpr (hJle (mem_subgroupOf.mp hz))
  refine ⟨hTC, (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ _ hTC).mpr ?_⟩
  rw [← hC']
  exact (LBalance.pComponent_nested_iff p _ Y J inf_le_left hJle).mpr hJ

theorem ggPumpupInput_of_lBalance (hL : GGLBalanceInput) : GGPumpupInput := by
  intro G _ _ p hp hK x y hxy hox hoy J hJ
  have : Fact p.Prime := ⟨hp⟩
  set Y := centralizer ({y} : Set G) with hYdef
  set X := centralizer ({x} : Set G) with hXdef
  have hxY : x ∈ Y := mem_centralizer_singleton_iff.mpr hxy
  have hxp : x ^ p = 1 := hox ▸ pow_orderOf_eq_one x
  have hy1 : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hoy
    exact hp.one_lt.ne hoy
  have hYK : CFSG.Open.lBalanceIsKGroup ↥Y := by
    have hP : IsPGroup p (zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hoy, pow_one])
    have hne : zpowers y ≠ ⊥ := fun h => hy1 (zpowers_eq_bot.mp h)
    refine GGPumpup.lBalanceIsKGroup_of_le (hK _ hne hP) ?_
    have hc : centralizer ((zpowers y : Subgroup G) : Set G) = Y := by
      rw [zpowers_eq_closure, centralizer_closure]
    rw [← hc]
    exact centralizer_le_normalizer _
  have hJYX : CFSG.Open.lBalanceIsPComponent p (Y ⊓ X) J :=
    GGPumpup.lBalanceIsPComponent_inf_of_pLayer hJ
  have hJle : J ≤ Y ⊓ X := LBalance.subnormal_le hJYX.1
  have hJYX' : J ≤ CFSG.Open.lBalancePLayer p (Y ⊓ X) := le_sSup hJYX
  have hJW : J ≤ CFSG.Open.lBalancePLayer p Y :=
    hJYX'.trans (lBalancePLayer_inf_centralizer_le_of_input hL hp hYK hxY hxp)
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx'p : x' ^ p = 1 := Subtype.ext (by simp [x', hxp])
  set T := J.subgroupOf Y with hTdef
  obtain ⟨hTC, hT⟩ := GGPumpup.isPComponent_subgroupOf_centralizer hxY hJYX
  have hTE : T ≤ pLayer (↥Y) p := by
    intro z hz
    have hz' : (z : G) ∈ (pLayer (↥Y) p).map Y.subtype := by
      rw [← LBalance.Asm.lBalancePLayer_eq_map]
      exact hJW (mem_subgroupOf.mp hz)
    exact (mem_map_iff_mem Y.subtype_injective).mp hz'
  obtain ⟨A', hA', hKA'⟩ := GGPumpup.exists_pComponent_closureIn_eq hx'p hTC hT hTE
  set A := A'.map Y.subtype with hAdef
  have hAY : A ≤ Y := map_subtype_le A'
  have hAlB : CFSG.Open.lBalanceIsPComponent p Y A := by
    refine (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y A hAY).mp ?_
    have hAA' : A.subgroupOf Y = A' := comap_map_eq_self_of_injective Y.subtype_injective A'
    rw [hAA']
    exact hA'
  have hAW : A ≤ CFSG.Open.lBalancePLayer p Y := le_sSup hAlB
  have : ((CFSG.Open.lBalancePLayer p Y).subgroupOf Y).Normal :=
    lBalancePLayer_subgroupOf_normal p Y
  have hAW' : CFSG.Open.lBalanceIsPComponent p (CFSG.Open.lBalancePLayer p Y) A :=
    LBalance.Asm.pComponent_relative_normal_restriction p _ Y A (lBalancePLayer_le p Y) hAlB hAW
  have hKeq : ggLayerClosure p Y J = GGPumpup.orbitJoinLT A x p := by
    rw [ggLayerClosure_eq_map (hJle.trans inf_le_left), ← hTdef, hKA', GGPumpup.map_orbitJoinLT]
    rfl
  by_cases hxA : x ∈ normalizer (A : Set G)
  · left
    rw [hKeq, GGPumpup.orbitJoinLT_eq_self hxA hp.pos]
    exact ⟨hAW', hxA⟩
  · right
    exact ⟨A, hAW', hxA, hKeq.trans (GGPumpup.orbitJoinLT_eq_iSup_map_conj hp.pos hxp)⟩

theorem ggPumpupInput_of_catalogueSchreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    GGPumpupInput :=
  ggPumpupInput_of_lBalance (ggLBalanceInput_of_catalogueSchreier hS)

end Main

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.BlueprintB2Thompson
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG CFSG.Quasithin.BlueprintB2

theorem exists_elementary_card_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (p r : ℕ) (h : ∃ A : Subgroup X, IsElementaryAbelian p A ∧ Nat.card A = p ^ r) :
    ∃ A : Subgroup Y, IsElementaryAbelian p A ∧ Nat.card A = p ^ r := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A.map e.toMonoidHom, isElementaryAbelian_map hA _, by
    rw [Subgroup.card_map_of_injective e.injective, hc]⟩

theorem pRank_congr_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    CFSG.pRank p X = CFSG.pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

theorem map_mem_elemThompsonFamily_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {p : ℕ} {A : Subgroup X} (hA : A ∈ elemThompsonFamily X p) :
    A.map e.toMonoidHom ∈ elemThompsonFamily Y p :=
  ⟨isElementaryAbelian_map hA.1 e.toMonoidHom, by
    rw [Subgroup.card_map_of_injective e.injective, hA.2, pRank_congr_mulEquiv e p]⟩

theorem map_elemThompson_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    (elemThompson X p).map e.toMonoidHom = elemThompson Y p := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (map_mem_elemThompsonFamily_mulEquiv e hA)
  · refine sSup_le fun B hB => ?_
    intro y hy
    have : e.symm y ∈ elemThompson X p :=
      le_sSup (map_mem_elemThompsonFamily_mulEquiv e.symm hB) ⟨y, hy, rfl⟩
    exact ⟨e.symm y, this, e.apply_symm_apply y⟩

variable {G : Type*} [Group G]

theorem map_elemThompson_subtype_eq_of_le [Finite G] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup G} (hXY : X ≤ Y) (hJ : (elemThompson Y p).map Y.subtype ≤ X) :
    (elemThompson X p).map X.subtype = (elemThompson Y p).map Y.subtype := by
  have hJZ : elemThompson Y p ≤ X.subgroupOf Y := fun y hy =>
    Subgroup.mem_subgroupOf.2 (hJ ⟨y, hy, rfl⟩)
  have h1 := elemThompson_map_subtype (p := p) hJZ
  let e : X.subgroupOf Y ≃* X := Subgroup.subgroupOfEquivOfLe hXY
  have hcomp : X.subtype.comp e.toMonoidHom = Y.subtype.comp (X.subgroupOf Y).subtype := by
    ext
    rfl
  rw [← map_elemThompson_mulEquiv e p, Subgroup.map_map, hcomp, ← Subgroup.map_map, h1]

theorem map_elemThompsonCenterTorsion_le (p : ℕ) (X : Subgroup G) :
    (elemThompsonCenterTorsion X p).map X.subtype ≤ (elemThompson X p).map X.subtype :=
  Subgroup.map_mono fun _ hz => (mem_centerTorsion_iff.mp hz).1

theorem mem_map_elemThompsonCenterTorsion_iff [Finite G] {p : ℕ} [Fact p.Prime]
    {X : Subgroup G} {x : G} :
    x ∈ (elemThompsonCenterTorsion X p).map X.subtype ↔
      x ∈ X ∧ x ^ p = 1 ∧ ∀ j ∈ (elemThompson X p).map X.subtype, j * x = x * j := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hc, hp⟩ := mem_elemThompsonCenterTorsion_iff_centralizer.mp hy
    refine ⟨y.2, by simpa using congrArg Subtype.val hp, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc j hj)
  · rintro ⟨hxX, hxp, hxj⟩
    refine ⟨⟨x, hxX⟩, mem_elemThompsonCenterTorsion_iff_centralizer.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun j hj => Subtype.ext (hxj j ⟨j, hj, rfl⟩)
    · exact Subtype.ext (by simpa using hxp)

theorem map_elemThompsonCenterTorsion_subtype_eq_of_le [Finite G] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup G} (hXY : X ≤ Y) (hJ : (elemThompson Y p).map Y.subtype ≤ X) :
    (elemThompsonCenterTorsion X p).map X.subtype =
      (elemThompsonCenterTorsion Y p).map Y.subtype := by
  have hJXY := map_elemThompson_subtype_eq_of_le hXY hJ
  ext x
  constructor
  · intro hx
    obtain ⟨hxX, hxp, hxj⟩ := mem_map_elemThompsonCenterTorsion_iff.1 hx
    rw [hJXY] at hxj
    exact mem_map_elemThompsonCenterTorsion_iff.2 ⟨hXY hxX, hxp, hxj⟩
  · intro hx
    obtain ⟨-, hxp, hxj⟩ := mem_map_elemThompsonCenterTorsion_iff.1 hx
    refine mem_map_elemThompsonCenterTorsion_iff.2
      ⟨hJ (map_elemThompsonCenterTorsion_le p Y hx), hxp, ?_⟩
    rw [hJXY]
    exact hxj

theorem mem_map_elemBaumann_iff {p : ℕ} {X : Subgroup G} {x : G} :
    x ∈ (elemBaumann X p).map X.subtype ↔
      x ∈ X ∧ ∀ e ∈ (elemThompsonCenterTorsion X p).map X.subtype, e * x = x * e := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy e he)
  · rintro ⟨hxX, hx⟩
    exact ⟨⟨x, hxX⟩, Subgroup.mem_centralizer_iff.mpr fun e he =>
      Subtype.ext (hx e ⟨e, he, rfl⟩), rfl⟩

theorem thompson_centralized_internal_seeds_have_normal_baumann_centralizer {H : Type*}
    [Group H] [Finite H] (T : Sylow 2 H) (V : Subgroup H) [V.Normal] (hV1 : V ≠ ⊥)
    (hV : IsElementaryAbelian 2 V) (C J E S : Subgroup H)
    (hC : C = Subgroup.centralizer (V : Set H))
    (hJ : J = (elemThompson (T : Subgroup H) 2).map (T : Subgroup H).subtype)
    (hE : E = (elemThompsonCenterTorsion (T : Subgroup H) 2).map (T : Subgroup H).subtype)
    (hS : S = (elemBaumann (T : Subgroup H) 2).map (T : Subgroup H).subtype)
    (hCT : C ≤ T) (hJC : J ≤ C) :
    J = (elemThompson C 2).map C.subtype ∧
      E = (elemThompsonCenterTorsion C 2).map C.subtype ∧ V ≤ E ∧
      S = Subgroup.centralizer (E : Set H) ∧ S ≤ C ∧ S ≠ ⊥ ∧ S.Normal ∧ IsPGroup 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVc, hV2⟩ := isElementaryAbelian_iff.1 hV
  have hJC' := hJC
  rw [hJ] at hJC'
  have hJ' : J = (elemThompson C 2).map C.subtype := by
    rw [hJ, map_elemThompson_subtype_eq_of_le hCT hJC']
  have hE' : E = (elemThompsonCenterTorsion C 2).map C.subtype := by
    rw [hE, map_elemThompsonCenterTorsion_subtype_eq_of_le hCT hJC']
  have hVC : V ≤ C := by
    rw [hC]
    exact fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw => hVc w hw v hv
  have hVE : V ≤ E := by
    intro v hv
    rw [hE]
    refine mem_map_elemThompsonCenterTorsion_iff.2 ⟨hCT (hVC hv), hV2 v hv, fun j hj => ?_⟩
    have hjC := hJC' hj
    rw [hC] at hjC
    exact (Subgroup.mem_centralizer_iff.1 hjC v hv).symm
  have hSE : S = Subgroup.centralizer (E : Set H) := by
    ext x
    rw [hS, mem_map_elemBaumann_iff, Subgroup.mem_centralizer_iff, ← hE]
    constructor
    · rintro ⟨-, hx⟩
      exact hx
    · intro hx
      refine ⟨hCT ?_, hx⟩
      rw [hC, Subgroup.mem_centralizer_iff]
      exact fun v hv => hx v (hVE hv)
  have hSC : S ≤ C := by
    rw [hSE, hC]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVE)
  have hES : E ≤ S := by
    rw [hSE]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hE] at hx hy
    obtain ⟨-, -, hxj⟩ := mem_map_elemThompsonCenterTorsion_iff.1 hx
    exact hxj y (map_elemThompsonCenterTorsion_le 2 _ hy)
  have hS1 : S ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (by rw [← h]; exact hVE.trans hES))
  have hEn : E.Normal := by
    have : C.Normal := by
      rw [hC]
      infer_instance
    have := elemThompsonCenterTorsion_characteristic C 2
    rw [hE']
    exact ConjAct.normal_of_characteristic_of_normal
  have hSn : S.Normal := by
    rw [hSE]
    infer_instance
  exact ⟨hJ', hE', hVE, hSE, hSC, hS1, hSn, T.isPGroup'.to_le (hSC.trans hCT)⟩

end CFSG.Quasithin.SteinbergBQ

module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SProp21

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L828SBt

variable {G : Type} [Group G] [Finite G]

theorem s828_map_commSub {X V : Subgroup G} [IsMulCommutative ↥V]
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (W : Subgroup ↥V) :
    (s828CommSub (autOn X V) W).map V.subtype = ⁅X, W.map V.subtype⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, s828CommSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, w, hw, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.1 hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    show (((conjAct V g) w * w⁻¹ : ↥V) : G) ∈ ⁅X, W.map V.subtype⁆
    rw [Subgroup.coe_mul, CFSG.Quasithin.AutOn.coe_conjAct_apply, Subgroup.coe_inv]
    have e : (g : G) * (w : G) * (g : G)⁻¹ * (w : G)⁻¹ = ⁅(g : G), (w : G)⁆ := by
      rw [commutatorElement_def]
    rw [e]
    exact Subgroup.commutator_mem_commutator hgX (Subgroup.mem_map_of_mem _ hw)
  · rw [Subgroup.commutator_le]
    intro x hx g hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hg
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hXV hx
    have hgen : (CFSG.Quasithin.conjAct V ⟨x, hxN⟩ w * w⁻¹) ∈ s828CommSub (autOn X V) W :=
      Subgroup.subset_closure ⟨_, CFSG.Quasithin.AutOn.conjAct_mem_autOn ⟨x, hxN⟩ hx, w, hw, rfl⟩
    have e : ((CFSG.Quasithin.conjAct V ⟨x, hxN⟩ w * w⁻¹ : ↥V) : G) = ⁅x, (w : G)⁆ := by
      rw [Subgroup.coe_mul, CFSG.Quasithin.AutOn.coe_conjAct_apply, Subgroup.coe_inv,
        commutatorElement_def]
    have hmem : ⁅x, (w : G)⁆ ∈ (s828CommSub (autOn X V) W).map V.subtype := by
      rw [← e]
      exact Subgroup.mem_map_of_mem V.subtype hgen
    exact hmem

theorem s828_fixV_map {T L I : Subgroup G} {h : G} [IsMulCommutative ↥(fsuV T I)]
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))).map (fsuV T I).subtype =
      ch82U (fsuV T I) h := by
  rw [fixV_autOn_82 hAN, Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.mpr inf_le_left

theorem s828_Bt_L3 {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hMB1 : MB1_828) (hcard : Mathieu.StmtH13Card) (hV : IsElemAbelian 2 (fsuV T I))
    (hL0 : fsuL0 T L = L) (hC5 : Concl825 T L I h k)
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
    (hr : ∃ n : ℕ, Row711L3Nine T L I n) :
    ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h =
      ch82B (fsuV T I) h := by
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian hAe
  have hLUN : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hX : autOn (ch82A (fsuV T I) h) (fsuV T I) ≤
      Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    autOn_le_normalizer_82 hAL
  have hXe : IsElemAbelian2 (autOn (ch82A (fsuV T I) h) (fsuV T I)) :=
    isElemAbelian2_of_828 (isElemAbelian_autOn_82 hAe)
  have hrows := rows_hlu82_828 hcard hL0 hV hC5 hAN hAp
  have hm := (hMB1 _ (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) hX hXe).1
    (hrows.1 hr)
  rw [s828_perfect_autOn_LU hLN hAN] at hm
  have hm2 := congrArg (Subgroup.map (fsuV T I).subtype) hm
  rw [Subgroup.map_sup, s828_map_commSub hLUN, s828_fixV_map (L := L) hAN, ← s828_B'_eq_map hLN hAN hAL]
    at hm2
  rw [Subgroup.commutator_comm (ch82B (fsuV T I) h) (ch82LU L (ch82U (fsuV T I) h)), hB]
  exact hm2

theorem s828_Bt_cocode {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hMB1 : MB1_828) (hcard : Mathieu.StmtH13Card) (hV : IsElemAbelian 2 (fsuV T I))
    (hL0 : fsuL0 T L = L) (hC5 : Concl825 T L I h k)
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
    (hr : Row711M24Cocode T L I) :
    ⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h =
      ch82B (fsuV T I) h := by
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian hAe
  have hLUN : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hX : autOn (ch82A (fsuV T I) h) (fsuV T I) ≤
      Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    autOn_le_normalizer_82 hAL
  have hXe : IsElemAbelian2 (autOn (ch82A (fsuV T I) h) (fsuV T I)) :=
    isElemAbelian2_of_828 (isElemAbelian_autOn_82 hAe)
  have hrows := rows_hlu82_828 hcard hL0 hV hC5 hAN hAp
  have hm := (hMB1 _ (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) hX hXe).2.2.2
    (hrows.2.2.2 hr)
  rw [s828_perfect_autOn_LU hLN hAN] at hm
  have hm2 := congrArg (Subgroup.map (fsuV T I).subtype) hm
  rw [Subgroup.map_sup, s828_map_commSub hLUN, s828_fixV_map (L := L) hAN, ← s828_B'_eq_map hLN hAN hAL]
    at hm2
  rw [Subgroup.commutator_comm (ch82B (fsuV T I) h) (ch82LU L (ch82U (fsuV T I) h)), hB]
  exact hm2

theorem s828_Bt_M22 {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hMB1 : MB1_828) (hcard : Mathieu.StmtH13Card) (hV : IsElemAbelian 2 (fsuV T I))
    (hL0 : fsuL0 T L = L) (hC5 : Concl825 T L I h k)
    (hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAN : ch82A (fsuV T I) h ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hAL : ch82A (fsuV T I) h ≤ Subgroup.normalizer (L : Set G))
    (hAe : IsElemAbelian 2 (ch82A (fsuV T I) h))
    (hB : ch82B (fsuV T I) h = ⁅fsuV T I, ch82A (fsuV T I) h⁆ ⊔
      ⁅fsuV T I, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h)
    (hr : Row711M22Code T L I) :
    (⁅ch82B (fsuV T I) h, ch82LU L (ch82U (fsuV T I) h)⁆ ⊔ ch82U (fsuV T I) h).relIndex
      (ch82B (fsuV T I) h) = 2 := by
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian hAe
  have hLUN : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hX : autOn (ch82A (fsuV T I) h) (fsuV T I) ≤
      Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    autOn_le_normalizer_82 hAL
  have hXe : IsElemAbelian2 (autOn (ch82A (fsuV T I) h) (fsuV T I)) :=
    isElemAbelian2_of_828 (isElemAbelian_autOn_82 hAe)
  have hrows := rows_hlu82_828 hcard hL0 hV hC5 hAN hAp
  have hm := (hMB1 _ (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)) hX hXe).2.1
    (hrows.2.1 hr)
  rw [s828_perfect_autOn_LU hLN hAN] at hm
  have hrel := Subgroup.relIndex_map_map_of_injective (f := (fsuV T I).subtype)
    (s828CommSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
      (s828BPrime (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I))) ⊔
        fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))
    (s828BPrime (autOn L (fsuV T I)) (autOn (ch82A (fsuV T I) h) (fsuV T I)))
    (fsuV T I).subtype_injective
  rw [hm] at hrel
  rw [Subgroup.map_sup, s828_map_commSub hLUN, s828_fixV_map (L := L) hAN, ← s828_B'_eq_map hLN hAN hAL]
    at hrel
  rw [Subgroup.commutator_comm (ch82B (fsuV T I) h) (ch82LU L (ch82U (fsuV T I) h)), hB]
  exact hrel

end L828SBt

end CFSG.Quasithin.H13

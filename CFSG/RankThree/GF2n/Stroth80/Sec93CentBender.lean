module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76StrongEmb
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.GF2n.Stroth80.Sec93OutBender

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.GH74.Uniqueness.Bender

theorem mem_of_mul_self_eq_one_of_bender {K : Type} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K) {T : Subgroup K}
    (hTQ : T ≤ (Q : Subgroup K)) (hZT : rootCenter (Q : Subgroup K) ≤ T)
    (hT : IsElemAbelian 2 T) (hT1 : T ≠ ⊥) {x : K} (hx : x ∈ Subgroup.centralizer (T : Set K))
    (hx2 : x * x = 1) : x ∈ T := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact T.one_mem
  obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  have htt : t * t = 1 := hT.mul_self_eq_one htT
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have hord : orderOf t = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact htt) ht1'
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  have htB : t ∈ borel (Q : Subgroup K) := le_borel _ (hTQ htT)
  have hxc : x ∈ Subgroup.centralizer ({t} : Set K) := by
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx t htT
  have hxB : x ∈ borel (Q : Subgroup K) :=
    CFSG.ComponentClassification.Sol76.centralizer_le_of_isStronglyEmbedded hc.strong hord htB hxc
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  exact hZT (hc.center_of_involution x hxB hxo)

theorem rootCenter_le_map_center {K : Type} [Group K] (Q : Subgroup K) :
    rootCenter Q ≤ (Subgroup.center Q).map Q.subtype := by
  intro y hy
  obtain ⟨hyQ, hyc⟩ := hy
  refine ⟨⟨y, hyQ⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyc g g.2)

theorem mem_of_mul_self_eq_one_psl2 {G : Type} [Group G] [Finite G]
    {f : ℕ} (hG : StatedClassicalModel G .PSL 2 2 f) {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) :
    x ∈ T := by
  obtain ⟨⟨-, ⟨Q, hQT⟩, -⟩, -⟩ := psl2_wc hG hT hT1
  exact mem_of_mul_self_eq_one_of_bender (benderType_of_psl2 hG) Q hQT.symm.le
    (inf_le_left.trans hQT.le) hT.1 hT1 hx hx2

theorem mem_of_mul_self_eq_one_sz {G : Type} [Group G] [Finite G]
    {s : ℕ} (hG : CFSG.Blueprint.LieModel G .twistedB2 0 2 s) {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) :
    x ∈ T := by
  obtain ⟨⟨-, ⟨Q, hQT⟩, -⟩, -⟩ := sz_wc hG hT hT1
  obtain ⟨n, i, e, h⟩ := exists_benderType_of_sz hG
  refine mem_of_mul_self_eq_one_of_bender h Q ?_ ?_ hT.1 hT1 hx hx2
  · rw [hQT]
    exact Subgroup.map_subtype_le _
  · rw [hQT]
    exact rootCenter_le_map_center _

theorem mem_of_mul_self_eq_one_psu3 {G : Type} [Group G] [Finite G]
    {s : ℕ} (hs : 2 ≤ s) (hG : StatedClassicalModel G .PSU 3 2 s) {T : Subgroup G}
    (hT : IsWC T) (hT1 : T ≠ ⊥) {x : G} (hx : x ∈ Subgroup.centralizer (T : Set G))
    (hx2 : x * x = 1) : x ∈ T := by
  obtain ⟨⟨-, ⟨Q, hQT⟩, -⟩, -⟩ := psu3_wc hs hG hT hT1
  obtain ⟨n, i, e, h⟩ := exists_benderType_of_psu3 hs hG
  refine mem_of_mul_self_eq_one_of_bender h Q ?_ ?_ hT.1 hT1 hx hx2
  · rw [hQT]
    exact Subgroup.map_subtype_le _
  · rw [hQT]
    exact rootCenter_le_map_center _

end CFSG.RankThree.GF2n.Stroth80

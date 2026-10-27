module

public import CFSG.LocalAnalysis.StandardType.GGE6D4LocalJ
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType.E6D4Tw

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem pow_five_le_card_range_ggGamma {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hJX : J ≤ X) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hS : Nat.card (Bs ⊓ J : Subgroup G) = 3 ^ 4)
    (hZ : ∀ b ∈ Bs ⊓ J, b ∈ Subgroup.centralizer (J : Set G) → b = 1)
    {d : G} (hdBs : d ∈ Bs) (hdJ : d ∈ Subgroup.centralizer (J : Set G))
    (hdX : d ∉ Subgroup.centralizer (X : Set G)) :
    3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd1 : d ≠ 1 := by
    intro h
    exact hdX (by rw [h]; exact Subgroup.one_mem _)
  have hdord : orderOf d = 3 := orderOf_eq_prime (hBs.2 d hdBs) hd1
  have hZcard : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, hdord]
  have hZC : Subgroup.zpowers d ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.zpowers_le.mpr hdJ
  have hKC : (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      Subgroup.centralizer (J : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJX))
  have hZKC : (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) ≤
      Subgroup.centralizer (J : Set G) :=
    sup_le hZC hKC
  have hBs_cent : Bs ≤ Subgroup.centralizer (Bs : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨c, hc⟩ ⟨b, hb⟩)
  have hBsNA : Bs ≤ Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) :=
    hBs_cent.trans ((Subgroup.centralizer_le (fun x hx => hx.1)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hBsNZ : Bs ≤ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) :=
    hBs_cent.trans ((Subgroup.centralizer_le
      (fun x hx => Subgroup.zpowers_le.mpr hdBs hx)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hZKBs : (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) ≤
      Bs := sup_le (Subgroup.zpowers_le.mpr hdBs) inf_le_left
  have hdisjA : Disjoint (Bs ⊓ J : Subgroup G)
      (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) := by
    rw [Subgroup.disjoint_def]
    intro a ha ha'
    exact hZ a ha (hZKC ha')
  have hdisjZ : Disjoint (Subgroup.zpowers d : Subgroup G)
      (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [Subgroup.disjoint_def]
    intro a haZ haK
    by_contra ha1
    have haord : orderOf a = 3 := by
      have hdiv : orderOf a ∣ 3 := by
        rw [← hZcard]
        exact Subgroup.orderOf_dvd_natCard _ haZ
      exact ((Nat.dvd_prime Nat.prime_three).mp hdiv).resolve_left
        (fun h => ha1 (orderOf_eq_one_iff.mp h))
    have hazcard : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, haord]
    have hazEq : Subgroup.zpowers a = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haZ)
        (by rw [hZcard, hazcard])
    have hd_za : d ∈ Subgroup.zpowers a := by
      rw [hazEq]
      exact Subgroup.mem_zpowers d
    exact hdX (Subgroup.zpowers_le.mpr haK.2 hd_za)
  have hnormA : (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) ≤
      Subgroup.normalizer ((Bs ⊓ J : Subgroup G) : Set G) := hZKBs.trans hBsNA
  have hnormZ : (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) :=
    inf_le_left.trans hBsNZ
  have hcardA := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Bs ⊓ J : Subgroup G)
    (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G)
    hnormA hdisjA
  have hcardZ := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers d : Subgroup G)
    (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) hnormZ hdisjZ
  have hcardH : Nat.card ((Bs ⊓ J : Subgroup G) ⊔
      (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) :
        Subgroup G) =
      3 ^ 5 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    rw [hcardA, hcardZ, hS, hZcard]
    ring
  have hle : Nat.card ((Bs ⊓ J : Subgroup G) ⊔
      (Subgroup.zpowers d ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) :
        Subgroup G) ≤ Nat.card Bs :=
    Subgroup.card_le_of_le
      (sup_le inf_le_left (sup_le (Subgroup.zpowers_le.mpr hdBs) inf_le_left))
  have hle' : 3 ^ 5 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      Nat.card Bs := by
    rw [← hcardH]
    exact hle
  have hmul := CFSG.StandardType.NbrU63.card_range_ggGamma_mul_card_inf (Bs := Bs) (K := X) hN
  have hfinal : 3 ^ 5 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      Nat.card (ggGamma X hN).range *
        Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    rw [hmul]
    exact hle'
  exact Nat.le_of_mul_le_mul_right hfinal Nat.card_pos

theorem exists_mem_centralizer_not_mem_centralizer {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {X : Subgroup G} {z : G}
    (hXz : (X = L ∧ z = x) ∨ (X = K ∧ z = y)) :
    ∃ d ∈ Bs, d ∈ Subgroup.centralizer (J : Set G) ∧ d ∉ Subgroup.centralizer (X : Set G) := by
  have hpre : LargeEvenStdSubPre 3 B x L D J := hH.1.2.2.1
  have hDBs : D ≤ Bs := hpre.1.trans hH.1.2.1.1
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  have hnb : LargeEvenNeighbor 3 x y K D J := hH.2.2.2.2.1.2
  have hxD : x ∈ D := hpre.2.2.2.1
  have hyD : y ∈ D := by
    rw [hnb.1]
    exact Subgroup.subset_closure (by simp)
  have hxBs : x ∈ Bs := hDBs hxD
  have hyBs : y ∈ Bs := hDBs hyD
  have hxCJ : x ∈ Subgroup.centralizer (J : Set G) :=
    (Subgroup.mem_inf.mp (hDeq ▸ hxD)).2
  have hyCJ : y ∈ Subgroup.centralizer (J : Set G) :=
    (Subgroup.mem_inf.mp (hDeq ▸ hyD)).2
  rcases hXz with ⟨hXL, -⟩ | ⟨hXK, -⟩
  ·
    rw [hXL]
    refine ⟨y, hyBs, hyCJ, ?_⟩
    intro hyL
    have hxL : x ∈ Subgroup.centralizer (L : Set G) := (GGConfig.data_L hH.1).1
    have hDCL : D ≤ Subgroup.centralizer (L : Set G) := by
      rw [hnb.1, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hxL
      · exact hyL
    have hDp : IsPGroup 3 D := CFSG.Open.IsElemAbelian.isPGroup hpre.2.1
    have hDcyc : IsCyclic ↥D :=
      hH.1.1.2.2.2.2.2.2.1.2.2.2.2 D hDCL hDp
    exact (CFSG.StandardType.TableB.not_isCyclic_of_card (p := 3) (by norm_num)
      hpre.2.1.2 (le_of_eq hpre.2.2.1.symm)) hDcyc
  ·
    rw [hXK]
    refine ⟨x, hxBs, hxCJ, ?_⟩
    intro hxK
    have hzpx : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hxK
    have hKzpx : K ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
      Subgroup.le_centralizer_iff.mp hzpx
    have hbot : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKzpx
    exact hnb.2.2 (by rw [hbot]; exact bot_le)

end CFSG.StandardType.E6D4Tw

end

module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Single
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HSThree
public import CFSG.Quasithin.Background.A318POutMore

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.RankThree.Native CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

theorem card_closure_pair_le_three {G : Type} [Group G] [Finite G] {a b c : G} (hc : c ^ 3 = 1)
    (ha : a ∈ Subgroup.zpowers c) (hb : b ∈ Subgroup.zpowers c) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ 3 := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.zpowers c := by
    rw [Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · assumption
    · assumption
  have hcard : Nat.card (Subgroup.zpowers c) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc)
  exact (Subgroup.card_le_of_le hle).trans hcard

theorem hs_conj_hsXp_of_orderOf_three
    (a : NativeSporadic.HS) (ha : orderOf a = 3) :
    ∃ g : hs100P, g * hs100Equiv a * g⁻¹ = hsXp := by
  have h3 : a ^ 3 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hpow : hs100Equiv a ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hne : hs100Equiv a ≠ 1 := fun h => ha1 (hs100Equiv.injective (by rw [h, map_one]))
  exact exists_conj_hsXp (hs100Equiv a) hpow hne

theorem hs_isConj_of_orderOf_three
    (a b : NativeSporadic.HS) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ k : NativeSporadic.HS, k * a * k⁻¹ = b := by
  obtain ⟨g, hg⟩ := hs_conj_hsXp_of_orderOf_three a ha
  obtain ⟨h, hh⟩ := hs_conj_hsXp_of_orderOf_three b hb
  refine ⟨hs100Equiv.symm (h⁻¹ * g), hs100Equiv.injective ?_⟩
  have ea : hs100Equiv a = g⁻¹ * hsXp * g := by rw [← hg]; group
  have eb : hs100Equiv b = h⁻¹ * hsXp * h := by rw [← hh]; group
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [ea, eb]
  group

theorem listRow_hs :
    ListRow NativeSporadic.HS := by
  obtain ⟨x, y, -, hx3, hy3, hxy, hcard, -⟩ := CFSG.SectionRank.HS_sylow3_square_witness
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h9 := card_closure_pair_le_three (c := y) hy3 (Subgroup.one_mem _)
      (Subgroup.mem_zpowers y)
    rw [hcard] at h9
    norm_num at h9
  have hn : y ∉ Subgroup.zpowers x := by
    intro hy
    have h9 := card_closure_pair_le_three (c := x) hx3 (Subgroup.mem_zpowers x) hy
    rw [hcard] at h9
    norm_num at h9
  exact listRow_of_single_class hs_isConj_of_orderOf_three (orderOf_eq_prime hx3 hx1) hy3 hxy hn

theorem outerRow_hs :
    OuterRow NativeSporadic.HS :=
  outerRow_of_not_three_dvd_outer
    (CFSG.Quasithin.A318P.not_dvd_outer_HS (S := NativeSporadic.HS) (MulEquiv.refl _)
      Nat.prime_three (by norm_num))

theorem row_carrier_hs :
    RowOf (NativeSporadic.Carrier .HS) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.HS) e.symm ⟨listRow_hs, outerRow_hs⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

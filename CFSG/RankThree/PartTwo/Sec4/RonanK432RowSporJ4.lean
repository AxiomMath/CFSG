module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Single
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open scoped commutatorElement

instance finite_j4_of_cert : Finite NativeSporadic.J4 :=
  CFSG.Sporadic.J4.fam_j4_simplicity.1

private theorem j4_pow_mul_eq_of_comm {G : Type} [Group G] {x y c : G}
    (hxy : x * y = c * (y * x)) (hcx : Commute c x) (n : ℕ) :
    x ^ n * y = c ^ n * (y * x ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxc : x * c ^ n = c ^ n * x := ((hcx.symm).pow_right n).eq
    calc x ^ (n + 1) * y = x * (x ^ n * y) := by rw [pow_succ', mul_assoc]
      _ = x * (c ^ n * (y * x ^ n)) := by rw [ih]
      _ = (x * c ^ n) * (y * x ^ n) := by rw [mul_assoc]
      _ = (c ^ n * x) * (y * x ^ n) := by rw [hxc]
      _ = c ^ n * (x * y) * x ^ n := by simp only [mul_assoc]
      _ = c ^ n * (c * (y * x)) * x ^ n := by rw [hxy]
      _ = c ^ (n + 1) * (y * x ^ (n + 1)) := by
        rw [pow_succ c n, pow_succ' x n]; simp only [mul_assoc]

private theorem j4_pow_three_eq_one {G : Type} [Group G] {x y c : G} (hx : x ^ 3 = 1)
    (hxy : x * y = c * (y * x)) (hcx : Commute c x) : c ^ 3 = 1 := by
  have h := j4_pow_mul_eq_of_comm hxy hcx 3
  rw [hx, one_mul, mul_one] at h
  have h' : c ^ 3 * y = 1 * y := by rw [one_mul]; exact h.symm
  exact mul_right_cancel h'

private theorem j4_notMem_zpowers {G : Type} [Group G] {x y c : G} (hx : x ^ 3 = 1)
    (hc1 : c ≠ 1) (hcy : Commute c y) (hnc : x * y ≠ y * x) : c ∉ Subgroup.zpowers x := by
  intro hmem
  rcases mem_zpowers_cases_of_pow_three hx hmem with h | h | h
  · exact hc1 h
  · rw [h] at hcy
    exact hnc hcy.eq
  · rw [h, Commute.inv_left_iff] at hcy
    exact hnc hcy.eq

theorem j4_isConj_of_orderThree :
    ∀ a b : NativeSporadic.J4, orderOf a = 3 → orderOf b = 3 →
      ∃ k : NativeSporadic.J4, k * a * k⁻¹ = b := by
  obtain ⟨φ⟩ : Nonempty (NativeSporadic.J4 ≃* ↥CFSG.Sporadic.J4.J) :=
    ⟨CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat⟩
  have toCE : ∀ c : NativeSporadic.J4, orderOf c = 3 →
      ∃ g : ↥CFSG.Sporadic.J4.J, g * φ c * g⁻¹ = CFSG.Quasithin.J4M2.cE := by
    intro c hc
    have hc3 : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hc
      exact absurd hc (by norm_num)
    have hφ3 : φ c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have hφ1 : φ c ≠ 1 := fun h => hc1 (φ.injective (h.trans (map_one φ).symm))
    exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_conj_cE_of_orderThree (φ c) hφ3 hφ1
  intro a b ha hb
  obtain ⟨ga, hga⟩ := toCE a ha
  obtain ⟨gb, hgb⟩ := toCE b hb
  refine ⟨φ.symm (gb⁻¹ * ga), φ.injective ?_⟩
  have ha' : φ a = ga⁻¹ * CFSG.Quasithin.J4M2.cE * ga := by rw [← hga]; group
  have hb' : φ b = gb⁻¹ * CFSG.Quasithin.J4M2.cE * gb := by rw [← hgb]; group
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ha', hb']
  group

theorem listRow_j4 :
    ListRow NativeSporadic.J4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, -, hx3, -, hxy, hcx, hcy, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hxy (commutatorElement_one_left _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hnc : x * y ≠ y * x := fun h => hxy (commutatorElement_eq_one_iff_mul_comm.2 h)
  have hxyc : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  have hc3 : ⁅x, y⁆ ^ 3 = 1 := j4_pow_three_eq_one hx3 hxyc hcx
  have hxc : x * ⁅x, y⁆ = ⁅x, y⁆ * x := hcx.eq.symm
  exact listRow_of_single_class j4_isConj_of_orderThree hxo hc3 hxc
    (j4_notMem_zpowers hx3 hxy hcy hnc)

theorem outerRow_j4 :
    OuterRow NativeSporadic.J4 :=
  outerRow_of_not_three_dvd_outer (S := NativeSporadic.J4) CFSG.Quasithin.qSporOutTwo_holds

theorem row_carrier_j4 :
    RowOf (NativeSporadic.Carrier .J4) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.J4) e.symm ⟨listRow_j4, outerRow_j4⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432

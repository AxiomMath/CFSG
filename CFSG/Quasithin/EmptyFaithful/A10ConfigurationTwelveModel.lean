module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationNineModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

def x3m : Wc := ⟨c3, 1, false⟩

theorem x3m_cube : x3m * x3m * x3m = 1 := by decide +kernel

theorem x3m_ne_one : x3m ≠ 1 := by decide +kernel

theorem x3m_norm : ∀ e ∈ E0h, x3m * e * x3m⁻¹ ∈ E0h := by decide +kernel

theorem x3m_norm_inv : ∀ e ∈ E0h, x3m⁻¹ * e * x3m ∈ E0h := by decide +kernel

theorem x3m_comm_H1m : ∀ y ∈ H1m, x3m * y = y * x3m := by decide +kernel

theorem x3m_not_cent : ∃ e ∈ E0h, x3m * e ≠ e * x3m := by decide +kernel

theorem t0'_mem_V2 : t0' ∈ baseSub ⊥ V := by decide +kernel

theorem T2h_cent_H1m : ∀ w ∈ T2h, (∀ y ∈ H1m, w * y = y * w) → w = 1 := by decide +kernel

def fm : Wc := ⟨f1, 1, false⟩

theorem fm_norm : ∀ e ∈ E0h, fm * e * fm⁻¹ ∈ E0h := by decide +kernel

theorem fm_norm_inv : ∀ e ∈ E0h, fm⁻¹ * e * fm ∈ E0h := by decide +kernel

theorem fm_comm_M2 : ∀ y ∈ M2h, fm * y = y * fm := by decide +kernel

theorem M2h_decomp : ∀ y ∈ M2h, ∃ a ∈ H1m, ∃ w ∈ T2h, y = a * w := by decide +kernel

theorem card_M2h : Nat.card M2h = 24 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem fm_pts : ∃ i : Fin 5, i ≠ 0 ∧ fm = ptm false 0 * ptm false i ∧
    ptm false (s3 0) * ptm false (s3 i) ≠ ptm false 0 * ptm false i := by
  decide +kernel

end CFSG.Quasithin.A10

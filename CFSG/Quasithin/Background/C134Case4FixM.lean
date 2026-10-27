module

public import CFSG.Quasithin.Background.C134Case4Fix
public import CFSG.Quasithin.Background.C134L32CorrM

public section

namespace CFSG.Quasithin.C134Case4Fix

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem exists_memW [Finite G] {G₀ R L : Subgroup G}
    (h4 : C134Case4Min G₀ R L) (hR : IsPGroup 2 R) (hRG : R ≤ G₀)
    (hRL : R ≤ Subgroup.normalizer (L : Set G)) (hQR : c134Q G₀ L ≤ R) :
    ∃ c ∈ c134CQ G₀ L, c ≠ 1 ∧ c ∈ quasithinOmegaOneCenter R := by
  classical
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, hW1⟩, -⟩ := h4
  set W := c134CQ G₀ L with hW
  have hWR : W ≤ R := inf_le_left.trans hQR
  obtain ⟨c₀, hc₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot hR hWR (le_normalizer_c134CQ hRG hRL) hW1)
  have hc₀W : (c₀ : G) ∈ W := c₀.2.1
  have hc₀C : (c₀ : G) ∈ Subgroup.centralizer (R : Set G) := c₀.2.2
  have hc₀R : (c₀ : G) ∈ R := hWR hc₀W
  have hc₀1' : (c₀ : G) ≠ 1 := fun h => hc₀1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨(c₀ : G), hc₀R⟩
  have hk' : orderOf (c₀ : G) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨(c₀ : G), hc₀R⟩ : ↥R)
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk'
    exact hc₀1' hk'
  set c : G := (c₀ : G) ^ 2 ^ (k - 1) with hc
  have hcW : c ∈ W := Subgroup.pow_mem _ hc₀W _
  have hcC : c ∈ Subgroup.centralizer (R : Set G) := Subgroup.pow_mem _ hc₀C _
  have hc2 : c ^ 2 = 1 := by
    rw [hc, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk1), ← hk']
    exact pow_orderOf_eq_one _
  have hc1 : c ≠ 1 := by
    intro h1
    have hdvd : 2 ^ k ∣ 2 ^ (k - 1) := hk' ▸ orderOf_dvd_of_pow_eq_one h1
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hlt : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨c, hcW, hc1, ?_⟩
  exact Subgroup.subset_closure ⟨⟨hWR hcW, hcC⟩, hc2⟩

end CFSG.Quasithin.C134Case4Fix

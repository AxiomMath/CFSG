module

public import CFSG.Quasithin.H13.A6S1372Twelve

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace A6Seventeen

theorem eq_top_of_swap_four {P : Subgroup (Perm (Fin 6))}
    (h : ∀ i : Fin 6, i ≠ 4 → swap i 4 ∈ P) : P = ⊤ := by
  have hsw : ∀ x y : Fin 6, x ≠ y → swap x y ∈ P := by
    intro x y hxy
    by_cases hx : x = 4
    · subst hx
      rw [swap_comm]
      exact h y (Ne.symm hxy)
    by_cases hy : y = 4
    · subst hy
      exact h x hx
    have key : ∀ x y : Fin 6, x ≠ 4 → y ≠ 4 → x ≠ y →
        swap x y = swap x 4 * swap y 4 * swap x 4 := by decide
    rw [key x y hx hy hxy]
    exact P.mul_mem (P.mul_mem (h x hx) (h y hy)) (h x hx)
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  exact hsw x y hxy

theorem swap_four_words : ∀ i : Fin 6, i ≠ 4 →
    swap i 4 = swap 4 5 ∨ swap i 4 = swap 3 4 ∨
      swap i 4 = (swap 0 1 * swap 2 3) * swap 3 4 * (swap 0 1 * swap 2 3) ∨
      swap i 4 = (swap 0 2 * swap 1 3) * swap 3 4 * (swap 0 2 * swap 1 3) ∨
      swap i 4 = (swap 0 2 * swap 1 3) * ((swap 0 1 * swap 2 3) * swap 3 4 *
        (swap 0 1 * swap 2 3)) * (swap 0 2 * swap 1 3) := by
  decide

theorem eq_top_of_gens {P : Subgroup (Perm (Fin 6))} (h1 : swap 4 5 ∈ P) (h2 : swap 3 4 ∈ P)
    (h3 : swap 0 1 * swap 2 3 ∈ P) (h4 : swap 0 2 * swap 1 3 ∈ P) : P = ⊤ := by
  refine eq_top_of_swap_four fun i hi => ?_
  rcases swap_four_words i hi with h | h | h | h | h <;> rw [h]
  · exact h1
  · exact h2
  · exact P.mul_mem (P.mul_mem h3 h2) h3
  · exact P.mul_mem (P.mul_mem h4 h2) h4
  · exact P.mul_mem (P.mul_mem h4 (P.mul_mem (P.mul_mem h3 h2) h3)) h4

theorem R8_gens : swap (0 : Fin 6) 1 * swap 2 3 ∈ R8 ∧ swap (0 : Fin 6) 2 * swap 1 3 ∈ R8 := by
  decide

end A6Seventeen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

omit hhat in
theorem exists_mul_of_mem_LT
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14) {l : G} (hl : l ∈ L ⊔ T) :
    ∃ a ∈ C.I ⊔ pCoreOf 2 H, a⁻¹ * l ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  have hQN := S.QH_le_NV hNS h13315 h1356two hH
  have hIN := C.I_le_NV hNS h13315 h1356two hH hab
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  set P : Subgroup (Perm (Fin 6)) :=
    ((C.I ⊔ pCoreOf 2 H).subgroupOf (Subgroup.normalizer (V : Set G))).map S.frame.ρ with hP
  have hmemP : ∀ a : G, ∀ ha : a ∈ Subgroup.normalizer (V : Set G), a ∈ C.I ⊔ pCoreOf 2 H →
      S.frame.ρ ⟨a, ha⟩ ∈ P := fun a ha h => ⟨⟨a, ha⟩, h, rfl⟩
  have hR8 := S.R8_le_rho_QH hNS h13315 h1356two hH hab h13314 hna
  have hP1 : swap 4 5 ∈ P := by
    rw [← C.rho_v]
    exact hmemP _ C.v.2 (Subgroup.mem_sup_left (C.v_mem_I))
  have hP2 : swap 3 4 ∈ P := by
    rw [← C.rho_w]
    exact hmemP _ C.w.2 (Subgroup.mem_sup_left (C.w_mem_I))
  have hPR : ∀ σ ∈ R8, σ ∈ P := by
    intro σ hσ
    obtain ⟨q, hq, hqN, hρq⟩ := hR8 σ hσ
    rw [← hρq]
    exact hmemP _ hqN (Subgroup.mem_sup_right hq)
  have htop := A6Seventeen.eq_top_of_gens hP1 hP2 (hPR _ A6Seventeen.R8_gens.1)
    (hPR _ A6Seventeen.R8_gens.2)
  have hlN := hLTN hl
  have hmem : S.frame.ρ ⟨l, hlN⟩ ∈ P := by rw [htop]; trivial
  obtain ⟨⟨a, haN⟩, ha, hρa⟩ := hmem
  have ha' : a ∈ C.I ⊔ pCoreOf 2 H := ha
  refine ⟨a, ha', ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem ?_) hl, ?_⟩⟩
  · exact sup_le (C.I_le_LT hNS h13315 h1356two hH hab)
      ((S.QH_le_T hNS h13315 h1356two hH).trans le_sup_right) ha'
  · have h1 : S.frame.ρ (⟨a, haN⟩⁻¹ * ⟨l, hlN⟩) = 1 := by
      rw [map_mul, map_inv, hρa, inv_mul_cancel]
    have := (S.rho_eq_one_iff _).1 h1
    simpa using this

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6

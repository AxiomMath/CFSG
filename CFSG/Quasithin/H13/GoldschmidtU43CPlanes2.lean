module

public import CFSG.Quasithin.H13.GoldschmidtU43CAut

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

set_option synthInstance.maxSize 1024

@[expose] def pw3 (c : Fin 4 → V4) : ℕ → Fin 4 → V4
  | 0 => idc
  | 1 => c
  | _ => comp c c

@[expose] def pwA {M : Type*} [Monoid M] (g : M) : ℕ → M
  | 0 => 1
  | 1 => g
  | _ => g * g

theorem rbar_gen : ∀ s : OC, SwapC s.cols → comp s.cols s.cols = idc → ∀ ρ : OC,
    Cube1 ρ.cols → ρ.cols ≠ idc → (∀ v, InP2 v → app ρ.cols v = v) → ∀ r : OC, Cube1 r.cols →
      ∃ i < 3, ∃ j < 3,
        r.cols = comp (pw3 ρ.cols i) (pw3 (comp s.cols (comp ρ.cols s.cols)) j) := by
  decide +kernel

theorem pw3_colsOf (g : MulAut (Multiplicative V4)) (i : ℕ) :
    pw3 (colsOf g) i = colsOf (pwA g i) := by
  rcases i with _ | _ | i
  · exact colsOf_one.symm
  · rfl
  · show comp (colsOf g) (colsOf g) = colsOf (g * g)
    rw [colsOf_mul]

theorem Rbar_gen {s ρ r : MulAut (Multiplicative V4)} (hs : s ∈ Oq) (hsw : SwapA s)
    (hs2 : s * s = 1) (hρ : ρ ∈ Rbar) (hne : ρ ≠ 1) (hfix : ∀ v, InP2 v → vapp ρ v = v)
    (hr : r ∈ Rbar) : ∃ i < 3, ∃ j < 3, r = pwA ρ i * pwA (s * ρ * s) j := by
  have key := rbar_gen (toOC ⟨s, hs⟩) (by rw [toOC_mk_cols, swapC_iff]; exact hsw)
    (by rw [toOC_mk_cols, comp_eq_idc_iff]; exact hs2) (toOC ⟨ρ, hρ.1⟩)
    (by rw [toOC_mk_cols, cube1_iff]; exact hρ.2)
    (by rw [toOC_mk_cols]; exact fun h => hne ((cols_eq_idc_iff ρ).1 h))
    (by
      intro v hv
      rw [toOC_mk_cols, ← vapp_eq_app]
      exact hfix v hv) (toOC ⟨r, hr.1⟩) (by rw [toOC_mk_cols, cube1_iff]; exact hr.2)
  obtain ⟨i, hi, j, hj, hij⟩ := key
  refine ⟨i, hi, j, hj, ?_⟩
  simp only [toOC_mk_cols] at hij
  have e2 : comp (colsOf s) (comp (colsOf ρ) (colsOf s)) = colsOf (s * ρ * s) := by
    rw [← colsOf_mul, ← colsOf_mul, mul_assoc]
  rw [e2, pw3_colsOf, pw3_colsOf, ← colsOf_mul, colsOf_eq_iff] at hij
  exact hij

end CFSG.Quasithin.H13.U43

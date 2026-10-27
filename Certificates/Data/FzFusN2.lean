module

public import Certificates.Data.FzFusN

public section

namespace Certificates.FzFus

open Certificates.FzJ36

theorem phi_ne_one_tbl : ∀ s ∈ subTable, phi s.1 s.2.1 (mkE 1 1 (qL 1)) ≠ 1 := by
  decide +kernel

theorem phi_surj_tbl (s : Fin 4 × Fin 4 × List Cls) (hs : s ∈ subTable) :
    Function.Surjective (phi s.1 s.2.1) := by
  have hz : ∀ e : Z2, e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
  intro z
  rcases hz z with rfl | rfl
  · exact ⟨1, map_one _⟩
  · refine ⟨mkE 1 1 (qL 1), ?_⟩
    rcases hz (phi s.1 s.2.1 (mkE 1 1 (qL 1))) with h | h
    · exact absurd h (phi_ne_one_tbl s hs)
    · exact h

theorem phi_keq_one (u v : Fin 4) {m : Model} (h : KEq m 1) : phi u v m = 1 := by
  rcases h with rfl | rfl
  · exact map_one _
  · rw [one_mul]
    exact phi_zeta u v

end Certificates.FzFus

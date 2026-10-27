module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Cox
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cls

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

section Model

theorem s3_decomp : ∃ μ ∈ Uh, p10sA 2 = fhatA * xA * μ := by
  have hex : ∃ u ∈ UL, comp (comp fhatL xL) u = p10sL.getD 2 idL := by decide +kernel
  obtain ⟨u, hu, hl⟩ := hex
  obtain ⟨μ, -, hμ⟩ := exists_That_of_mem_Thl (UL_check.2.2.2.2.1 u hu).1
  refine ⟨μ, ⟨u, hu, hμ⟩, ?_⟩
  have h1 : RepL (p10sL.getD 2 idL) ((fhatA * xA * μ : Ah) : P45) := by
    rw [← hl]
    exact repL_mul (repL_mul repL_fhat repL_x) hμ
  exact Subtype.ext (eq_of_repL (repL_p10sA 2) h1)

theorem aW_conj_eq {w : List ℕ} {x y : Ah} {xl yl : PL} (hx : RepL xl (x : P45))
    (hy : RepL yl (y : P45)) (h : conjWL xl w = yl) : aW w * x * (aW w)⁻¹ = y :=
  Subtype.ext (eq_of_repL (repL_conjW hx w) (h ▸ hy))

theorem aW_comm_fhat {w : List ℕ} (h : comp (evalAL w) fhatL = comp fhatL (evalAL w)) :
    aW w * fhatA = fhatA * aW w :=
  comm_of_comp_comm (v := fhatA) repL_fhat (repL_aW w) h

theorem conj_s1 : aW [3, 2, 0, 1, 1, 0, 2] * p10sA 2 * (aW [3, 2, 0, 1, 1, 0, 2])⁻¹ = p10sA 0 :=
  aW_conj_eq (repL_p10sA 2) (repL_p10sA 0) (by decide +kernel)

theorem conj_s5 : aW [0, 2, 0, 1] * p10sA 2 * (aW [0, 2, 0, 1])⁻¹ = p10sA 4 :=
  aW_conj_eq (repL_p10sA 2) (repL_p10sA 4) (by decide +kernel)

theorem conj_s6 : aW [1, 0, 2] * p10sA 2 * (aW [1, 0, 2])⁻¹ = p10sA 5 :=
  aW_conj_eq (repL_p10sA 2) (repL_p10sA 5) (by decide +kernel)

theorem conj_t : aW [2, 0, 1] * p10sA 2 * (aW [2, 0, 1])⁻¹ = p10tA :=
  aW_conj_eq (repL_p10sA 2) (repL_wordSA [3, 1, 2, 3, 4, 3, 1, 2, 3]) (by decide +kernel)

theorem comm_s1 : aW [3, 2, 0, 1, 1, 0, 2] * fhatA = fhatA * aW [3, 2, 0, 1, 1, 0, 2] :=
  aW_comm_fhat (by decide +kernel)

theorem comm_s5 : aW [0, 2, 0, 1] * fhatA = fhatA * aW [0, 2, 0, 1] :=
  aW_comm_fhat (by decide +kernel)

theorem comm_s6 : aW [1, 0, 2] * fhatA = fhatA * aW [1, 0, 2] :=
  aW_comm_fhat (by decide +kernel)

theorem comm_t : aW [2, 0, 1] * fhatA = fhatA * aW [2, 0, 1] :=
  aW_comm_fhat (by decide +kernel)

end Model

end CFSG.Quasithin.H13.F431.U42Aut

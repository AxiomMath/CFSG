module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bInv

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def nfix (σ : P45) : ℕ := (Finset.univ.filter fun i : Fin 45 => σ i = i).card

theorem nfix_conj (c σ : P45) : nfix (c * σ * c⁻¹) = nfix σ := by
  have key : ∀ i : Fin 45, (c * σ * c⁻¹) i = i ↔ σ (c⁻¹ i) = c⁻¹ i := by
    intro i
    constructor
    · intro h
      have := congrArg (fun x => c⁻¹ x) h
      simpa using this
    · intro h
      show c (σ (c⁻¹ i)) = i
      rw [h]
      simp
  unfold nfix
  refine Finset.card_equiv c⁻¹ fun i => ?_
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact key i

@[expose] def nfixL (l : List ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin 45 => l.getD i 0 = i.val).card

theorem nfix_of_repL {l : List ℕ} {σ : P45} (h : RepL l σ) : nfix σ = nfixL l := by
  unfold nfix nfixL
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [h.2 i, Fin.ext_iff]

theorem nfixL_x : nfixL xL = 13 := by decide +kernel

theorem nfixL_t0 : nfixL (Tl.getD 20 []) = 5 := by decide +kernel

theorem not_isConj_t0A_xA : ¬ IsConj t0A xA := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h1 : (c : P45) * (t0A : P45) * (c : P45)⁻¹ = (xA : P45) := congrArg Subtype.val hc
  have h2 := nfix_conj (c : P45) (t0A : P45)
  rw [h1, nfix_of_repL (show RepL xL (xA : P45) from repL_x),
    nfix_of_repL repL_t0A, nfixL_x, nfixL_t0] at h2
  exact absurd h2 (by decide)

end CFSG.Quasithin.H13.F431.U42Aut

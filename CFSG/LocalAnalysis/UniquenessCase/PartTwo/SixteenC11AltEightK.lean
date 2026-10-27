module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11AltCrit
public import CFSG.Permutation.FinPackCount
public import CFSG.Permutation.FinPackVec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16C11AltEightK

open Equiv Finset CFSG.Permutation.FinPack

theorem h16 : 8 ≤ 16 := by norm_num

@[expose] def eqvK (a b u : ℕ) : Bool := Nat.beq u a || Nat.beq u b

theorem eqv_iff {w u : Fin 8 → ZMod 2} {a b : ℕ} (ha : vcode w = a)
    (hb : vcode (fun i => w i + 1) = b) : S16C11AltEqv w u ↔ eqvK a b (vcode u) = true := by
  rw [S16C11AltEqv, eqvK, Bool.or_eq_true, ← ha, ← hb, beq_vcode_iff, beq_vcode_iff]

theorem vcode_pact (v : Fin 8 → ZMod 2) (τ : Perm (Fin 8)) :
    vcode (S16C11AltPact τ⁻¹ v) = mulK 8 (vcode v) (enc τ) :=
  vcode_inv_apply h16 v τ

@[expose] def inT (u : ℕ) : Bool :=
  eqvK 4369 286326784 u || (eqvK 1114129 285217024 u || eqvK 285212689 1118464 u)

@[expose] noncomputable def qT (d : ℕ) : Bool :=
  eqvK 4369 286326784 (mulK 8 4369 d) &&
    (inT (mulK 8 4369 d) && (inT (mulK 8 1114129 d) && inT (mulK 8 285212689 d)))

theorem cnt_T : cntK 8 qT 8 0 0 0 = 128 := by decide +kernel

theorem card_T (x₀ xa xb : Fin 8 → ZMod 2) (h0 : vcode x₀ = 4369)
    (h0' : vcode (fun i => x₀ i + 1) = 286326784) (ha : vcode xa = 1114129)
    (ha' : vcode (fun i => xa i + 1) = 285217024) (hb : vcode xb = 285212689)
    (hb' : vcode (fun i => xb i + 1) = 1118464) :
    (univ.filter fun g : Perm (Fin 8) =>
      S16C11AltEqv x₀ (S16C11AltPact g x₀) ∧ S16C11AltTriple x₀ xa xb g).card = 128 := by
  rw [card_filter_inv, ← cnt_T, ← card_filter_eq_cntK]
  refine congrArg Finset.card (Finset.filter_congr fun τ _ => ?_)
  simp only [S16C11AltTriple, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, exists_eq_or_imp, exists_eq, exists_eq_left, eqv_iff h0 h0', eqv_iff ha ha', eqv_iff hb hb',
    vcode_pact, h0, ha, hb, qT, inT, Bool.and_eq_true, Bool.or_eq_true]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16C11AltEightK

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 L0S image_lineSet lineSet_eq_of_sameSet)
open scoped Pointwise

@[expose] def wv : List ℕ := [1, 1, 3, 0, 1, 0, 2, 3, 0, 2, 2, 0]

@[expose] def wb : List ℕ := [2, 3, 0, 2, 2, 3, 2, 2, 0, 2]

@[expose] def wx : List ℕ := [3, 2, 3, 2, 3, 1, 1, 3, 0, 1, 3, 2, 2]

theorem a4_check :
    comp (evalAL wv) (evalAL wv) = idL ∧ comp (evalAL wb) (comp (evalAL wb) (evalAL wb)) = idL ∧
    comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb)) ≠ evalAL wv ∧
    comp (evalAL wv) (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))) =
      comp (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))) (evalAL wv) ∧
    comp (comp (evalAL wb) (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))))
      (evalAL (invAL wb)) =
      comp (evalAL wv) (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))) ∧
    (evalAL wv).getD 0 0 = 0 ∧ sameSet (imgSet (evalAL wv) L0) L0 = true ∧
    (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))).getD 0 0 = 0 ∧
    sameSet (imgSet (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))) L0) L0 = true ∧
    sameSet (imgSet (evalAL wb) L0) L0 = true ∧ (evalAL wx).getD 0 0 = 0 := by
  decide +kernel

theorem a4_check_f :
    comp (evalAL wv) fhatL = comp fhatL (evalAL wv) ∧
    comp (evalAL wb) fhatL = comp fhatL (evalAL wb) ∧
    comp (evalAL wx) fhatL = comp fhatL (evalAL wx) ∧
    comp (comp (evalAL wv) (comp (comp (evalAL wx) (evalAL wv)) (evalAL (invAL wx))))
      (comp (comp (evalAL wv) (comp (comp (evalAL wx) (evalAL wv)) (evalAL (invAL wx))))
        (comp (evalAL wv) (comp (comp (evalAL wx) (evalAL wv)) (evalAL (invAL wx))))) = idL ∧
    comp (evalAL wv) (comp (comp (evalAL wx) (evalAL wv)) (evalAL (invAL wx))) ≠ idL := by
  decide +kernel

@[expose] def vA : Ah := ⟨wordAP wv, wordAP_mem wv⟩

@[expose] def bA : Ah := ⟨wordAP wb, wordAP_mem wb⟩

@[expose] def xwA : Ah := ⟨wordAP wx, wordAP_mem wx⟩

theorem repL_vA : RepL (evalAL wv) (vA : P45) := repL_wordAP wv

theorem repL_bA : RepL (evalAL wb) (bA : P45) := repL_wordAP wb

theorem repL_xwA : RepL (evalAL wx) (xwA : P45) := repL_wordAP wx

theorem repL_bA_inv : RepL (evalAL (invAL wb)) ((bA⁻¹ : Ah) : P45) := by
  have : ((bA⁻¹ : Ah) : P45) = wordAP (invAL wb) := by
    rw [wordAP_invAL]
    rfl
  rw [this]
  exact repL_wordAP _

theorem repL_xwA_inv : RepL (evalAL (invAL wx)) ((xwA⁻¹ : Ah) : P45) := by
  have : ((xwA⁻¹ : Ah) : P45) = wordAP (invAL wx) := by
    rw [wordAP_invAL]
    rfl
  rw [this]
  exact repL_wordAP _

theorem mem_P1h_of_repL {g : Ah} {l : PL} (h : RepL l (g : P45)) (h0 : l.getD 0 0 = 0) :
    g ∈ P1h := by
  rw [mem_P1h_iff]
  apply Fin.ext
  rw [← h.2 0]
  exact h0

theorem mem_P2h_of_repL {g : Ah} {l : PL} (h : RepL l (g : P45))
    (h0 : sameSet (imgSet l L0) L0 = true) : g ∈ P2h := by
  rw [mem_P2h_iff, L0S, image_lineSet h (by decide), lineSet_eq_of_sameSet h0]

theorem eq_of_repL_eq {g h : Ah} {l m : PL} (hg : RepL l (g : P45)) (hh : RepL m (h : P45))
    (hlm : l = m) : g = h := Subtype.ext (eq_of_repL hg (hlm ▸ hh))

@[expose] def wA : Ah := bA * vA * bA⁻¹

theorem repL_wA : RepL (comp (comp (evalAL wb) (evalAL wv)) (evalAL (invAL wb))) (wA : P45) :=
  repL_mul (repL_mul repL_bA repL_vA) repL_bA_inv

theorem vA_sq : vA * vA = 1 :=
  eq_of_repL_eq (repL_mul repL_vA repL_vA) (repL_one 45) a4_check.1

theorem bA_cube : bA * bA * bA = 1 := by
  have h : RepL (comp (evalAL wb) (comp (evalAL wb) (evalAL wb))) ((bA * (bA * bA) : Ah) : P45) :=
    repL_mul repL_bA (repL_mul repL_bA repL_bA)
  rw [mul_assoc]
  exact eq_of_repL_eq h (repL_one 45) a4_check.2.1

theorem wA_ne_vA : wA ≠ vA := fun h => a4_check.2.2.1 (repL_unique repL_wA (h ▸ repL_vA))

theorem vA_comm_wA : vA * wA = wA * vA :=
  eq_of_repL_eq (repL_mul repL_vA repL_wA) (repL_mul repL_wA repL_vA) a4_check.2.2.2.1

theorem bA_rel : bA * wA * bA⁻¹ = vA * wA :=
  eq_of_repL_eq (repL_mul (repL_mul repL_bA repL_wA) repL_bA_inv) (repL_mul repL_vA repL_wA)
    a4_check.2.2.2.2.1

theorem vA_mem_Bh : vA ∈ Bh :=
  ⟨mem_P1h_of_repL repL_vA a4_check.2.2.2.2.2.1, mem_P2h_of_repL repL_vA a4_check.2.2.2.2.2.2.1⟩

theorem bA_mem_P2h : bA ∈ P2h :=
  mem_P2h_of_repL repL_bA a4_check.2.2.2.2.2.2.2.2.2.1

theorem xwA_mem_P1h : xwA ∈ P1h :=
  mem_P1h_of_repL repL_xwA a4_check.2.2.2.2.2.2.2.2.2.2

theorem vA_comm_f : vA * fhatA = fhatA * vA :=
  eq_of_repL_eq (repL_mul repL_vA repL_fhat) (repL_mul repL_fhat repL_vA) a4_check_f.1

theorem bA_comm_f : bA * fhatA = fhatA * bA :=
  eq_of_repL_eq (repL_mul repL_bA repL_fhat) (repL_mul repL_fhat repL_bA) a4_check_f.2.1

theorem xwA_comm_f : xwA * fhatA = fhatA * xwA :=
  eq_of_repL_eq (repL_mul repL_xwA repL_fhat) (repL_mul repL_fhat repL_xwA) a4_check_f.2.2.1

@[expose] def uA : Ah := vA * (xwA * vA * xwA⁻¹)

theorem repL_uA : RepL (comp (evalAL wv) (comp (comp (evalAL wx) (evalAL wv)) (evalAL (invAL wx))))
    (uA : P45) := repL_mul repL_vA (repL_mul (repL_mul repL_xwA repL_vA) repL_xwA_inv)

theorem uA_cube : uA * (uA * uA) = 1 :=
  eq_of_repL_eq (repL_mul repL_uA (repL_mul repL_uA repL_uA)) (repL_one 45) a4_check_f.2.2.2.1

theorem uA_ne_one : uA ≠ 1 := fun h => a4_check_f.2.2.2.2 (repL_unique repL_uA (h ▸ repL_one 45))

end CFSG.Quasithin.H13.F431.U42Aut

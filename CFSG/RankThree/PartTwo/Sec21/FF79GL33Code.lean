module

public import Certificates.Data.CFSGNative.GL33.Check
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.GL33

abbrev Vec := Fin 3 → ZMod 3

abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 3)

@[expose] def decV (r : ℕ) : Vec :=
  ![((r % 3 : ℕ) : ZMod 3), (((r / 3) % 3 : ℕ) : ZMod 3), (((r / 9) % 3 : ℕ) : ZMod 3)]

@[expose] def encV (u : Vec) : ℕ := (u 0).val + 3 * (u 1).val + 9 * (u 2).val

@[expose] def dec (c : ℕ) : Mat :=
  Matrix.of ![decV (c % 27), decV ((c / 27) % 27), decV ((c / 729) % 27)]

@[expose] def enc (M : Mat) : ℕ := encV (M 0) + 27 * encV (M 1) + 729 * encV (M 2)

theorem encV_lt (u : Vec) : encV u < 27 := by
  have h0 := ZMod.val_lt (u 0)
  have h1 := ZMod.val_lt (u 1)
  have h2 := ZMod.val_lt (u 2)
  unfold encV
  omega

theorem enc_lt (M : Mat) : enc M < N := by
  have h0 := encV_lt (M 0)
  have h1 := encV_lt (M 1)
  have h2 := encV_lt (M 2)
  unfold enc N
  omega

theorem decV_encV (u : Vec) : decV (encV u) = u := by
  have h0 := ZMod.val_lt (u 0)
  have h1 := ZMod.val_lt (u 1)
  have h2 := ZMod.val_lt (u 2)
  have e0 : (encV u) % 3 = (u 0).val := by unfold encV; omega
  have e1 : (encV u) / 3 % 3 = (u 1).val := by unfold encV; omega
  have e2 : (encV u) / 9 % 3 = (u 2).val := by unfold encV; omega
  funext j
  fin_cases j <;> simp [decV, e0, e1, e2]

theorem encV_decV {r : ℕ} (hr : r < 27) : encV (decV r) = r := by
  unfold encV decV
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ZMod.val_natCast]
  omega

theorem decV_inj {r r' : ℕ} (hr : r < 27) (hr' : r' < 27) (h : decV r = decV r') : r = r' := by
  rw [← encV_decV hr, ← encV_decV hr', h]

theorem dec_enc (M : Mat) : dec (enc M) = M := by
  have h0 := encV_lt (M 0)
  have h1 := encV_lt (M 1)
  have h2 := encV_lt (M 2)
  have e0 : enc M % 27 = encV (M 0) := by unfold enc; omega
  have e1 : enc M / 27 % 27 = encV (M 1) := by unfold enc; omega
  have e2 : enc M / 729 % 27 = encV (M 2) := by unfold enc; omega
  ext i j
  fin_cases i
  · rw [show dec (enc M) ⟨0, by decide⟩ = decV (enc M % 27) from rfl, e0, decV_encV]; rfl
  · rw [show dec (enc M) ⟨1, by decide⟩ = decV (enc M / 27 % 27) from rfl, e1, decV_encV]; rfl
  · rw [show dec (enc M) ⟨2, by decide⟩ = decV (enc M / 729 % 27) from rfl, e2, decV_encV]; rfl

theorem dec_row0 (c : ℕ) : dec c 0 = decV (c % 27) := rfl

theorem dec_row1 (c : ℕ) : dec c 1 = decV ((c / 27) % 27) := rfl

theorem dec_row2 (c : ℕ) : dec c 2 = decV ((c / 729) % 27) := rfl

theorem enc_dec {c : ℕ} (hc : c < N) : enc (dec c) = c := by
  unfold N at hc
  have e0 : encV (decV (c % 27)) = c % 27 := encV_decV (by omega)
  have e1 : encV (decV (c / 27 % 27)) = c / 27 % 27 := encV_decV (by omega)
  have e2 : encV (decV (c / 729 % 27)) = c / 729 % 27 := encV_decV (by omega)
  unfold enc
  rw [dec_row0, dec_row1, dec_row2, e0, e1, e2]
  omega

theorem dec_inj {c c' : ℕ} (hc : c < N) (hc' : c' < N) (h : dec c = dec c') : c = c' := by
  rw [← enc_dec hc, ← enc_dec hc', h]

theorem vmDig_lt (v b k : ℕ) : vmDig v b k < 3 := by
  unfold vmDig; omega

theorem vmRaw_lt (v b : ℕ) : vmRaw v b < 27 := by
  have h1 := vmDig_lt v b 1
  have h3 := vmDig_lt v b 3
  have h9 := vmDig_lt v b 9
  unfold vmRaw; omega

theorem decV_digits {d₀ d₁ d₂ : ℕ} (h₀ : d₀ < 3) (h₁ : d₁ < 3) (h₂ : d₂ < 3) :
    decV (d₀ + 3 * d₁ + 9 * d₂) = ![(d₀ : ZMod 3), (d₁ : ZMod 3), (d₂ : ZMod 3)] := by
  have e0 : (d₀ + 3 * d₁ + 9 * d₂) % 3 = d₀ := by omega
  have e1 : (d₀ + 3 * d₁ + 9 * d₂) / 3 % 3 = d₁ := by omega
  have e2 : (d₀ + 3 * d₁ + 9 * d₂) / 9 % 3 = d₂ := by omega
  unfold decV
  rw [e0, e1, e2]

theorem decV_vmRaw (r c : ℕ) : decV (vmRaw r c) = Matrix.vecMul (decV r) (dec c) := by
  unfold vmRaw
  rw [decV_digits (vmDig_lt r c 1) (vmDig_lt r c 3) (vmDig_lt r c 9)]
  funext j
  fin_cases j <;>
  simp [vmDig, Matrix.vecMul, dotProduct, Fin.sum_univ_three, decV, dec, ZMod.natCast_mod,
    Nat.cast_add, Nat.cast_mul]

theorem ofFn_get! {n : ℕ} (f : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  have hs : i < (Array.ofFn f).size := by rw [Array.size_ofFn]; exact hi
  rw [getElem!_pos (Array.ofFn f) i hs]
  exact Array.getElem_ofFn ..

theorem act_eq {r c : ℕ} (hr : r < 27) (hc : c < N) : act (vmTab ()) c r = vmRaw r c := by
  have hk : r * 19683 + c < 27 * 19683 := by unfold N at hc; omega
  unfold act vmTab
  rw [ofFn_get! _ _ hk]
  show vmRaw ((r * 19683 + c) / 19683) ((r * 19683 + c) % 19683) = _
  have h1 : (r * 19683 + c) / 19683 = r := by unfold N at hc; omega
  have h2 : (r * 19683 + c) % 19683 = c := by unfold N at hc; omega
  rw [h1, h2]

theorem act_lt {r c : ℕ} (hr : r < 27) (hc : c < N) : act (vmTab ()) c r < 27 := by
  rw [act_eq hr hc]; exact vmRaw_lt r c

theorem decV_act {r c : ℕ} (hr : r < 27) (hc : c < N) :
    decV (act (vmTab ()) c r) = Matrix.vecMul (decV r) (dec c) := by
  rw [act_eq hr hc, decV_vmRaw]

theorem mulc_lt {a b : ℕ} (hb : b < N) : mulc (vmTab ()) a b < N := by
  have h0 := act_lt (r := a % 27) (by omega) hb
  have h1 := act_lt (r := a / 27 % 27) (by omega) hb
  have h2 := act_lt (r := a / 729 % 27) (by omega) hb
  unfold mulc N
  omega

theorem dec_mulc {a b : ℕ} (hb : b < N) : dec (mulc (vmTab ()) a b) = dec a * dec b := by
  have h0 := act_lt (r := a % 27) (by omega) hb
  have h1 := act_lt (r := a / 27 % 27) (by omega) hb
  have h2 := act_lt (r := a / 729 % 27) (by omega) hb
  ext i j
  have key : ∀ x : ℕ, ∀ y : ℕ, ∀ z : ℕ, x < 27 → y < 27 → z < 27 →
      dec (x + 27 * y + 729 * z) 0 = decV x ∧ dec (x + 27 * y + 729 * z) 1 = decV y ∧
        dec (x + 27 * y + 729 * z) 2 = decV z := by
    intro x y z hx hy hz
    refine ⟨?_, ?_, ?_⟩
    · rw [dec_row0]; congr 1; omega
    · rw [dec_row1]; congr 1; omega
    · rw [dec_row2]; congr 1; omega
  obtain ⟨k0, k1, k2⟩ := key _ _ _ h0 h1 h2
  have hrow : ∀ i : Fin 3, (dec a * dec b) i =
      Matrix.vecMul (dec a i) (dec b) := by
    intro i; ext j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  unfold mulc
  match i with
  | 0 =>
    show dec _ 0 j = _
    rw [k0, decV_act (by omega) hb, hrow 0, dec_row0]
  | 1 =>
    show dec _ 1 j = _
    rw [k1, decV_act (by omega) hb, hrow 1, dec_row1]
  | 2 =>
    show dec _ 2 j = _
    rw [k2, decV_act (by omega) hb, hrow 2, dec_row2]

theorem det3 (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℕ) :
    (Matrix.of ![![(a0 : ZMod 3), a1, a2], ![b0, b1, b2], ![c0, c1, c2]] : Mat).det =
      ((a0 * b1 * c2 + a1 * b2 * c0 + a2 * b0 * c1 +
        2 * (a0 * b2 * c1 + a1 * b0 * c2 + a2 * b1 * c0) : ℕ) : ZMod 3) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  push_cast
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2]
  simp only [sub_eq_add_neg]
  ring1

theorem det_dec (c : ℕ) : (dec c).det =
    ((((c % 27) % 3) * ((((c / 27) % 27) / 3) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 3) % 3) * ((((c / 27) % 27) / 9) % 3) * (((c / 729) % 27) % 3) +
      (((c % 27) / 9) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 3) % 3) +
    2 * ((((c % 27) % 3) * ((((c / 27) % 27) / 9) % 3) * ((((c / 729) % 27) / 3) % 3) +
      (((c % 27) / 3) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 9) % 3) * ((((c / 27) % 27) / 3) % 3) * (((c / 729) % 27) % 3))) : ℕ) :
      ZMod 3) := by
  rw [← det3]
  rfl

theorem rawInv_of_det {c : ℕ} (h : (dec c).det ≠ 0) : rawInv c = true := by
  unfold rawInv
  rw [bne_iff_ne]
  intro h0
  apply h
  rw [det_dec]
  generalize hn : (((c % 27) % 3) * ((((c / 27) % 27) / 3) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 3) % 3) * ((((c / 27) % 27) / 9) % 3) * (((c / 729) % 27) % 3) +
      (((c % 27) / 9) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 3) % 3) +
    2 * ((((c % 27) % 3) * ((((c / 27) % 27) / 9) % 3) * ((((c / 729) % 27) / 3) % 3) +
      (((c % 27) / 3) % 3) * (((c / 27) % 27) % 3) * ((((c / 729) % 27) / 9) % 3) +
      (((c % 27) / 9) % 3) * ((((c / 27) % 27) / 3) % 3) * (((c / 729) % 27) % 3)))) = n
  have hn3 : n % 3 = 0 := by rw [← hn]; exact h0
  rw [ZMod.natCast_eq_zero_iff]
  omega

end CFSG.RankThree.PartTwo.Sec21.FF79.GL33

end

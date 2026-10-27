module

public import Certificates.Data.CFSGNative.He.Fp
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.He.Native

open Matrix

@[expose] def toVec (p d : ℕ) (v : Array ℕ) : Fin d → ZMod p := fun j => (v[j.val]! : ZMod p)

@[expose] def toMat (p d : ℕ) (X : Array (Array ℕ)) : Matrix (Fin d) (Fin d) (ZMod p) :=
  Matrix.of fun i j => ((X[i.val]!)[j.val]! : ZMod p)

theorem toVec_apply (p d : ℕ) (v : Array ℕ) (j : Fin d) : toVec p d v j = (v[j.val]! : ZMod p) :=
  rfl

theorem toMat_apply (p d : ℕ) (X : Array (Array ℕ)) (i j : Fin d) :
    toMat p d X i j = ((X[i.val]!)[j.val]! : ZMod p) := rfl

theorem fold_add_eq_sum (f : ℕ → ℕ) : ∀ n : ℕ,
    Nat.fold n (fun j _ acc => acc + f j) 0 = ∑ j ∈ Finset.range n, f j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.fold_succ, ih, Finset.sum_range_succ]

theorem dot_cast (p d : ℕ) (r v : Array ℕ) :
    (dot p d r v : ZMod p) = ∑ j : Fin d, (r[j.val]! : ZMod p) * (v[j.val]! : ZMod p) := by
  unfold dot
  rw [ZMod.natCast_mod, fold_add_eq_sum (fun j => r[j]! * v[j]!) d, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun j => ((r[j]! * v[j]! : ℕ) : ZMod p)) d]
  simp only [Nat.cast_mul]

theorem getElem!_ofFn {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem toVec_mulVec (p d : ℕ) (M : Array (Array ℕ)) (v : Array ℕ) :
    toVec p d (mulVec p d M v) = toMat p d M *ᵥ toVec p d v := by
  funext i
  rw [toVec_apply, Matrix.mulVec, dotProduct]
  unfold mulVec
  rw [getElem!_ofFn _ i.isLt, dot_cast]
  rfl

theorem mulVec_size (p d : ℕ) (M : Array (Array ℕ)) (v : Array ℕ) :
    (mulVec p d M v).size = d := by
  unfold mulVec; simp

theorem toMat_mulM (p d : ℕ) (X Y : Array (Array ℕ)) :
    toMat p d (mulM p d X Y) = toMat p d X * toMat p d Y := by
  ext i k
  rw [toMat_apply, Matrix.mul_apply]
  unfold mulM
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ k.isLt, dot_cast]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold col
  rw [getElem!_ofFn _ j.isLt]
  rfl

theorem toMat_idM (p d : ℕ) : toMat p d (idM d) = 1 := by
  ext i j
  rw [toMat_apply, Matrix.one_apply]
  unfold idM
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem toMat_powM (p d : ℕ) (M : Array (Array ℕ)) (e : ℕ) :
    toMat p d (powM p d M e) = toMat p d M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact toMat_idM p d
  | succ e ih => rw [powM, toMat_mulM, ih, pow_succ]

theorem toMat_eq_of_beq {p d : ℕ} {X Y : Array (Array ℕ)} (h : (X == Y) = true) :
    toMat p d X = toMat p d Y := by
  rw [beq_iff_eq] at h
  rw [h]

theorem toVec_eq_of_beq {p d : ℕ} {v w : Array ℕ} (h : (v == w) = true) :
    toVec p d v = toVec p d w := by
  rw [beq_iff_eq] at h
  rw [h]

theorem toMat_colsMat (p d : ℕ) (vs : Array (Array ℕ)) (i t : Fin d) :
    toMat p d (colsMat d vs) i t = toVec p d vs[t.val]! i := by
  rw [toMat_apply, toVec_apply]
  unfold colsMat
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ t.isLt]

theorem canonV_spec {p d : ℕ} {v : Array ℕ} (h : canonV p d v = true) :
    v.size = d ∧ ∀ j < v.size, v[j]! < p := by
  unfold canonV at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  rw [getElem!_pos v j hj]
  exact h.2 j hj

theorem eq_of_toVec_eq {p d : ℕ} {v w : Array ℕ} (hv : canonV p d v = true)
    (hw : canonV p d w = true) (h : toVec p d v = toVec p d w) : v = w := by
  obtain ⟨hvs, hv'⟩ := canonV_spec hv
  obtain ⟨hws, hw'⟩ := canonV_spec hw
  apply Array.ext (by rw [hvs, hws])
  intro j hj hj'
  have hjd : j < d := by rw [← hvs]; exact hj
  have e := congrFun h ⟨j, hjd⟩
  rw [toVec_apply, toVec_apply, ZMod.natCast_eq_natCast_iff'] at e
  rw [Nat.mod_eq_of_lt (hv' j hj), Nat.mod_eq_of_lt (hw' j hj')] at e
  rwa [getElem!_pos v j hj, getElem!_pos w j hj'] at e

theorem wsChar_eq_asciiWhitespace :
    wsChar = CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  funext c; unfold wsChar; rfl

theorem decode_apply_eq_decodeEntries (p d : ℕ) (s : String) (i j : Fin d) :
    CFSG.Blueprint.NativeSporadic.decode p d 1 s i j =
      (((decodeEntries s)[i.val * d + j.val]?.getD 0 : ℕ) : ZMod p) := by
  unfold decodeEntries
  rw [wsChar_eq_asciiWhitespace]
  rfl

theorem toMat_rowsOf (p d : ℕ) (s : String) :
    toMat p d (rowsOf p d s) = CFSG.Blueprint.NativeSporadic.decode p d 1 s := by
  ext i j
  rw [decode_apply_eq_decodeEntries, toMat_apply]
  unfold rowsOf
  rw [getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt, ZMod.natCast_mod, List.getElem?_toArray]

end CFSG.Sporadic.He.Native

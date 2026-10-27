module

public import CFSG.Monster.B.Dyadic.Reduce
public import Certificates.Certificate3103
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native

@[expose] def Bmat : Matrix (Fin 4371) (Fin 4371) ℤ := fun i j => Bz i j

abbrev denD : ℕ := 128

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

@[expose] noncomputable def ell (R : Module.Basis (Fin 4371) ℚ V) (i : Fin 4371) : V :=
  (1 / (denD : ℚ)) • ∑ j, (Bmat i j : ℚ) • R j

@[expose] def Lam (R : Module.Basis (Fin 4371) ℚ V) : Submodule ℤ V :=
  Submodule.span ℤ (Set.range (ell R))

theorem Bmat_apply (i j : Fin 4371) : Bmat i j = Bz i j := rfl

theorem beq_one_testBit (a k : ℕ) : ((a >>> k) % 2 == 1) = a.testBit k := by
  rw [Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (a >>> k) with h | h <;> simp [h]

theorem rowBit_bytesOfNat (x : ℕ) {j : ℕ} (hj : j < 4416) :
    rowBit (bytesOfNat x) j = x.testBit j := by
  unfold rowBit bytesOfNat
  rw [getBytes_ofFn _ (by omega)]
  simp only
  rw [UInt8.toNat_ofNat', beq_one_testBit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.div_add_mod j 8]
  simp [Nat.mod_lt j (by norm_num : 8 > 0)]

theorem rowBit_qRowBytes (fr y : ByteArray) {t : ℕ} (ht : t < 4370) :
    rowBit (qRowBytes fr y) t =
      (rowBit y (srcIdx t) ^^ (rowBit y removedCoord && rowBit fr (srcIdx t))) := by
  unfold qRowBytes
  rw [rowBit_packed _ t (by omega)]
  simp only
  rw [Nat.div_add_mod t 8]
  simp [ht]

theorem srcIdx_eq (j : Fin 4370) : srcIdx j = (pIdx.succAbove j : ℕ) := by
  unfold srcIdx removedCoord
  by_cases h : (j : ℕ) < 1197
  · rw [ite_eq_left h, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; exact h)]
    rfl
  · rw [ite_eq_right h, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp [pIdx]; omega)]
    rfl

theorem xor_ite_zmod2 (a b c : Bool) :
    (if (a ^^ (b && c)) = true then (1 : ZMod 2) else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) * (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

theorem Pmap_apply (y : Fin 4371 → ZMod 2) (j : Fin 4370) :
    Pmap y j = y (pIdx.succAbove j) + y pIdx * fvec (pIdx.succAbove j) := rfl

theorem Qmat_apply (g : Fin 26) (k t : Fin 4370) :
    Qmat g k t = Pmap (fun j => Cmat g (pIdx.succAbove k) j) t := rfl

theorem fixed_facts : fixedVector.testBit 1197 = true ∧
    ∀ i < 1197, (!fixedVector.testBit i) = true := by
  obtain ⟨-, h1, h2⟩ := Certificates.certificate3103
  exact ⟨h1, fun i hi => by rw [h2 i hi]; rfl⟩

theorem fvec_p : fvec pIdx = 1 := by
  unfold fvec
  exact ite_eq_left fixed_facts.1

theorem fvec_of_lt {i : Fin 4371} (hi : (i : ℕ) < 1197) :
    fvec i = 0 := by
  unfold fvec
  have h := fixed_facts.2 i hi
  rw [Bool.not_eq_true'] at h
  rw [h]
  rfl

theorem fvec_ne_zero : fvec ≠ 0 := by
  intro h
  have := congrFun h pIdx
  rw [fvec_p] at this
  exact one_ne_zero this

theorem Pmap_eq_zero_iff (y : Fin 4371 → ZMod 2) :
    Pmap y = 0 ↔ y = 0 ∨ y = fvec := by
  constructor
  · intro h
    have hy : y = y pIdx • fvec := by
      funext i
      rcases Fin.eq_self_or_eq_succAbove pIdx i with hi | ⟨j, rfl⟩
      · subst hi
        simp [fvec_p]
      · have := congrFun h j
        rw [Pmap_apply, Pi.zero_apply] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← ZMod.neg_eq_self_mod_two (y pIdx * _)]
        exact eq_neg_of_add_eq_zero_left this
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (y pIdx) with hp | hp
    · left
      rw [hy, hp, zero_smul]
    · right
      rw [hy, hp, one_smul]
  · rintro (rfl | rfl)
    · exact map_zero Pmap
    · funext j
      rw [Pmap_apply, fvec_p, one_mul, Pi.zero_apply]
      exact (show ∀ c : ZMod 2, c + c = 0 by decide) _

theorem Pmap_single (j : Fin 4370) : Pmap (Pi.single (pIdx.succAbove j) 1) = Pi.single j 1 := by
  funext t
  rw [Pmap_apply, Pi.single_apply, Pi.single_apply, Pi.single_apply,
    ite_eq_right (Fin.succAbove_ne pIdx j).symm, zero_mul, add_zero]
  by_cases h : t = j
  · subst h
    simp
  · rw [ite_eq_right (fun e => h (Fin.succAbove_right_injective e)), ite_eq_right h]

theorem Pmap_surjective : Function.Surjective Pmap := by
  intro z
  refine ⟨Fin.insertNth pIdx 0 z, ?_⟩
  funext j
  rw [Pmap_apply, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same, zero_mul, add_zero]

end CFSG.Monster.B.Dyadic

end

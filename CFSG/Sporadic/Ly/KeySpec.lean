module

public import CFSG.Sporadic.Ly.PackSpec
public import CFSG.Sporadic.He.FpSpec
public import Certificates.Data.CFSGNative.Ly.Orbit

public section

namespace CFSG.Sporadic.Ly

open Native Matrix Finset
open CFSG.Sporadic.He.Native (toMat)

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

@[expose] def ValidKey (key : ByteArray) : Prop :=
  key.size = 276 ∧ ∀ q < 276, (key.get! q).toNat < 125

@[expose] def keyU (key : ByteArray) : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  Matrix.of fun j m => (keyDigit key (111 * m.val + j.val) : ZMod 5)

@[expose] def keyC (key : ByteArray) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  Matrix.of fun a b => (keyDigit key (777 + 7 * a.val + b.val) : ZMod 5)

@[expose] def keyT (key : ByteArray) : Matrix (Fin 111) (Fin 111) (ZMod 5) :=
  keyU key * keyC key * (keyU key)ᵀ

theorem keyDigit_lt (key : ByteArray) (p : ℕ) : keyDigit key p < 5 := Nat.mod_lt _ (by norm_num)

theorem code3_toNat (a b c : ℕ) : (code3 a b c).toNat = a % 5 + 5 * (b % 5) + 25 * (c % 5) := by
  unfold code3
  rw [UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)]

theorem encodeDigits_size (D : ℕ → ℕ) : (encodeDigits D).size = 276 := by
  simp [encodeDigits, ByteArray.size]

theorem encodeDigits_get (D : ℕ → ℕ) {q : ℕ} (hq : q < 276) :
    (encodeDigits D).get! q = code3 (D (3 * q)) (D (3 * q + 1)) (D (3 * q + 2)) := by
  rw [byteArray_get!_eq]
  simp only [encodeDigits]
  rw [getElem!_pos _ q (by simpa using hq), Array.getElem_ofFn]

theorem validKey_encodeDigits (D : ℕ → ℕ) : ValidKey (encodeDigits D) := by
  refine ⟨encodeDigits_size D, fun q hq => ?_⟩
  rw [encodeDigits_get D hq, code3_toNat]
  omega

theorem keyDigit_encodeDigits (D : ℕ → ℕ) {p : ℕ} (hp : p < 828) :
    keyDigit (encodeDigits D) p = D p % 5 := by
  unfold keyDigit
  rw [encodeDigits_get D (by omega), code3_toNat]
  have h3 := Nat.mod_lt p (show 0 < 3 by norm_num)
  have hp3 := Nat.div_add_mod p 3
  interval_cases hm : p % 3
  · simp only [pow_zero, Nat.div_one]
    rw [show 3 * (p / 3) = p by omega]
    omega
  · rw [show 3 * (p / 3) + 1 = p by omega, pow_one]
    omega
  · rw [show 3 * (p / 3) + 2 = p by omega, show (5 : ℕ) ^ 2 = 25 by norm_num]
    omega

theorem keyDigit_byte (key : ByteArray) (q t : ℕ) (ht : t < 3) :
    keyDigit key (3 * q + t) = (key.get! q).toNat / 5 ^ t % 5 := by
  unfold keyDigit
  rw [show (3 * q + t) / 3 = q by omega, show (3 * q + t) % 3 = t by omega]

theorem frTable_get (M : Array (Array ℕ)) {g c : ℕ} (hg : g < 37) (hc : c < 125) :
    (frTable M)[125 * g + c]! = frEntry M g c := by
  have ht : 125 * g + c < 37 * 125 := by omega
  unfold frTable
  rw [getElem!_pos _ (125 * g + c) (by simpa using ht), Array.getElem_ofFn]
  simp only
  rw [show (125 * g + c) / 125 = g by omega, show (125 * g + c) % 125 = c by omega]

theorem frEntry_lane (M : Array (Array ℕ)) (g c : ℕ) {i : ℕ} (hi : i < 112) :
    (frEntry M g c).lane i = frSum M i g c % 5 :=
  W14.lane_packW (fun _ _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) hi

theorem fold_add_lane (f : ℕ → W14) :
    ∀ n ≤ 63, (∀ g < n, ∀ i < 112, (f g).lane i ≤ 4) → ∀ i < 112,
      (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane i =
        ∑ g ∈ range n, (f g).lane i ∧
      (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane i ≤ 4 * n := by
  intro n
  induction n with
  | zero => intro _ _ i _; simp [W14.lane_zero]
  | succ n ih =>
    intro hn hf i hi
    rw [Nat.fold_succ]
    have ih' := ih (by omega) (fun g hg => hf g (by omega))
    have hb : ∀ j < 112, (Nat.fold n (fun g _ acc => acc.add (f g)) W14.zero).lane j +
        (f n).lane j < 256 := by
      intro j hj
      have := (ih' j hj).2
      have := hf n (by omega) j hj
      omega
    rw [W14.lane_add hb hi, (ih' i hi).1, Finset.sum_range_succ]
    refine ⟨rfl, ?_⟩
    have := (ih' i hi).2
    have := hf n (by omega) i hi
    rw [← (ih' i hi).1]
    omega

theorem sum_groups (F : ℕ → ZMod 5) :
    ∀ n, ∑ g ∈ range n, (F (3 * g) + F (3 * g + 1) + F (3 * g + 2)) = ∑ j ∈ range (3 * n), F j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem rowProd_lane (M : Array (Array ℕ)) {key : ByteArray} (hv : ValidKey key) {r : ℕ}
    (hr : r < 7) {i : ℕ} (hi : i < 112) :
    (rowProd (frTable M) key r).lane i =
      ∑ g ∈ range 37, frSum M i g (key.get! (37 * r + g)).toNat % 5 ∧
    (rowProd (frTable M) key r).lane i ≤ 148 := by
  have hkey : ∀ g < 37, (key.get! (37 * r + g)).toNat < 125 := fun g hg => hv.2 _ (by omega)
  have hT : ∀ g < 37, (frTable M)[125 * g + (key.get! (37 * r + g)).toNat]! =
      frEntry M g (key.get! (37 * r + g)).toNat := fun g hg => frTable_get M hg (hkey g hg)
  have h := fold_add_lane (fun g => (frTable M)[125 * g + (key.get! (37 * r + g)).toNat]!) 37
    (by norm_num) (fun g hg j hj => by
      rw [hT g hg, frEntry_lane _ _ _ hj]; omega) i hi
  unfold rowProd
  refine ⟨?_, by simpa using h.2⟩
  rw [h.1]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hT g (Finset.mem_range.1 hg), frEntry_lane _ _ _ hi]

theorem ent_eq (M : Array (Array ℕ)) {i j : ℕ} (hi : i < 111) (hj : j < 111) :
    ent M i j = (M[i]!)[j]! := by
  unfold ent; rw [ite_eq_left ⟨hi, hj⟩]

theorem rowProd_lane_cast (M : Array (Array ℕ)) {key : ByteArray} (hv : ValidKey key)
    (r : Fin 7) (i : Fin 111) :
    ((rowProd (frTable M) key r.val).lane i.val : ZMod 5) = (toMat 5 111 M * keyU key) i r := by
  rw [(rowProd_lane M hv r.isLt (by omega)).1, Matrix.mul_apply, Nat.cast_sum]
  have hkey : ∀ g < 37, (key.get! (37 * r.val + g)).toNat < 125 := fun g hg => hv.2 _ (by omega)
  have hterm : ∀ g ∈ range 37, ((frSum M i.val g (key.get! (37 * r.val + g)).toNat % 5 : ℕ) :
      ZMod 5) = (fun j => (((M[i.val]!)[j]! : ℕ) : ZMod 5) *
        (keyDigit key (111 * r.val + j) : ZMod 5)) (3 * g) +
      (fun j => (((M[i.val]!)[j]! : ℕ) : ZMod 5) *
        (keyDigit key (111 * r.val + j) : ZMod 5)) (3 * g + 1) +
      (fun j => (((M[i.val]!)[j]! : ℕ) : ZMod 5) *
        (keyDigit key (111 * r.val + j) : ZMod 5)) (3 * g + 2) := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    simp only
    rw [ZMod.natCast_mod, frSum, ent_eq M i.isLt (by omega), ent_eq M i.isLt (by omega),
      ent_eq M i.isLt (by omega)]
    have e0 := keyDigit_byte key (37 * r.val + g) 0 (by norm_num)
    have e1 := keyDigit_byte key (37 * r.val + g) 1 (by norm_num)
    have e2 := keyDigit_byte key (37 * r.val + g) 2 (by norm_num)
    rw [show 3 * (37 * r.val + g) + 0 = 111 * r.val + 3 * g by ring] at e0
    rw [show 3 * (37 * r.val + g) + 1 = 111 * r.val + (3 * g + 1) by ring] at e1
    rw [show 3 * (37 * r.val + g) + 2 = 111 * r.val + (3 * g + 2) by ring] at e2
    rw [e0, e1, e2]
    simp only [pow_zero, Nat.div_one, pow_one, show (5 : ℕ) ^ 2 = 25 by norm_num]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, sum_groups (fun j => (((M[i.val]!)[j]! : ℕ) : ZMod 5) *
    (keyDigit key (111 * r.val + j) : ZMod 5)) 37, show 3 * 37 = 111 by norm_num,
    ← Fin.sum_univ_eq_sum_range (fun j => (((M[i.val]!)[j]! : ℕ) : ZMod 5) *
      (keyDigit key (111 * r.val + j) : ZMod 5)) 111]
  rfl

end CFSG.Sporadic.Ly

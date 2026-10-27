module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylowData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.D4TwoPK

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two

@[expose] def laneK (x t : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 3 t)) 7

@[expose] def gmTab : ℕ := 2821848294356612419217921029917578219971947684264937521152

@[expose] def gmK (u v : ℕ) : ℕ := laneK gmTab (Nat.add (Nat.mul 8 u) v)

@[expose] def entK (a b i j : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (gmK (laneK a (Nat.mul 8 i)) (laneK b j))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 1)) (laneK b (Nat.add 8 j))))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 2)) (laneK b (Nat.add 16 j))))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 3)) (laneK b (Nat.add 24 j))))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 4)) (laneK b (Nat.add 32 j))))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 5)) (laneK b (Nat.add 40 j))))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 6)) (laneK b (Nat.add 48 j))))
    (gmK (laneK a (Nat.add (Nat.mul 8 i) 7)) (laneK b (Nat.add 56 j)))

@[expose] def packK (a b n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun t acc => Nat.add acc (Nat.shiftLeft (entK a b (Nat.div t 8) (Nat.mod t 8)) (Nat.mul 3 t))) n

@[expose] def mulK (a b : ℕ) : ℕ := packK a b 64

@[expose, irreducible] def decA (x : ℕ) : Array GF8 :=
  Array.ofFn (n := 64) fun t => GF8.ofNat' (laneK x t.val)

theorem laneK_eq (x t : ℕ) : laneK x t = x / 8 ^ t % 8 := by
  have h7 : (7 : ℕ) = 2 ^ 3 - 1 := rfl
  change (x >>> (3 * t)) &&& 7 = _
  rw [h7, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem laneK_lt (x t : ℕ) : laneK x t < 8 := by
  rw [laneK_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem gmK_lt (u v : ℕ) : gmK u v < 8 := laneK_lt _ _

theorem xor_lt8 {u v : ℕ} (hu : u < 8) (hv : v < 8) : Nat.xor u v < 8 :=
  Nat.xor_lt_two_pow (n := 3) hu hv

theorem entK_lt (a b i j : ℕ) : entK a b i j < 8 := by
  unfold entK
  repeat' first | apply xor_lt8 | apply gmK_lt

theorem packK_succ (a b n : ℕ) :
    packK a b (n + 1) = packK a b n + entK a b (n / 8) (n % 8) * 8 ^ n := by
  change packK a b n + (entK a b (n / 8) (n % 8) <<< (3 * n)) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  rfl

theorem packK_lt (a b n : ℕ) : packK a b n < 8 ^ n := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [packK_succ, pow_succ]
    have he := entK_lt a b (n / 8) (n % 8)
    nlinarith [Nat.one_le_pow n 8 (by norm_num)]

theorem packK_lane (a b n t : ℕ) (ht : t < n) :
    packK a b n / 8 ^ t % 8 = entK a b (t / 8) (t % 8) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [packK_succ]
    have hP := packK_lt a b n
    have he := entK_lt a b (n / 8) (n % 8)
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
    · obtain ⟨d, rfl⟩ : ∃ d, n = t + (d + 1) := ⟨n - t - 1, by omega⟩
      have key : entK a b ((t + (d + 1)) / 8) ((t + (d + 1)) % 8) * 8 ^ (t + (d + 1)) =
          entK a b ((t + (d + 1)) / 8) ((t + (d + 1)) % 8) * 8 ^ d * 8 * 8 ^ t := by ring
      rw [key, Nat.add_mul_div_right _ _ (pow_pos (by norm_num) _), Nat.add_mul_mod_self_right]
      exact ih (by omega)
    · subst h
      rw [Nat.add_mul_div_right _ _ (pow_pos (by norm_num) _), Nat.div_eq_of_lt hP, zero_add,
        Nat.mod_eq_of_lt he]

theorem laneK_mulK (a b t : ℕ) (ht : t < 64) : laneK (mulK a b) t = entK a b (t / 8) (t % 8) := by
  rw [laneK_eq]
  exact packK_lane a b 64 t ht

theorem mulK_lt (a b : ℕ) : mulK a b < 8 ^ 64 := packK_lt a b 64

theorem getD_decA (x t : ℕ) (h : t < 64) : (decA x).getD t 0 = GF8.ofNat' (laneK x t) := by
  unfold decA
  exact getD_ofFn _ t h

theorem add_ofNat' {u v : ℕ} (hu : u < 8) (hv : v < 8) :
    GF8.ofNat' u + GF8.ofNat' v = GF8.ofNat' (Nat.xor u v) := by
  change GF8.ofNat' ((u % 8) ^^^ (v % 8)) = _
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]
  rfl

theorem mulNat_eq_gmK : ∀ u < 8, ∀ v < 8, GF8.mulNat u v % 8 = gmK u v := by
  decide +kernel

theorem mul_ofNat' {u v : ℕ} (hu : u < 8) (hv : v < 8) :
    GF8.ofNat' u * GF8.ofNat' v = GF8.ofNat' (gmK u v) := by
  change GF8.ofNat' (GF8.mulNat (u % 8) (v % 8)) = _
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv, ← mulNat_eq_gmK u hu v hv]
  unfold GF8.ofNat'
  simp only [Nat.mod_mod]

theorem mulArr_decA (a b : ℕ) : mulArr (decA a) (decA b) = decA (mulK a b) := by
  unfold mulArr
  conv_rhs => unfold decA
  congr 1
  funext ⟨t, ht⟩
  simp (disch := omega) only [getD_decA]
  simp (disch := solve_by_elim [laneK_lt]) only [mul_ofNat']
  simp (disch := solve_by_elim (maxDepth := 40) [xor_lt8, gmK_lt]) only [add_ofNat']
  rw [laneK_mulK a b t ht]
  rfl

theorem decA_inj {p q : ℕ} (hp : p < 8 ^ 64) (hq : q < 8 ^ 64) (h : decA p = decA q) : p = q := by
  have hl : ∀ t < 64, p / 8 ^ t % 8 = q / 8 ^ t % 8 := by
    intro t ht
    have h1 := congrArg (fun A => ((A.getD t 0 : GF8).val : ℕ)) h
    simp only [getD_decA _ _ ht] at h1
    have e1 : (GF8.ofNat' (laneK p t)).val.val = laneK p t := Nat.mod_eq_of_lt (laneK_lt p t)
    have e2 : (GF8.ofNat' (laneK q t)).val.val = laneK q t := Nat.mod_eq_of_lt (laneK_lt q t)
    rw [← laneK_eq, ← laneK_eq, ← e1, ← e2]
    exact h1
  suffices key : ∀ n p q, p < 8 ^ n → q < 8 ^ n → (∀ t < n, p / 8 ^ t % 8 = q / 8 ^ t % 8) →
      p = q from key 64 p q hp hq hl
  intro n
  induction n with
  | zero => intro p q hp hq _; simp at hp hq; omega
  | succ n ih =>
    intro p q hp hq hl
    have h0 := hl 0 (by omega)
    have hd : p / 8 = q / 8 := by
      refine ih _ _ ?_ ?_ ?_
      · rw [pow_succ] at hp; omega
      · rw [pow_succ] at hq; omega
      · intro t ht
        have := hl (t + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    simp at h0
    omega

theorem commutes_decA (a b : ℕ) :
    commutes (decA a) (decA b) = Nat.beq (mulK a b) (mulK b a) := by
  unfold commutes
  rw [mulArr_decA, mulArr_decA]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  refine ⟨decA_inj (mulK_lt a b) (mulK_lt b a), fun h => ?_⟩
  rw [h]

theorem mulArr_of (A B C : Array GF8) (a b c : ℕ) (hA : A = decA a) (hB : B = decA b)
    (hC : C = decA c) (h : Nat.beq (mulK a b) c = true) : mulArr A B = C := by
  subst hA hB hC
  rw [mulArr_decA, Nat.eq_of_beq_eq_true h]

theorem center_of (X A B : Array GF8) (x a b : ℕ) (hX : X = decA x) (hA : A = decA a)
    (hB : B = decA b) (r : Bool)
    (h : (Nat.beq (mulK x a) (mulK a x) && Nat.beq (mulK x b) (mulK b x)) = r) :
    (commutes X A && commutes X B) = r := by
  subst hX hA hB
  rw [commutes_decA, commutes_decA]
  exact h

end CFSG.LocalAnalysis.UniquenessCase.UC22.D4TwoPK

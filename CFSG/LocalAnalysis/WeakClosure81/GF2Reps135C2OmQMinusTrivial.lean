module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private lemma c2slomqmtv_coprime {f : ℕ} (hf : 1 ≤ f) : (2 ^ f - 1).Coprime (2 ^ f + 1) := by
  have heven : Even (2 ^ f : ℕ) := (even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega)
  have hodd : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one
  have hsplit : 2 ^ f + 1 = (2 ^ f - 1) + 2 := by
    have := Nat.one_le_two_pow (n := f)
    omega
  rw [hsplit, Nat.coprime_self_add_right]
  exact hodd.coprime_two_right

private lemma c2slomqmtv_prod_eq_neg_one {l : ℕ} {s : Fin l → ℤ} (hs : SpIsSign s)
    (hodd : Odd (Finset.univ.filter fun a => s a = -1).card) : ∏ a, s a = -1 := by
  have h1 : ∏ a, s a = ∏ a, (if s a = -1 then (-1 : ℤ) else 1) := by
    apply Finset.prod_congr rfl
    intro a _
    rcases hs a with h | h <;> simp [h]
  rw [h1, ← Finset.prod_filter, Finset.prod_const]
  exact hodd.neg_one_pow

private lemma c2slomqmtv_one_symm_apply {l : ℕ} (b : Fin l) :
    ((1 : Equiv.Perm (Fin l)).symm) b = b := rfl

private lemma c2slomqmtv_triv_fst {l m h j : ℕ} (hl : 1 ≤ l) :
    (omqMinusTriv l m h j hl).1 ⟨0, by omega⟩ = -(j : ZMod m) := by
  rw [omqMinusTriv]
  simp

private lemma c2slomqmtv_cast_ne_zero {m j : ℕ} (hm : 2 ≤ m) (hj : ¬ m ∣ j) :
    -(j : ZMod m) ≠ 0 := by
  intro h
  apply hj
  have h' : (j : ZMod m) = 0 := by
    have := congrArg Neg.neg h
    simpa using this
  exact (ZMod.natCast_eq_zero_iff j m).mp h'

private lemma c2slomqmtv_act_a_fst_zero {l m h j : ℕ} (hl : 2 ≤ l) {π : Equiv.Perm (Fin l)}
    {s : Fin l → ℤ} (hπ1 : π ⟨1, by omega⟩ = ⟨0, by omega⟩) :
    (omqMinusAct π s (omqMinusTriv l m h j (by omega))).1 ⟨0, by omega⟩ = 0 := by
  have hsymm : π.symm ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
    rw [Equiv.symm_apply_eq]
    exact hπ1.symm
  have hne : (⟨1, by omega⟩ : Fin l) ≠ ⟨0, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp only [omqMinusAct, omqMinusTriv, Prod.fst, omqSignedAct, Equiv.refl_symm,
    Equiv.refl_apply, Pi.single_apply]
  rw [hsymm, if_neg hne, mul_zero]

private lemma c2slomqmtv_triv_inj {l m h j j' : ℕ} (hl : 1 ≤ l) (hc : m.Coprime h)
    (hj : j < m * h) (hj' : j' < m * h)
    (heq : omqMinusTriv l m h j hl = omqMinusTriv l m h j' hl) : j = j' := by
  have h1 : ((j : ℕ) : ZMod m) = ((j' : ℕ) : ZMod m) := by
    have h := congrArg (fun u : OmqMinusLat l m h => u.1 ⟨0, by omega⟩) heq
    simp only [omqMinusTriv, Pi.single_apply] at h
    exact neg_inj.mp h
  have h2 : ((j : ℕ) : ZMod h) = ((j' : ℕ) : ZMod h) := by
    have h := congrArg (fun u : OmqMinusLat l m h => u.2) heq
    simp only [omqMinusTriv] at h
    exact neg_inj.mp h
  rcases le_total j j' with hle | hle
  · have hm : m ∣ j' - j := by
      have hz : ((j' - j : ℕ) : ZMod m) = 0 := by
        rw [Nat.cast_sub hle, h1, sub_self]
      exact (ZMod.natCast_eq_zero_iff (j' - j) m).mp hz
    have hh : h ∣ j' - j := by
      have hz : ((j' - j : ℕ) : ZMod h) = 0 := by
        rw [Nat.cast_sub hle, h2, sub_self]
      exact (ZMod.natCast_eq_zero_iff (j' - j) h).mp hz
    have hdvd : m * h ∣ j' - j := hc.mul_dvd_of_dvd_of_dvd hm hh
    have hzero : j' - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hm : m ∣ j - j' := by
      have hz : ((j - j' : ℕ) : ZMod m) = 0 := by
        rw [Nat.cast_sub hle, h1, sub_self]
      exact (ZMod.natCast_eq_zero_iff (j - j') m).mp hz
    have hh : h ∣ j - j' := by
      have hz : ((j - j' : ℕ) : ZMod h) = 0 := by
        rw [Nat.cast_sub hle, h2, sub_self]
      exact (ZMod.natCast_eq_zero_iff (j - j') h).mp hz
    have hdvd : m * h ∣ j - j' := hc.mul_dvd_of_dvd_of_dvd hm hh
    have hzero : j - j' = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

private lemma c2slomqmtv_act_c {l m h j : ℕ} (hl : 1 ≤ l) (hj : j ≤ m * h) {s : Fin l → ℤ}
    (hs0 : s ⟨0, by omega⟩ = -1) (hprod : ∏ a, s a = -1) :
    omqMinusAct (1 : Equiv.Perm (Fin l)) s (omqMinusTriv l m h j hl) =
      omqMinusTriv l m h (m * h - j) hl := by
  have hcast_m : ((m * h - j : ℕ) : ZMod m) = -((j : ℕ) : ZMod m) := by
    rw [Nat.cast_sub hj, Nat.cast_mul, ZMod.natCast_self]
    ring
  have hcast_h : ((m * h - j : ℕ) : ZMod h) = -((j : ℕ) : ZMod h) := by
    rw [Nat.cast_sub hj, Nat.cast_mul, ZMod.natCast_self]
    ring
  apply Prod.ext
  · funext b
    simp only [omqMinusAct, omqMinusTriv, Prod.fst, omqSignedAct, Pi.single_apply]
    rw [c2slomqmtv_one_symm_apply b]
    by_cases hb : b = ⟨0, by omega⟩
    · rw [if_pos hb, if_pos hb, hb, hs0, hcast_m]
      ring
    · rw [if_neg hb, if_neg hb, mul_zero]
  · simp only [omqMinusAct, omqMinusTriv, Prod.snd, hprod, hcast_h]
    ring

private def c2slomqmtv_J (m : ℕ) (i : Fin 7) : ℕ :=
  (i.val / (m - 1)) * m + i.val % (m - 1) + 1

private lemma c2slomqmtv_J_pos (m : ℕ) (i : Fin 7) : 1 ≤ c2slomqmtv_J m i := by
  unfold c2slomqmtv_J
  omega

private lemma c2slomqmtv_J_lt {m h : ℕ} (hm : 3 ≤ m) (hh : 5 ≤ h) (i : Fin 7) :
    c2slomqmtv_J m i < m * h := by
  have hr : i.val % (m - 1) + 1 ≤ m - 1 := by
    have := Nat.mod_lt i.val (by omega : 0 < m - 1)
    omega
  have hq : i.val / (m - 1) ≤ 3 :=
    Nat.div_le_of_le_mul (by omega : i.val ≤ (m - 1) * 3)
  have h1 : (i.val / (m - 1)) * m ≤ 3 * m := Nat.mul_le_mul_right m hq
  calc c2slomqmtv_J m i
      = (i.val / (m - 1)) * m + (i.val % (m - 1) + 1) := by
        unfold c2slomqmtv_J; ring
    _ ≤ 3 * m + (m - 1) := Nat.add_le_add h1 hr
    _ ≤ 4 * m := by omega
    _ < m * h := by
        rw [show 4 * m = m * 4 by ring]
        exact Nat.mul_lt_mul_of_pos_left (by omega : 4 < h) (by omega : 0 < m)

private lemma c2slomqmtv_J_mod {m : ℕ} (hm : 2 ≤ m) (i : Fin 7) :
    c2slomqmtv_J m i % m = i.val % (m - 1) + 1 := by
  have hr : i.val % (m - 1) + 1 < m := by
    have := Nat.mod_lt i.val (by omega : 0 < m - 1)
    omega
  unfold c2slomqmtv_J
  rw [Nat.mul_comm (i.val / (m - 1)) m, Nat.add_assoc, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt hr]

private lemma c2slomqmtv_J_div {m : ℕ} (hm : 2 ≤ m) (i : Fin 7) :
    c2slomqmtv_J m i / m = i.val / (m - 1) := by
  have hr : i.val % (m - 1) + 1 < m := by
    have := Nat.mod_lt i.val (by omega : 0 < m - 1)
    omega
  unfold c2slomqmtv_J
  rw [Nat.mul_comm (i.val / (m - 1)) m, Nat.add_assoc, Nat.mul_add_div (by omega : 0 < m),
    Nat.div_eq_of_lt hr, Nat.add_zero]

private lemma c2slomqmtv_J_not_dvd {m : ℕ} (hm : 2 ≤ m) (i : Fin 7) :
    ¬ m ∣ c2slomqmtv_J m i := by
  intro hdvd
  have h0 : c2slomqmtv_J m i % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [c2slomqmtv_J_mod hm] at h0
  omega

private lemma c2slomqmtv_J_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (c2slomqmtv_J m) := by
  intro i i' h
  have hdiv : i.val / (m - 1) = i'.val / (m - 1) := by
    have := congrArg (fun n => n / m) h
    rwa [c2slomqmtv_J_div hm, c2slomqmtv_J_div hm] at this
  have hmod : i.val % (m - 1) = i'.val % (m - 1) := by
    have := congrArg (fun n => n % m) h
    rw [c2slomqmtv_J_mod hm, c2slomqmtv_J_mod hm] at this
    omega
  apply Fin.ext
  have h1 := Nat.div_add_mod' i.val (m - 1)
  have h2 := Nat.div_add_mod' i'.val (m - 1)
  rw [hdiv, hmod] at h1
  omega

theorem omq_minus_exists_trivial_weights {f : ℕ} (hf : 2 ≤ f) {l : ℕ} (hl : 3 ≤ l) {m h : ℕ}
    (hm : m = 2 ^ f - 1) (hh : h = 2 ^ f + 1) {π : Equiv.Perm (Fin l)} {s : Fin l → ℤ}
    (hs : SpIsSign s) (hsh : OmqMinusShape (by omega : 2 ≤ l) π s) :
    ∃ J : Fin 7 → ℕ, (∀ i, 1 ≤ J i ∧ J i < m * h) ∧
      Function.Injective (fun i => omqMinusTriv l m h (J i) (by omega)) ∧
      ∀ i i', omqMinusTriv l m h (J i) (by omega) ≠
        omqMinusAct π s (omqMinusTriv l m h (J i') (by omega)) := by
  have hpow4 : 4 ≤ 2 ^ f := by
    have := Nat.pow_le_pow_of_le (by norm_num : 1 < 2) hf
    norm_num at this
    exact this
  have hm3 : 3 ≤ m := by rw [hm]; omega
  have hh5 : 5 ≤ h := by rw [hh]; omega
  have hmh15 : 15 ≤ m * h := by nlinarith
  have hc : m.Coprime h := by
    rw [hm, hh]
    exact c2slomqmtv_coprime (by omega : 1 ≤ f)
  rcases hsh with hA | hC
  · obtain ⟨_, _, _, hπ1⟩ := hA
    refine ⟨c2slomqmtv_J m, ?_, ?_, ?_⟩
    · intro i
      exact ⟨c2slomqmtv_J_pos m i, c2slomqmtv_J_lt hm3 hh5 i⟩
    · intro i i' heq
      exact c2slomqmtv_J_injective (by omega : 2 ≤ m)
        (c2slomqmtv_triv_inj (by omega : 1 ≤ l) hc (c2slomqmtv_J_lt hm3 hh5 i)
          (c2slomqmtv_J_lt hm3 hh5 i') heq)
    · intro i i' heq
      have h0 := congrArg (fun u : OmqMinusLat l m h => u.1 ⟨0, by omega⟩) heq
      rw [c2slomqmtv_triv_fst,
        c2slomqmtv_act_a_fst_zero (by omega : 2 ≤ l) hπ1] at h0
      exact c2slomqmtv_cast_ne_zero (by omega : 2 ≤ m)
        (c2slomqmtv_J_not_dvd (by omega : 2 ≤ m) i) h0
  · obtain ⟨hπeq, hs0, hodd⟩ := hC
    have hprod : ∏ a, s a = -1 := c2slomqmtv_prod_eq_neg_one hs hodd
    refine ⟨fun i => i.val + 1, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      constructor <;> omega
    · intro i i' heq
      dsimp only at heq ⊢
      have hJ := c2slomqmtv_triv_inj (by omega : 1 ≤ l) hc (by omega : i.val + 1 < m * h)
        (by omega : i'.val + 1 < m * h) heq
      exact Fin.ext (by omega)
    · intro i i' heq
      dsimp only at heq ⊢
      have hJlt : i.val + 1 < m * h := by omega
      have hsum : m * h - (i'.val + 1) < m * h := by omega
      have hne : i.val + 1 ≠ m * h - (i'.val + 1) := by omega
      rw [hπeq] at heq
      rw [c2slomqmtv_act_c (by omega : 1 ≤ l) (by omega : i'.val + 1 ≤ m * h) hs0 hprod] at heq
      exact hne (c2slomqmtv_triv_inj (by omega : 1 ≤ l) hc hJlt hsum heq)

end CFSG.LocalAnalysis.WeakClosure81

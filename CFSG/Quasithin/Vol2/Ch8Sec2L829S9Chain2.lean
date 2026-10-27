module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix

@[expose] def S9cInv {E : Type} [Field E] {d : ℕ} (N : Subgroup (GL (Fin d) E))
    (Y : Submodule E (Fin d → E)) : Prop :=
  ∀ g ∈ N, ∀ v ∈ Y, (g : Matrix (Fin d) (Fin d) E) *ᵥ v ∈ Y

theorem s9c_chain_exists {E : Type} [Field E] {d : ℕ} (N : Subgroup (GL (Fin d) E))
    (Z : Submodule E (Fin d → E)) (hZ : S9cInv N Z) :
    ∃ r : ℕ, ∃ Y : ℕ → Submodule E (Fin d → E), Y 0 = ⊥ ∧ Y r = Z ∧
      (∀ i j, i ≤ j → j ≤ r → Y i ≤ Y j) ∧
      (∀ i, i ≤ r → S9cInv N (Y i)) ∧
      (∀ i, i < r → Y i < Y (i + 1) ∧
        ∀ W : Submodule E (Fin d → E), S9cInv N W → Y i ≤ W → W ≤ Y (i + 1) →
          W = Y i ∨ W = Y (i + 1)) := by
  classical
  have hbot : S9cInv N (⊥ : Submodule E (Fin d → E)) := by
    intro g _ v hv
    rw [Submodule.mem_bot] at hv
    rw [hv, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  have up : ∀ n : ℕ, ∀ A : Submodule E (Fin d → E), S9cInv N A → A ≤ Z →
      Module.finrank E Z - Module.finrank E A ≤ n →
      ∃ r : ℕ, ∃ Y : ℕ → Submodule E (Fin d → E), Y 0 = A ∧ Y r = Z ∧
        (∀ i j, i ≤ j → j ≤ r → Y i ≤ Y j) ∧
        (∀ i, i ≤ r → S9cInv N (Y i)) ∧
        (∀ i, i < r → Y i < Y (i + 1) ∧
          ∀ W : Submodule E (Fin d → E), S9cInv N W → Y i ≤ W → W ≤ Y (i + 1) →
            W = Y i ∨ W = Y (i + 1)) := by
    intro n
    induction n with
    | zero =>
      intro A hA hAZ hn
      have hAeq : A = Z := by
        have h1 := Submodule.finrank_mono hAZ
        exact Submodule.eq_of_le_of_finrank_eq hAZ (by omega)
      refine ⟨0, fun _ => A, rfl, hAeq.symm ▸ rfl, fun i j _ _ => le_rfl,
        fun i _ => hA, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ n ih =>
      intro A hA hAZ hn
      by_cases hAeq : A = Z
      · refine ⟨0, fun _ => A, rfl, hAeq, fun i j _ _ => le_rfl, fun i _ => hA,
          fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      have hlt : A < Z := lt_of_le_of_ne hAZ hAeq
      have hQ : ∃ m : ℕ, ∃ W : Submodule E (Fin d → E),
          (S9cInv N W ∧ A < W ∧ W ≤ Z) ∧ Module.finrank E W = m :=
        ⟨_, Z, ⟨hZ, hlt, le_rfl⟩, rfl⟩
      obtain ⟨W₀, ⟨hW₀inv, hAW₀, hW₀Z⟩, hfW₀⟩ := Nat.find_spec hQ
      have hmin : ∀ W : Submodule E (Fin d → E), S9cInv N W → A < W → W ≤ Z →
          Nat.find hQ ≤ Module.finrank E W := fun W h1 h2 h3 =>
        Nat.find_min' hQ ⟨W, ⟨h1, h2, h3⟩, rfl⟩
      have hirr : ∀ W : Submodule E (Fin d → E), S9cInv N W → A ≤ W → W ≤ W₀ →
          W = A ∨ W = W₀ := by
        intro W hWinv hAW hWW₀
        by_cases hWA : W = A
        · exact Or.inl hWA
        by_cases hWW : W = W₀
        · exact Or.inr hWW
        exfalso
        have hAlt : A < W := lt_of_le_of_ne hAW (Ne.symm hWA)
        have hWlt : W < W₀ := lt_of_le_of_ne hWW₀ hWW
        have h1 := hmin W hWinv hAlt (hWW₀.trans hW₀Z)
        have h2 : Module.finrank E W < Module.finrank E W₀ :=
          Submodule.finrank_lt_finrank_of_lt hWlt
        rw [hfW₀] at h2
        omega
      have hfA : Module.finrank E A < Module.finrank E W₀ :=
        Submodule.finrank_lt_finrank_of_lt hAW₀
      have hfW₀Z : Module.finrank E W₀ ≤ Module.finrank E Z := Submodule.finrank_mono hW₀Z
      obtain ⟨r', Y', hY0', hYr', hmono', hinv', hsteps'⟩ :=
        ih W₀ hW₀inv hW₀Z (by omega)
      let Yf : ℕ → Submodule E (Fin d → E) := fun i => if i = 0 then A else Y' (i - 1)
      have hYf0 : Yf 0 = A := by simp [Yf]
      have hYfr : Yf (r' + 1) = Z := by simp [Yf, hYr']
      have hYfsucc : ∀ i, Yf (i + 1) = Y' i := by
        intro i
        simp [Yf]
      refine ⟨r' + 1, Yf, hYf0, hYfr, ?_, ?_, ?_⟩
      · intro i j hij hj
        rcases i with _ | i
        · rcases j with _ | j
          · exact le_rfl
          · rw [hYf0, hYfsucc j]
            exact hAW₀.le.trans (by simpa [hY0'] using hmono' 0 j (Nat.zero_le _) (by omega))
        · rcases j with _ | j
          · omega
          · rw [hYfsucc i, hYfsucc j]
            exact hmono' i j (by omega) (by omega)
      · intro i hi
        rcases i with _ | i
        · rw [hYf0]
          exact hA
        · rw [hYfsucc i]
          exact hinv' i (by omega)
      · intro i hi
        rcases i with _ | i
        · rw [hYf0, hYfsucc 0, hY0']
          exact ⟨hAW₀, fun W hWinv hAW hWW₀ => hirr W hWinv hAW hWW₀⟩
        · rw [hYfsucc i, hYfsucc (i + 1)]
          obtain ⟨hlt', hirr'⟩ := hsteps' i (by omega)
          exact ⟨hlt', hirr'⟩
  obtain ⟨r, Y, hY0, hYr, hmono, hinv, hsteps⟩ :=
    up (Module.finrank E Z) ⊥ hbot bot_le (by simp)
  exact ⟨r, Y, hY0, hYr, hmono, hinv, hsteps⟩

theorem s9c_rank_one_vec {E : Type} [Field E] {d : ℕ} {t : Matrix (Fin d) (Fin d) E}
    (hr : (t - 1).rank = 1) :
    ∃ u : Fin d → E, u ≠ 0 ∧ ∀ v : Fin d → E, ∃ c : E, (t - 1) *ᵥ v = c • u := by
  rw [Matrix.rank] at hr
  obtain ⟨v, hv0, hvall⟩ := finrank_eq_one_iff'.mp hr
  refine ⟨(v : Fin d → E), fun h => hv0 (Subtype.ext h), fun x => ?_⟩
  obtain ⟨c, hc⟩ := hvall ⟨(t - 1) *ᵥ x, LinearMap.mem_range_self _ x⟩
  refine ⟨c, ?_⟩
  have h2 := congrArg Subtype.val hc
  simpa using h2.symm

theorem s9c_pow_two_eq_one {E : Type} [Field E] [CharP E 2] {d : ℕ} (g : GL (Fin d) E) (r : ℕ)
    (h : ((g : Matrix (Fin d) (Fin d) E) - 1) ^ r = 0) : ∃ m : ℕ, g ^ (2 ^ m) = 1 := by
  set n : Matrix (Fin d) (Fin d) E := (g : Matrix (Fin d) (Fin d) E) - 1 with hn
  have hgn : (g : Matrix (Fin d) (Fin d) E) = n + 1 := by rw [hn, sub_add_cancel]
  have hxx : ∀ x : Matrix (Fin d) (Fin d) E, x + x = 0 := by
    intro x
    ext i j
    have h2E : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
    simp only [Matrix.add_apply, Matrix.zero_apply]
    rw [← two_mul, h2E, zero_mul]
  have hsq : ∀ x : Matrix (Fin d) (Fin d) E, (x + 1) ^ 2 = x ^ 2 + 1 := by
    intro x
    calc (x + 1) ^ 2 = x * x + (x + x) + 1 := by noncomm_ring
      _ = x ^ 2 + 1 := by rw [hxx x, add_zero, sq]
  have key : ∀ m : ℕ, (n + 1) ^ (2 ^ m) = n ^ (2 ^ m) + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      calc (n + 1) ^ (2 ^ (k + 1)) = ((n + 1) ^ (2 ^ k)) ^ 2 := by
            rw [pow_succ 2 k, pow_mul]
        _ = (n ^ (2 ^ k) + 1) ^ 2 := by rw [ih]
        _ = (n ^ (2 ^ k)) ^ 2 + 1 := hsq _
        _ = n ^ (2 ^ (k + 1)) + 1 := by rw [← pow_mul, pow_succ 2 k]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, r ≤ 2 ^ m := ⟨r, (Nat.lt_two_pow_self).le⟩
  have hnm : n ^ (2 ^ m) = 0 := pow_eq_zero_of_le hm h
  refine ⟨m, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, hgn, key, hnm, zero_add]

theorem s9c_flag_nilpotent {E : Type} [Field E] {d : ℕ} (r : ℕ) (Y : ℕ → Submodule E (Fin d → E))
    (hY0 : Y 0 = ⊥) (hYr : Y r = ⊤) (g : GL (Fin d) E)
    (hg : ∀ i, i < r → ∀ v ∈ Y (i + 1), (g : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∈ Y i) :
    ((g : Matrix (Fin d) (Fin d) E) - 1) ^ r = 0 := by
  have claim : ∀ k, k ≤ r → ∀ v ∈ Y r,
      (((g : Matrix (Fin d) (Fin d) E) - 1) ^ k) *ᵥ v ∈ Y (r - k) := by
    intro k
    induction k with
    | zero =>
      intro _ v hv
      simpa using hv
    | succ k ih =>
      intro hk v hv
      have h1 := ih (by omega) v hv
      have hidx : r - k = (r - (k + 1)) + 1 := by omega
      rw [hidx] at h1
      have h2 := hg (r - (k + 1)) (by omega) _ h1
      have e : (((g : Matrix (Fin d) (Fin d) E) - 1) ^ (k + 1)) *ᵥ v =
          (g : Matrix (Fin d) (Fin d) E) *ᵥ (((g : Matrix (Fin d) (Fin d) E) - 1) ^ k *ᵥ v) -
            ((g : Matrix (Fin d) (Fin d) E) - 1) ^ k *ᵥ v := by
        rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      rw [e]
      exact h2
  have hzero : ∀ v : Fin d → E, (((g : Matrix (Fin d) (Fin d) E) - 1) ^ r) *ᵥ v = 0 := by
    intro v
    have hv : v ∈ Y r := by
      rw [hYr]
      exact Submodule.mem_top
    have := claim r le_rfl v hv
    rw [Nat.sub_self, hY0] at this
    exact (Submodule.mem_bot E).mp this
  ext i j
  have := congrFun (hzero (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem s9c_flag_injective {E : Type} [Field E] {d : ℕ} (r : ℕ) (Y : ℕ → Submodule E (Fin d → E))
    (hY0 : Y 0 = ⊥) (hYr : Y r = ⊤) (Q : Matrix (Fin d) (Fin d) E)
    (hQ : ∀ i, i < r → ∀ v ∈ Y (i + 1), Q *ᵥ v ∈ Y i → v ∈ Y i) : Q.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hex : ∃ j, v ∈ Y j := ⟨r, by rw [hYr]; exact Submodule.mem_top⟩
  have hj : v ∈ Y (Nat.find hex) := Nat.find_spec hex
  have hjr : Nat.find hex ≤ r := Nat.find_min' hex (by rw [hYr]; exact Submodule.mem_top)
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, hY0] at hj
    exact hv0 ((Submodule.mem_bot E).mp hj)
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hvi : v ∈ Y (i + 1) := hi ▸ hj
  have hnot : v ∉ Y i := Nat.find_min hex (by omega)
  apply hnot
  apply hQ i (by omega) v hvi
  rw [hQv]
  exact (Y i).zero_mem

theorem s9c_false_of_pgroup {K₀ Ks : Type} [Group K₀] [Group Ks] [Finite Ks]
    (σ : K₀ →* Ks) (hσ : Function.Surjective σ) (hpg : ∀ x : K₀, ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hcard : Nat.card Ks = 168) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hcard]; norm_num : 3 ∣ Nat.card Ks)
  obtain ⟨y, rfl⟩ := hσ x
  obtain ⟨k, hk⟩ := hpg y
  have hpow : (σ y) ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have h3 : (3 : ℕ) ∣ 2 ^ k := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one hpow
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

end CFSG.Quasithin.H13.L829N

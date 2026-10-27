module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxSupp

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

@[expose] noncomputable def levTwoS2d_toStdDQ (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun x := fun a => x a - (if h : 0 < a.val then x ⟨a.val - 1, by omega⟩ else 0) +
      (if h : a.val + 2 = n then x ⟨a.val + 1, by omega⟩ else 0)
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem levTwoS2d_toStdDQ_apply (n : ℕ) (x : Fin n → ℚ) (a : Fin n) :
    levTwoS2d_toStdDQ n x a = x a - (if h : 0 < a.val then x ⟨a.val - 1, by omega⟩ else 0) +
      (if h : a.val + 2 = n then x ⟨a.val + 1, by omega⟩ else 0) := rfl

theorem levTwoS2d_toStdDQ_toRat (n : ℕ) (v : Fin n → ℤ) :
    levTwoS2d_toStdDQ n (toRat v) = toRat (toStdD n v) := by
  funext a
  simp only [levTwoS2d_toStdDQ_apply, toRat_apply, toStdD]
  push_cast
  by_cases h1 : 0 < a.val <;> by_cases h2 : a.val + 2 = n <;> simp [h1, h2]

theorem levTwoS2d_toStdDQ_eq_zero (n : ℕ) (hn : 4 ≤ n) {z : Fin n → ℚ}
    (h : levTwoS2d_toStdDQ n z = 0) : z = 0 := by
  have hlow : ∀ m, (hm : m ≤ n - 3) → z ⟨m, by omega⟩ = 0 := by
    intro m
    induction m with
    | zero =>
        intro _
        have h0 := congrFun h ⟨0, by omega⟩
        rw [levTwoS2d_toStdDQ_apply, Pi.zero_apply,
          dif_neg (show ¬ 0 < (0 : ℕ) by omega),
          dif_neg (show ¬ 0 + 2 = n by omega), sub_zero, add_zero] at h0
        exact h0
    | succ m ih =>
        intro hm
        have hm' : m ≤ n - 3 := by omega
        have hz := congrFun h ⟨m + 1, by omega⟩
        rw [levTwoS2d_toStdDQ_apply, Pi.zero_apply,
          dif_pos (show 0 < m + 1 by omega),
          dif_neg (show ¬ m + 1 + 2 = n by omega)] at hz
        have hprev : (⟨(m + 1) - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := by
          apply Fin.ext; simp only; omega
        rw [hprev, add_zero, sub_eq_zero] at hz
        rw [hz, ih hm']
  have hsum : z ⟨n - 2, by omega⟩ + z ⟨n - 1, by omega⟩ = 0 := by
    have hz := congrFun h ⟨n - 2, by omega⟩
    rw [levTwoS2d_toStdDQ_apply, Pi.zero_apply,
      dif_pos (show 0 < (n - 2 : ℕ) by omega),
      dif_pos (show (n - 2) + 2 = n by omega)] at hz
    have h3 : z ⟨n - 3, by omega⟩ = 0 := hlow (n - 3) (by omega)
    have hprev : (⟨(n - 2) - 1, by omega⟩ : Fin n) = ⟨n - 3, by omega⟩ := by
      apply Fin.ext; simp only; omega
    have hnext : (⟨(n - 2) + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := by
      apply Fin.ext; simp only; omega
    rw [hprev, hnext, h3, sub_zero] at hz
    linarith
  have hlast1 : z ⟨n - 1, by omega⟩ = z ⟨n - 2, by omega⟩ := by
    have hz := congrFun h ⟨n - 1, by omega⟩
    rw [levTwoS2d_toStdDQ_apply, Pi.zero_apply,
      dif_pos (show 0 < (n - 1 : ℕ) by omega),
      dif_neg (show ¬ (n - 1) + 2 = n by omega)] at hz
    have hprev : (⟨(n - 1) - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
      apply Fin.ext; simp only; omega
    rw [hprev, add_zero, sub_eq_zero] at hz
    exact hz
  have hlast2 : z ⟨n - 2, by omega⟩ = 0 := by
    have := hsum
    rw [← hlast1] at this
    linarith
  funext k
  by_cases hk : k.val ≤ n - 3
  · exact hlow k.val hk
  · have hk2 : k.val = n - 2 ∨ k.val = n - 1 := by omega
    rcases hk2 with hk2 | hk2
    · have : k = ⟨n - 2, by omega⟩ := Fin.ext hk2
      rw [this]; exact hlast2
    · have : k = ⟨n - 1, by omega⟩ := Fin.ext hk2
      rw [this, hlast1, hlast2, Pi.zero_apply]

theorem levTwoS2d_card_le_Z {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (_hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {s : Finset (Fin n → ℤ)}
    (hsΦ : (s : Set (Fin n → ℤ)) ⊆ Φ) (hlin : LinearIndependent ℚ (fun v : s => toRat (v : Fin n → ℤ)))
    (hZ : levTwoS2d_Supp n hn c Φ ⊆ levTwoS2d_Z n hn c) :
    s.card ≤ Nat.card (levTwoS2d_Z n hn c) := by
  classical
  set Z := levTwoS2d_Z n hn c with hZdef
  have hsupp : ∀ β ∈ s, ∀ a, toStdD n β a ≠ 0 → a ∈ Z := by
    intro β hβ a ha
    exact hZ ⟨β, hsΦ (Finset.mem_coe.mpr hβ), ha⟩
  have hzero : ∀ β ∈ s, ∀ a, a ∉ Z → toStdD n β a = 0 := by
    intro β hβ a ha
    by_contra hne
    exact ha (hsupp β hβ a hne)
  have hind : LinearIndependent ℚ
      (fun β : s => fun a : Z => levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a.1) := by
    rw [linearIndependent_iff']
    intro t g hsum β hβ
    have hsum' : (∑ β ∈ t, g β • levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ))) = 0 := by
      funext a
      by_cases ha : a ∈ Z
      · have h := congrFun hsum ⟨a, ha⟩
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      · have h0 : ∀ β : s, levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) a = 0 := by
          intro β
          rw [levTwoS2d_toStdDQ_toRat, toRat_apply]
          simp [hzero β.1 β.2 a ha]
        simp [h0]
    have hcomb : levTwoS2d_toStdDQ n (∑ β ∈ t, g β • toRat (β : Fin n → ℤ)) = 0 := by
      rw [map_sum]
      rw [show (∑ β ∈ t, levTwoS2d_toStdDQ n (g β • toRat (β : Fin n → ℤ))) =
          ∑ β ∈ t, g β • levTwoS2d_toStdDQ n (toRat (β : Fin n → ℤ)) from by
        apply Finset.sum_congr rfl; intro β _; rw [map_smul]]
      exact hsum'
    have hzero2 : (∑ β ∈ t, g β • toRat (β : Fin n → ℤ)) = 0 :=
      levTwoS2d_toStdDQ_eq_zero n hn hcomb
    exact (linearIndependent_iff'.mp hlin) t g hzero2 β hβ
  have hle := LinearIndependent.fintype_card_le_finrank hind
  rw [Module.finrank_fintype_fun_eq_card] at hle
  rw [Nat.card_eq_fintype_card]
  simpa using hle

@[expose] noncomputable def levTwoS2d_sigma {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n)
    (c : Fin n → ZMod p) (c₀ : ZMod p) (a : Fin n) : ℤ :=
  if levTwoS2d_d n hn c a = c₀ then 1 else -1

theorem levTwoS2d_sigma_spec {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n)
    (c : Fin n → ZMod p) {c₀ : ZMod p} {a : Fin n}
    (hda : levTwoS2d_d n hn c a = c₀ ∨ levTwoS2d_d n hn c a = -c₀) :
    ((levTwoS2d_sigma n hn c c₀ a : ℤ) : ZMod p) * c₀ = levTwoS2d_d n hn c a := by
  unfold levTwoS2d_sigma
  by_cases h : levTwoS2d_d n hn c a = c₀
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]
    rcases hda with h' | h'
    · exact absurd h' h
    · rw [h', Int.cast_neg, Int.cast_one, neg_one_mul]
      exact congrArg Neg.neg rfl

theorem levTwoS2d_intCast_eq_zero_of_abs_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℤ}
    (hm : m = -2 ∨ m = 0 ∨ m = 2) (h : (m : ZMod p) = 0) : m = 0 := by
  rcases hm with rfl | rfl | rfl
  · exfalso
    have hdvd_int : (p : ℤ) ∣ -2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (-2) p).mp h
    have hdvd_int2 : (p : ℤ) ∣ 2 := dvd_neg.mp hdvd_int
    have hdvd : p ∣ 2 := by exact_mod_cast hdvd_int2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  · rfl
  · exfalso
    have hdvd_int : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h
    have hdvd : p ∣ 2 := by exact_mod_cast hdvd_int
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega

end CFSG.StandardType.LevTwo


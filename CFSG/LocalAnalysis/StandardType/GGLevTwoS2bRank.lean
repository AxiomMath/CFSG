module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bSupp

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

@[expose] noncomputable def levTwoS2b_coordQ (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun x := fun a => x a - (if h : 0 < a.val then x ⟨a.val - 1, by omega⟩ else 0)
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem levTwoS2b_coordQ_toRat (n : ℕ) (v : Fin n → ℤ) :
    levTwoS2b_coordQ n (toRat v) = toRat (levTwoS2b_coord n v) := by
  funext a
  simp only [levTwoS2b_coordQ, levTwoS2b_coord, CFSG.LieType.Universal.Spin.toStdB,
    toRat_apply]
  push_cast
  by_cases h : 0 < a.val <;> simp [h]

theorem levTwoS2b_coordQ_eq_zero (n : ℕ) (_hn : 1 ≤ n) {z : Fin n → ℚ}
    (h : levTwoS2b_coordQ n z = 0) : z = 0 := by
  have hzero : ∀ m : ℕ, ∀ hm : m < n, z ⟨m, hm⟩ = 0 := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hz := congrFun h ⟨0, hm⟩
        simp only [levTwoS2b_coordQ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hz
        rw [dif_neg (show ¬ 0 < (0 : ℕ) by omega), sub_zero] at hz
        exact hz
    | succ m ih =>
        intro hm
        have hz := congrFun h ⟨m + 1, hm⟩
        simp only [levTwoS2b_coordQ, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hz
        rw [dif_pos (show 0 < m + 1 by omega)] at hz
        have hprev : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := by
          apply Fin.ext; simp
        rw [hprev, sub_eq_zero] at hz
        rw [hz, ih (by omega)]
  funext k
  exact hzero k.val k.isLt

theorem levTwoS2b_card_le_Z {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 1 ≤ n) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (_hΦ : LevTwoData (isFiniteType_cartanB n) p c Φ) {s : Finset (Fin n → ℤ)}
    (hsΦ : (s : Set (Fin n → ℤ)) ⊆ Φ)
    (hlin : LinearIndependent ℚ (fun v : s => toRat (v : Fin n → ℤ)))
    (hZ : levTwoS2b_Supp n c Φ ⊆ levTwoS2b_Z c) :
    s.card ≤ Nat.card (levTwoS2b_Z c) := by
  classical
  set Z := levTwoS2b_Z c with hZdef
  have hsupp : ∀ β ∈ s, ∀ a, levTwoS2b_coord n β a ≠ 0 → a ∈ Z := by
    intro β hβ a ha
    exact hZ ⟨β, hsΦ (Finset.mem_coe.mpr hβ), ha⟩
  have hzero : ∀ β ∈ s, ∀ a, a ∉ Z → levTwoS2b_coord n β a = 0 := by
    intro β hβ a ha
    by_contra hne
    exact ha (hsupp β hβ a hne)
  have hind : LinearIndependent ℚ
      (fun β : s => fun a : Z => levTwoS2b_coordQ n (toRat (β : Fin n → ℤ)) a.1) := by
    rw [linearIndependent_iff']
    intro t g hsum β hβ
    have hsum' : (∑ β ∈ t, g β • levTwoS2b_coordQ n (toRat (β : Fin n → ℤ))) = 0 := by
      funext a
      by_cases ha : a ∈ Z
      · have h := congrFun hsum ⟨a, ha⟩
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      · have h0 : ∀ β : s, levTwoS2b_coordQ n (toRat (β : Fin n → ℤ)) a = 0 := by
          intro β
          rw [levTwoS2b_coordQ_toRat, toRat_apply]
          simp [hzero β.1 β.2 a ha]
        simp [h0]
    have hcomb : levTwoS2b_coordQ n (∑ β ∈ t, g β • toRat (β : Fin n → ℤ)) = 0 := by
      rw [map_sum]
      rw [show (∑ β ∈ t, levTwoS2b_coordQ n (g β • toRat (β : Fin n → ℤ))) =
          ∑ β ∈ t, g β • levTwoS2b_coordQ n (toRat (β : Fin n → ℤ)) from by
        apply Finset.sum_congr rfl; intro β _; rw [map_smul]]
      exact hsum'
    have hzero2 : (∑ β ∈ t, g β • toRat (β : Fin n → ℤ)) = 0 :=
      levTwoS2b_coordQ_eq_zero n hn hcomb
    exact (linearIndependent_iff'.mp hlin) t g hzero2 β hβ
  have hle := LinearIndependent.fintype_card_le_finrank hind
  rw [Module.finrank_fintype_fun_eq_card] at hle
  rw [Nat.card_eq_fintype_card]
  simpa using hle

@[expose] noncomputable def levTwoS2b_sigma {p : ℕ} (n : ℕ) (c : Fin n → ZMod p) (c₀ : ZMod p)
    (a : Fin n) : ℤ :=
  if levTwoS2b_D c a = c₀ then 1 else -1

theorem levTwoS2b_sigma_spec {p : ℕ} (n : ℕ) (c : Fin n → ZMod p) {c₀ : ZMod p} {a : Fin n}
    (hda : levTwoS2b_D c a = c₀ ∨ levTwoS2b_D c a = -c₀) :
    ((levTwoS2b_sigma n c c₀ a : ℤ) : ZMod p) * c₀ = levTwoS2b_D c a := by
  unfold levTwoS2b_sigma
  by_cases h : levTwoS2b_D c a = c₀
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]
    rcases hda with h' | h'
    · exact absurd h' h
    · rw [h', Int.cast_neg, Int.cast_one, neg_one_mul]

theorem levTwoS2b_intCast_eq_zero_of_abs_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℤ}
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

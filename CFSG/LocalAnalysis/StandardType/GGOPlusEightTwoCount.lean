module

public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoLayer

public section

namespace CFSG.StandardType

namespace OPlusEight

namespace Cnt

open scoped Classical

@[expose] noncomputable def chi {K : Type} [Field K] (c : K) : ℤ := if c = 0 then 1 else -1

section Chi

variable {K : Type} [Field K] [CharP K 2]

theorem chi_zero : chi (0 : K) = 1 := by simp [chi]

theorem chi_one : chi (1 : K) = -1 := by simp [chi]

theorem chi_add (hK : ∀ c : K, c = 0 ∨ c = 1) (a b : K) : chi (a + b) = chi a * chi b := by
  rcases hK a with rfl | rfl <;> rcases hK b with rfl | rfl
  · simp [chi_zero]
  · simp [chi_zero, chi_one]
  · simp [chi_zero, chi_one]
  · rw [CharTwo.add_self_eq_zero, chi_zero, chi_one]
    norm_num

theorem sum_chi_eq_zero (hK : ∀ c : K, c = 0 ∨ c = 1) {Y : Type} [AddCommGroup Y] [Fintype Y]
    (φ : Y → K) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (hne : ∃ y, φ y ≠ 0) :
    ∑ y : Y, chi (φ y) = 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  have h1 : φ y₀ = 1 := (hK _).resolve_left hy₀
  have h2 : ∑ y : Y, chi (φ (y + y₀)) = ∑ y : Y, chi (φ y) :=
    Fintype.sum_equiv (Equiv.addRight y₀) _ _ (fun y => rfl)
  have h3 : ∀ y : Y, chi (φ (y + y₀)) = - chi (φ y) := fun y => by
    rw [hφ, h1, chi_add hK, chi_one]
    ring
  simp only [h3, Finset.sum_neg_distrib] at h2
  omega

end Chi

section QSum

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V] [Fintype V]

@[expose] noncomputable def qsum (Q : QuadraticForm K V) (S : Submodule K V) : ℤ :=
  ∑ v : S, chi (Q (v : V))

theorem qsum_sq (hK : ∀ c : K, c = 0 ∨ c = 1) (Q : QuadraticForm K V) (S : Submodule K V)
    (hreg : ∀ x ∈ S, (∀ y ∈ S, QuadraticMap.polar Q x y = 0) → x = 0) :
    (qsum Q S) ^ 2 = (Fintype.card S : ℤ) := by
  have hrow : ∀ v : S, ∑ w : S, chi (Q (w : V)) = ∑ u : S, chi (Q ((v : V) + (u : V))) :=
    fun v => (Fintype.sum_equiv (Equiv.addLeft v) (fun u : S => chi (Q ((v : V) + (u : V))))
      (fun w : S => chi (Q (w : V))) (fun u => rfl)).symm
  have hterm : ∀ v u : S, chi (Q (v : V)) * chi (Q ((v : V) + (u : V))) =
      chi (Q (u : V)) * chi (QuadraticMap.polar Q (v : V) (u : V)) := by
    intro v u
    rw [← chi_add hK, ← chi_add hK]
    congr 1
    have h1 : Q ((v : V) + (u : V)) =
        Q (v : V) + Q (u : V) + QuadraticMap.polar Q (v : V) (u : V) := by
      rw [QuadraticMap.polar]
      ring
    rw [h1]
    have h2 : Q (v : V) + (Q (v : V) + Q (u : V) + QuadraticMap.polar Q (v : V) (u : V)) =
        (Q (v : V) + Q (v : V)) + Q (u : V) + QuadraticMap.polar Q (v : V) (u : V) := by ring
    rw [h2, CharTwo.add_self_eq_zero, zero_add]
  have hinner : ∀ u : S, ∑ v : S, chi (QuadraticMap.polar Q (v : V) (u : V)) =
      if u = 0 then (Fintype.card S : ℤ) else 0 := by
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [chi_zero]
    · rw [if_neg hu]
      refine sum_chi_eq_zero hK _ (fun a b => by
        simp only [Submodule.coe_add, QuadraticMap.polar_add_left]) ?_
      by_contra hcon
      push Not at hcon
      apply hu
      apply Subtype.ext
      refine hreg u u.2 (fun y hy => ?_)
      rw [QuadraticMap.polar_comm]
      exact hcon ⟨y, hy⟩
  calc (qsum Q S) ^ 2 = (∑ v : S, chi (Q (v : V))) * (∑ w : S, chi (Q (w : V))) := by
        rw [qsum, sq]
    _ = ∑ v : S, ∑ u : S, chi (Q (v : V)) * chi (Q ((v : V) + (u : V))) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum, hrow v, Finset.mul_sum]
    _ = ∑ v : S, ∑ u : S, chi (Q (u : V)) * chi (QuadraticMap.polar Q (v : V) (u : V)) :=
        Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => hterm v u
    _ = ∑ u : S, ∑ v : S, chi (Q (u : V)) * chi (QuadraticMap.polar Q (v : V) (u : V)) :=
        Finset.sum_comm
    _ = ∑ u : S, chi (Q (u : V)) * ∑ v : S, chi (QuadraticMap.polar Q (v : V) (u : V)) :=
        Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    _ = (Fintype.card S : ℤ) := by
        simp only [hinner]
        rw [Finset.sum_eq_single (0 : S)]
        · simp [chi_zero]
        · intro u _ hu
          simp [hu]
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem eq_zero_or_one_of_card_two [Finite K] (hcard : Nat.card K = 2) :
    ∀ c : K, c = 0 ∨ c = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  intro a
  have h := FiniteField.pow_card a
  rw [← Nat.card_eq_fintype_card, hcard, pow_two] at h
  have h' : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h0)

theorem qsum_eq [Finite K] [Module.Finite K V] (hcard : Nat.card K = 2) (Q : QuadraticForm K V)
    (S : Submodule K V)
    (hreg : ∀ x ∈ S, (∀ y ∈ S, QuadraticMap.polar Q x y = 0) → x = 0) :
    ∃ j : ℕ, Module.finrank K S = 2 * j ∧ (qsum Q S = 2 ^ j ∨ qsum Q S = -2 ^ j) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hsq := qsum_sq (eq_zero_or_one_of_card_two hcard) Q S hreg
  have hc : Fintype.card S = 2 ^ Module.finrank K S := by
    rw [Module.card_eq_pow_finrank (K := K) (V := S), ← Nat.card_eq_fintype_card, hcard]
  rw [hc] at hsq
  have hn : (qsum Q S).natAbs ^ 2 = 2 ^ Module.finrank K S := by
    have := congrArg Int.natAbs hsq
    simpa [Int.natAbs_pow] using this
  have hdvd : (qsum Q S).natAbs ∣ 2 ^ Module.finrank K S := by
    rw [← hn]
    exact Dvd.intro_left _ (sq _).symm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h2j : Module.finrank K S = 2 * j := by
    have : 2 ^ (2 * j) = 2 ^ Module.finrank K S := by
      rw [← hn, hj, ← pow_mul, mul_comm]
    exact (Nat.pow_right_injective le_rfl this).symm
  refine ⟨j, h2j, ?_⟩
  rcases Int.natAbs_eq (qsum Q S) with h | h
  · left
    rw [h, hj]
    push_cast
    rfl
  · right
    rw [h, hj]
    push_cast
    rfl

theorem card_pred_modEq {p : ℕ} [Fact p.Prime] (x : V ≃ₗ[K] V) (hxp : x ^ p = 1)
    (S : Submodule K V) (hS : ∀ v ∈ S, x v ∈ S) (P : V → Prop) (hP : ∀ v, P v → P (x v)) :
    Fintype.card {v : S // P (v : V)} ≡
      Fintype.card {v : ↥(S ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace x) // P (v : V)} [MOD p] := by
  let α := {v : S // P (v : V)}
  let f : Function.End α := fun v => ⟨⟨x (v : V), hS _ v.1.2⟩, hP _ v.2⟩
  have hfpow : ∀ n : ℕ, ∀ v : α, (((f ^ n) v : α) : S).1 = (x ^ n) (v : S).1 := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ]
      show (((f ^ n) (f v) : α) : S).1 = (x ^ n) (x (v : S).1)
      rw [ih]
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext v
    apply Subtype.ext
    apply Subtype.ext
    rw [hfpow, hxp]
    rfl
  have h1 := Equiv.Perm.card_fixedPoints_modEq hf
  have h2 : Fintype.card (Function.fixedPoints f) =
      Fintype.card {v : ↥(S ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace x) // P (v : V)} := by
    refine Fintype.card_congr
      { toFun := fun w => ⟨⟨(w.1.1.1 : V), ⟨w.1.1.2,
          CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr
            (congrArg (fun a : α => ((a : S) : V)) w.2)⟩⟩, w.1.2⟩
        invFun := fun u => ⟨⟨⟨(u.1.1 : V), u.1.2.1⟩, u.2⟩, ?_⟩
        left_inv := fun w => rfl
        right_inv := fun u => rfl }
    apply Subtype.ext
    apply Subtype.ext
    exact CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp u.1.2.2
  rw [h2] at h1
  exact h1

theorem qsum_eq_card (hK : ∀ c : K, c = 0 ∨ c = 1) (Q : QuadraticForm K V) (S : Submodule K V) :
    qsum Q S = (Fintype.card {v : S // Q (v : V) = 0} : ℤ) -
      Fintype.card {v : S // Q (v : V) = 1} := by
  unfold qsum
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have h : ∀ v : S, chi (Q (v : V)) =
      (if Q (v : V) = 0 then (1 : ℤ) else 0) - (if Q (v : V) = 1 then (1 : ℤ) else 0) := by
    intro v
    rcases hK (Q (v : V)) with h0 | h0
    · simp [chi_zero, h0]
    · simp [chi_one, h0]
  simp_rw [h]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_boole]

theorem card_modEq {p : ℕ} [Fact p.Prime] (x : V ≃ₗ[K] V) (hxp : x ^ p = 1) (S : Submodule K V)
    (hS : ∀ v ∈ S, x v ∈ S) :
    Fintype.card S ≡
      Fintype.card ↥(S ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace x) [MOD p] := by
  have h := card_pred_modEq x hxp S hS (fun _ => True) (fun _ _ => trivial)
  simp only [← Nat.card_eq_fintype_card] at h ⊢
  rwa [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)),
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))] at h

theorem qsum_modEq (hK : ∀ c : K, c = 0 ∨ c = 1) {p : ℕ} [Fact p.Prime] (Q : QuadraticForm K V)
    (x : V ≃ₗ[K] V) (hxQ : ∀ v, Q (x v) = Q v) (hxp : x ^ p = 1) (S : Submodule K V)
    (hS : ∀ v ∈ S, x v ∈ S) :
    qsum Q S ≡ qsum Q (S ⊓ CFSG.RankThree.PartOne.LIT.fixedSpace x) [ZMOD p] := by
  rw [qsum_eq_card hK, qsum_eq_card hK]
  have h0 := card_pred_modEq x hxp S hS (fun v => Q v = 0) (fun v hv => by rw [hxQ]; exact hv)
  have h1 := card_pred_modEq x hxp S hS (fun v => Q v = 1) (fun v hv => by rw [hxQ]; exact hv)
  exact Int.ModEq.sub ((Int.natCast_modEq_iff).mpr h0) ((Int.natCast_modEq_iff).mpr h1)

end QSum

section Arith

theorem prime_cases (q f : ℕ) (hq : q.Prime) (hq3 : 3 < q)
    (hf : f = 0 ∨ f = 2 ∨ f = 4 ∨ f = 6) (h3 : ((2 : ℤ) ^ 8) ≡ 2 ^ f [ZMOD q]) :
    (f = 0 ∧ (q = 5 ∨ q = 17)) ∨ (f = 2 ∧ q = 7) ∨ (f = 4 ∧ q = 5) := by
  have hd := Int.ModEq.dvd h3
  have key : ∀ N : ℕ, ((q : ℤ) ∣ (N : ℤ)) → q ∣ N := fun N h => by exact_mod_cast h
  rcases hf with rfl | rfl | rfl | rfl
  · have h : q ∣ 255 := key 255 (by simpa using hd)
    have hmem : q ∈ Nat.divisors 255 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
    have e : Nat.divisors 255 = {1, 3, 5, 15, 17, 51, 85, 255} := by decide
    rw [e] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | (exfalso; norm_num at hq) | (left; omega)
  · have h : q ∣ 252 := key 252 (by simpa using hd)
    have hmem : q ∈ Nat.divisors 252 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
    have e : Nat.divisors 252 =
        {1, 2, 3, 4, 6, 7, 9, 12, 14, 18, 21, 28, 36, 42, 63, 84, 126, 252} := by decide
    rw [e] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      first | omega | (exfalso; norm_num at hq) | (right; left; omega)
  · have h : q ∣ 240 := key 240 (by simpa using hd)
    have hmem : q ∈ Nat.divisors 240 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
    have e : Nat.divisors 240 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 24, 30, 40, 48, 60, 80,
        120, 240} := by decide
    rw [e] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | omega | (exfalso; norm_num at hq) | (right; right; omega)
  · have h : q ∣ 192 := key 192 (by simpa using hd)
    have hmem : q ∈ Nat.divisors 192 := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
    have e : Nat.divisors 192 = {1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 192} := by decide
    rw [e] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> first | omega | (exfalso; norm_num at hq)

theorem arith_contra (q : ℕ) (hq : q.Prime) (hq3 : 3 < q) (d f z : ℕ) (hd : d = 2 ∨ d = 4)
    (hf : f = 0 ∨ f = 2 ∨ f = 4 ∨ f = 6) (hz : z = 0 ∨ z = 2 ∨ z = 4) (hzd : z ≤ d) (hzf : z ≤ f)
    (hsum : d + f ≤ 8 + z) (eU eF eZ : ℤ)
    (hU : eU = 2 ^ (d / 2) ∨ eU = -2 ^ (d / 2)) (hF : eF = 2 ^ (f / 2) ∨ eF = -2 ^ (f / 2))
    (hZ : eZ = 2 ^ (z / 2) ∨ eZ = -2 ^ (z / 2)) (hF0 : f = 0 → eF = 1) (hZ0 : z = 0 → eZ = 1)
    (h2 : (16 : ℤ) ≡ eU [ZMOD 3]) (h3 : ((2 : ℤ) ^ 8) ≡ 2 ^ f [ZMOD q])
    (h4 : (16 : ℤ) ≡ eF [ZMOD q]) (h5 : ((2 : ℤ) ^ d) ≡ 2 ^ z [ZMOD q])
    (h6 : eU ≡ eZ [ZMOD q]) (h7 : ((2 : ℤ) ^ f) ≡ 2 ^ z [ZMOD 3]) (h8 : eF ≡ eZ [ZMOD 3]) :
    False := by
  rcases prime_cases q f hq hq3 hf h3 with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hd with rfl | rfl <;> rcases hz with rfl | rfl | rfl <;>
  rcases hU with rfl | rfl <;> rcases hF with rfl | rfl <;> rcases hZ with rfl | rfl <;>
  (simp only [Int.ModEq] at *; norm_num at *; try omega)

end Arith

end Cnt

end OPlusEight

end CFSG.StandardType

end

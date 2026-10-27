module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

private theorem s1667_fix_card_fix_modEq {T : Type} [Group T] [Finite T] (p : ℕ) [Fact p.Prime]
    (α : MulAut T) (m : ℕ) (hα : α ^ (p ^ m) = 1) (V : Subgroup T)
    (hV : ∀ v ∈ V, α v ∈ V) :
    Nat.card V ≡ Nat.card {v : V // α v = v} [MOD p] := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let f : Function.End V := fun d => ⟨α d, hV d d.2⟩
  have hf : ∀ k : ℕ, ∀ d : V, ((f ^ k) d : T) = (α ^ k) d := by
    intro k
    induction k with
    | zero => intro d; rfl
    | succ k ih =>
      intro d
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f d) : T) = (α ^ k) (α d)
      rw [ih]
  have hfp : f ^ p ^ m = 1 := by
    funext d
    apply Subtype.ext
    rw [hf, hα]
    rfl
  have := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := m) hfp
  rw [Nat.card_eq_fintype_card]
  have h2 : Nat.card {d : V // α d = d} = Fintype.card f.fixedPoints := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun d => by
      show α d = d ↔ f d = d
      constructor
      · intro h; exact Subtype.ext h
      · intro h; exact congrArg Subtype.val h)
  rw [h2]
  exact this

theorem mulAut_eq_one_of_commutator_small {W : Type} [Group W] [Finite W]
    (hcomm : ∀ x y : W, x * y = y * x) (h2 : ∀ x : W, x ^ 2 = 1) (φ : MulAut W)
    (hφ : IsPGroup 13 (Subgroup.zpowers φ)) (B : Subgroup W) (hB : Nat.card B ≤ 2 ^ 10)
    (hBφ : ∀ b ∈ B, φ b ∈ B) (hφB : ∀ w : W, φ w * w⁻¹ ∈ B) : φ = 1 := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hφ) ⟨φ, Subgroup.mem_zpowers φ⟩
  rw [Subgroup.orderOf_mk] at hn
  have hφn : φ ^ 13 ^ n = 1 := by
    rw [← hn, pow_orderOf_eq_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro b
    refine ⟨1, ?_⟩
    rw [pow_one, orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (by
      show (b : W) ^ 2 = 1
      exact h2 (b : W))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB2
  have hk10 : k ≤ 10 := by
    have h : 2 ^ k ≤ 2 ^ 10 := by rw [← hk]; exact hB
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp h
  let F : Subgroup B :=
    { carrier := {b | φ (b : W) = (b : W)}
      mul_mem' := by
        intro a b ha hb
        change φ ((a : W) * (b : W)) = (a : W) * (b : W)
        rw [map_mul, ha, hb]
      one_mem' := by
        change φ (1 : W) = 1
        rw [map_one]
      inv_mem' := by
        intro a ha
        change φ ((a : W)⁻¹) = (a : W)⁻¹
        rw [map_inv, ha] }
  have hFcard : Nat.card {b : B // φ (b : W) = (b : W)} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  have hmod : Nat.card B ≡ Nat.card {b : B // φ (b : W) = (b : W)} [MOD 13] :=
    s1667_fix_card_fix_modEq 13 φ n hφn B hBφ
  have hdvd : Nat.card F ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.card_subgroup_dvd_card F
  obtain ⟨m, hmk, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hmod' : 2 ^ k ≡ 2 ^ m [MOD 13] := by
    rw [hk, hFcard, hm] at hmod
    exact hmod
  have hkm : k = m := by
    have hmod'' : 2 ^ k % 13 = 2 ^ m % 13 := hmod'
    interval_cases k <;> interval_cases m <;> simp_all
  have hcardF : Nat.card F = Nat.card B := by rw [hm, ← hkm, ← hk]
  have hFtop : F = ⊤ := (Subgroup.card_eq_iff_eq_top F).mp hcardF
  have hbfix : ∀ b : B, φ (b : W) = (b : W) := by
    intro b
    have : b ∈ F := by rw [hFtop]; exact Subgroup.mem_top b
    exact this
  have hφφ : φ * φ = 1 := by
    ext w
    have hb : φ w * w⁻¹ ∈ B := hφB w
    have hfix : φ (φ w * w⁻¹) = φ w * w⁻¹ := hbfix ⟨φ w * w⁻¹, hb⟩
    rw [map_mul, map_inv] at hfix
    show φ (φ w) = w
    have hc : (φ w)⁻¹ = φ w :=
      inv_eq_iff_mul_eq_one.mpr (by rw [← sq, h2])
    have hd : w⁻¹ = w := inv_eq_iff_mul_eq_one.mpr (by rw [← sq, h2])
    rw [hc, hd] at hfix
    have hsq : φ w * φ w = 1 := by rw [← sq, h2]
    calc φ (φ w) = φ (φ w) * (φ w * φ w) := by rw [hsq, mul_one]
      _ = (φ (φ w) * φ w) * φ w := by rw [mul_assoc]
      _ = (φ w * w) * φ w := by rw [hfix]
      _ = w * (φ w * φ w) := by rw [hcomm (φ w) w, mul_assoc]
      _ = w := by rw [hsq, mul_one]
  have hφ2 : φ ^ 2 = 1 := by rw [pow_two]; exact hφφ
  have hdvd2 : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one hφ2
  rw [hn] at hdvd2
  have hn0 : n = 0 := by
    by_contra hn'
    exact absurd (dvd_trans (dvd_pow_self 13 hn') hdvd2) (by decide)
  have hone : orderOf φ = 1 := by rw [hn, hn0, pow_zero]
  exact orderOf_eq_one_iff.mp hone

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

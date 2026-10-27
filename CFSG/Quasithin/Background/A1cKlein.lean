module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin

namespace A1c

open Matrix

variable {F : Type*} [Field F]

theorem det_eq_neg_one_of_sq_eq_one {M : Matrix (Fin 2) (Fin 2) F}
    (hM : M * M = 1) (h1 : M ≠ 1) (hn : M ≠ -1) : M.det = -1 := by
  have e := Matrix.eta_fin_two M
  set x := M 0 0 with hx
  set y := M 0 1 with hy
  set z := M 1 0 with hz
  set w := M 1 1 with hw
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, ← hx, ← hy, ← hz, ← hw] at h00 h01 h10 h11
  have hdet : M.det = x * w - y * z := Matrix.det_fin_two M
  rw [hdet]
  by_cases hs : x + w = 0
  · have : w = -x := by linear_combination hs
    rw [this]
    linear_combination -h00
  · exfalso
    have hy0 : y = 0 := by
      have : y * (x + w) = 0 := by linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hz0 : z = 0 := by
      have : z * (x + w) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hy0, hz0] at h00 h11
    simp at h00 h11
    have hxx : (x - 1) * (x + 1) = 0 := by linear_combination h00
    have hww : (w - 1) * (w + 1) = 0 := by linear_combination h11
    rcases mul_eq_zero.1 hxx with hx1 | hx1 <;> rcases mul_eq_zero.1 hww with hw1 | hw1
    · apply h1
      rw [e, hy0, hz0, show x = 1 by linear_combination hx1, show w = 1 by linear_combination hw1]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    · apply hs
      rw [show x = 1 by linear_combination hx1, show w = -1 by linear_combination hw1]; ring
    · apply hs
      rw [show x = -1 by linear_combination hx1, show w = 1 by linear_combination hw1]; ring
    · apply hn
      rw [e, hy0, hz0, show x = -1 by linear_combination hx1, show w = -1 by linear_combination hw1]
      ext i j; fin_cases i <;> fin_cases j <;> simp

theorem eq_one_or_neg_one_of_sq_eq_one_fin_one {a : GL (Fin 1) F} (ha : a ^ 2 = 1) :
    a = 1 ∨ a = -1 := by
  have h : ((a : Matrix (Fin 1) (Fin 1) F) 0 0) * (a : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 := by
    have := congrArg (fun u : GL (Fin 1) F => (u : Matrix (Fin 1) (Fin 1) F) 0 0) ha
    simpa [pow_two, Matrix.mul_apply] using this
  have h' : ((a : Matrix (Fin 1) (Fin 1) F) 0 0 - 1) *
      ((a : Matrix (Fin 1) (Fin 1) F) 0 0 + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · left
    apply Units.ext
    ext i j
    fin_cases i; fin_cases j
    simp [show (a : Matrix (Fin 1) (Fin 1) F) 0 0 = 1 by linear_combination h1]
  · right
    apply Units.ext
    ext i j
    fin_cases i; fin_cases j
    simp [show (a : Matrix (Fin 1) (Fin 1) F) 0 0 = -1 by linear_combination h1]

theorem neg_one_of_klein (h2 : (2 : F) ≠ 0) {d : ℕ} (hd : d ≤ 2) {a b : GL (Fin d) F}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab1 : a * b ≠ 1) : a = -1 ∨ b = -1 ∨ a * b = -1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hna, hnb, hnab⟩ := hcon
  interval_cases d
  · exact ha1 (Subsingleton.elim _ _)
  · exact (eq_one_or_neg_one_of_sq_eq_one_fin_one ha).elim ha1 hna
  · have hdet : ∀ g : GL (Fin 2) F, g ^ 2 = 1 → g ≠ 1 → g ≠ -1 →
        (g : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      intro g hg hg1 hgn
      refine det_eq_neg_one_of_sq_eq_one ?_ ?_ ?_
      · have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hg
        simpa [pow_two] using this
      · intro h; apply hg1; exact Units.ext h
      · intro h; apply hgn; exact Units.ext (by simpa using h)
    have hab2 : (a * b) ^ 2 = 1 := by
      rw [pow_two, mul_assoc, ← mul_assoc b, ← hab, mul_assoc, ← mul_assoc a, ← pow_two, ha,
        one_mul, ← pow_two, hb]
    have d1 := hdet a ha ha1 hna
    have d2 := hdet b hb hb1 hnb
    have d3 := hdet (a * b) hab2 hab1 hnab
    rw [Units.val_mul, Matrix.det_mul, d1, d2] at d3
    have : (2 : F) = 0 := by linear_combination d3
    exact h2 this

theorem exists_inverting_element {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Type*} [Group W]
    [Finite W] (hcomm : ∀ a b : W, a * b = b * a) (hpow : ∀ a : W, a ^ p = 1)
    (hcard : Nat.card W ≤ p ^ 2) {K : Type*} [Group K] (θ : K →* MulAut W) {a b : K}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) (ha1 : θ a ≠ 1) (hb1 : θ b ≠ 1)
    (hab1 : θ (a * b) ≠ 1) :
    (∀ w : W, θ a w = w⁻¹) ∨ (∀ w : W, θ b w = w⁻¹) ∨ (∀ w : W, θ (a * b) w = w⁻¹) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hW : IsPGroup p W := fun w => ⟨1, by rw [pow_one]; exact hpow w⟩
  obtain ⟨d, hd⟩ := (IsPGroup.iff_card).1 hW
  have hd2 : d ≤ 2 := by
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right hp1).1 hcard
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hd
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    have h3 := (Fact.out : p.Prime).two_le
    omega
  set ε := CFSG.SectionRank.Ccomm.elemAutEquivGL e with hε
  have key : ∀ x : K, (ε (θ x) = -1) → ∀ w : W, θ x w = w⁻¹ := fun x hx =>
    (CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e (θ x)).1 hx
  have hsq : ∀ x : K, x ^ 2 = 1 → ε (θ x) ^ 2 = 1 := fun x hx => by
    rw [← map_pow, ← map_pow, hx, map_one, map_one]
  have hne : ∀ x : K, θ x ≠ 1 → ε (θ x) ≠ 1 := fun x hx h => hx (by
    have := ε.injective (h.trans (map_one ε).symm)
    exact this)
  have hcomm' : ε (θ a) * ε (θ b) = ε (θ b) * ε (θ a) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hab]
  have hab2 : (a * b) ^ 2 = 1 := by
    rw [pow_two, mul_assoc, ← mul_assoc b, ← hab, mul_assoc, ← mul_assoc a, ← pow_two, ha,
      one_mul, ← pow_two, hb]
  have hmul : ε (θ (a * b)) = ε (θ a) * ε (θ b) := by rw [map_mul, map_mul]
  have hk := neg_one_of_klein h2 hd2 (hsq a ha) (hsq b hb) hcomm' (hne a ha1) (hne b hb1)
    (by rw [← hmul]; exact hne _ hab1)
  rcases hk with h | h | h
  · exact Or.inl (key a h)
  · exact Or.inr (Or.inl (key b h))
  · exact Or.inr (Or.inr (key (a * b) (by rw [hmul]; exact h)))

end A1c

end CFSG.Quasithin

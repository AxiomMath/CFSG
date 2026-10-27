module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

abbrev F3 := ZMod 3
abbrev Mat2 := Matrix (Fin 2) (Fin 2) F3

def T8 : List Mat2 :=
  [!![1, 1; 0, 1], !![1, 2; 0, 1], !![1, 0; 1, 1], !![1, 0; 2, 1],
    !![2, 1; 2, 0], !![2, 2; 1, 0], !![0, 1; 2, 2], !![0, 2; 1, 2]]

def Tall : List Mat2 := 1 :: T8

set_option maxRecDepth 100000 in
theorem T8_props : ∀ u ∈ T8, u ^ 3 = 1 ∧ u ≠ 1 ∧ u 0 0 * u 1 1 - u 0 1 * u 1 0 ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem order3_mem : ∀ M : Mat2, M ^ 3 = 1 → M ≠ 1 → M ∈ T8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fixed_exists : ∀ M ∈ T8, ∃ v : Fin 2 → F3, v ≠ 0 ∧ M *ᵥ v = v := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem two_fixed : ∀ c ∈ T8, ∀ t ∈ T8, ∀ w : Fin 2 → F3, w ≠ 0 → c *ᵥ w = w → t *ᵥ w = w →
    c = t ∨ c * t = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sl_decomp : ∀ M : Mat2, M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 →
    ∃ a ∈ Tall, ∃ b ∈ Tall, ∃ c ∈ Tall, M = a * b * c := by
  decide +kernel

theorem key_mem (B : Subgroup (GL (Fin 2) F3))
    (htrans : ∀ v w : Fin 2 → F3, v ≠ 0 → w ≠ 0 → ∃ b ∈ B, (b : Mat2) *ᵥ v = w)
    (h3 : ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1) (x : GL (Fin 2) F3)
    (hx3 : (x : Mat2) ^ 3 = 1) (hx1 : (x : Mat2) ≠ 1) : x ∈ B := by
  obtain ⟨b, hbB, hb1, hb3⟩ := h3
  have hbM3 : (b : Mat2) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hb3, Units.val_one]
  have hbM1 : (b : Mat2) ≠ 1 := fun h => hb1 (Units.ext (h.trans Units.val_one.symm))
  obtain ⟨v, hv0, hvfix⟩ := fixed_exists _ (order3_mem _ hbM3 hbM1)
  obtain ⟨w, hw0, hwfix⟩ := fixed_exists _ (order3_mem _ hx3 hx1)
  obtain ⟨b', hb'B, hb'v⟩ := htrans v w hv0 hw0
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin 2) F3, c = b' * b * b'⁻¹ := ⟨_, rfl⟩
  have hcB : c ∈ B := by
    rw [hc]
    exact B.mul_mem (B.mul_mem hb'B hbB) (B.inv_mem hb'B)
  have hcb : c * b' = b' * b := by
    rw [hc]
    exact inv_mul_cancel_right (b' * b) b'
  have hc1 : c ≠ 1 := by
    intro h1
    apply hb1
    have h2 : b' * b * b'⁻¹ = 1 := by rw [← hc]; exact h1
    have h4 : b' * b = b' * 1 := by
      rw [mul_one]
      exact mul_inv_eq_one.mp h2
    exact mul_left_cancel h4
  have hcc3 : c ^ 3 = 1 := by
    rw [hc, conj_pow, hb3, mul_one, mul_inv_cancel]
  have hcM3 : (c : Mat2) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hcc3, Units.val_one]
  have hcM1 : (c : Mat2) ≠ 1 := fun h => hc1 (Units.ext (h.trans Units.val_one.symm))
  have hcb' : (c : Mat2) * (b' : Mat2) = (b' : Mat2) * (b : Mat2) := by
    rw [← Units.val_mul, ← Units.val_mul, hcb]
  have hcfix : (c : Mat2) *ᵥ w = w := by
    calc (c : Mat2) *ᵥ w = (c : Mat2) *ᵥ ((b' : Mat2) *ᵥ v) := by rw [hb'v]
      _ = ((c : Mat2) * (b' : Mat2)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = ((b' : Mat2) * (b : Mat2)) *ᵥ v := by rw [hcb']
      _ = (b' : Mat2) *ᵥ ((b : Mat2) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = (b' : Mat2) *ᵥ v := by rw [hvfix]
      _ = w := hb'v
  rcases two_fixed _ (order3_mem _ hcM3 hcM1) _ (order3_mem _ hx3 hx1) w hw0 hcfix hwfix
    with h | h
  · have hcx : c = x := Units.ext h
    rw [← hcx]
    exact hcB
  · have hcx : c * x = 1 := Units.ext (by rw [Units.val_mul, h, Units.val_one])
    rw [eq_inv_of_mul_eq_one_right hcx]
    exact B.inv_mem hcB

theorem mem_of_T8 (B : Subgroup (GL (Fin 2) F3))
    (htrans : ∀ v w : Fin 2 → F3, v ≠ 0 → w ≠ 0 → ∃ b ∈ B, (b : Mat2) *ᵥ v = w)
    (h3 : ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1) :
    ∀ u ∈ T8, ∃ x ∈ B, (x : Mat2) = u := by
  intro u hu
  obtain ⟨hu3, hu1, hdet⟩ := T8_props u hu
  have hdet' : Matrix.det u ≠ 0 := by
    rw [Matrix.det_fin_two]
    exact hdet
  obtain ⟨x, hxu⟩ : ∃ x : GL (Fin 2) F3, (x : Mat2) = u :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero u hdet', rfl⟩
  exact ⟨x, key_mem B htrans h3 x (by rw [hxu]; exact hu3) (by rw [hxu]; exact hu1), hxu⟩

theorem sl_le_of_transitive (B : Subgroup (GL (Fin 2) F3))
    (htrans : ∀ v w : Fin 2 → F3, v ≠ 0 → w ≠ 0 → ∃ b ∈ B, (b : Mat2) *ᵥ v = w)
    (h3 : ∃ b ∈ B, b ≠ 1 ∧ b ^ 3 = 1) :
    ∀ g : GL (Fin 2) F3, (g : Mat2).det = 1 → g ∈ B := by
  intro g hg
  rw [Matrix.det_fin_two] at hg
  obtain ⟨a, ha, b, hb, c, hc, hgabc⟩ := sl_decomp (g : Mat2) hg
  have hmem : ∀ u ∈ Tall, ∃ x ∈ B, (x : Mat2) = u := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu8
    · exact ⟨1, B.one_mem, Units.val_one⟩
    · exact mem_of_T8 B htrans h3 u hu8
  obtain ⟨x, hxB, hx⟩ := hmem a ha
  obtain ⟨y, hyB, hy⟩ := hmem b hb
  obtain ⟨z, hzB, hz⟩ := hmem c hc
  have hg' : g = x * y * z := Units.ext (by rw [Units.val_mul, Units.val_mul, hx, hy, hz, hgabc])
  rw [hg']
  exact B.mul_mem (B.mul_mem hxB hyB) hzB

lemma smul_mem_F3 (T : AddSubgroup Mat2) {x : Mat2} (hx : x ∈ T) (c : F3) : c • x ∈ T := by
  have h : c • x = (ZMod.val c : ℕ) • x := by
    rw [← Nat.cast_smul_eq_nsmul F3, ZMod.natCast_zmod_val]
  rw [h]
  exact T.nsmul_mem hx _

lemma mem_of_smul_mem_F3 (T : AddSubgroup Mat2) {x : Mat2} {c : F3} (hc : c ≠ 0)
    (hx : c • x ∈ T) : x ∈ T := by
  have h := smul_mem_F3 T hx c⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

abbrev Iq : Mat2 := !![0, 1; -1, 0]
abbrev Jq : Mat2 := !![1, 1; 1, -1]
abbrev Kq : Mat2 := !![1, -1; -1, -1]
abbrev Gq : Mat2 := !![0, -1; 1, 1]

lemma det_Iq : Iq.det = 1 := by rw [Matrix.det_fin_two_of]; decide
lemma det_Jq : Jq.det = 1 := by rw [Matrix.det_fin_two_of]; decide
lemma det_Kq : Kq.det = 1 := by rw [Matrix.det_fin_two_of]; decide
lemma det_Gq : Gq.det = 1 := by rw [Matrix.det_fin_two_of]; decide

lemma adj_Iq : Iq.adjugate = !![0, -1; 1, 0] := by rw [Matrix.adjugate_fin_two_of]; decide
lemma adj_Jq : Jq.adjugate = !![-1, -1; -1, 1] := by rw [Matrix.adjugate_fin_two_of]; decide
lemma adj_Kq : Kq.adjugate = !![-1, 1; 1, 1] := by rw [Matrix.adjugate_fin_two_of]; decide
lemma adj_Gq : Gq.adjugate = !![1, 1; -1, 0] := by rw [Matrix.adjugate_fin_two_of]; decide

lemma conj_Iq (μ : Mat2) : Iq * μ * Iq.adjugate = !![μ 1 1, -μ 1 0; -μ 0 1, μ 0 0] := by
  rw [adj_Iq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma conj_Jq (μ : Mat2) :
    Jq * μ * Jq.adjugate = !![-(μ 0 0 + μ 0 1 + μ 1 0 + μ 1 1), μ 0 1 + μ 1 1 - μ 0 0 - μ 1 0;
      μ 1 0 + μ 1 1 - μ 0 0 - μ 0 1, μ 0 1 + μ 1 0 - μ 0 0 - μ 1 1] := by
  rw [adj_Jq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma conj_Kq (μ : Mat2) :
    Kq * μ * Kq.adjugate = !![μ 0 1 + μ 1 0 - μ 0 0 - μ 1 1, μ 0 0 + μ 0 1 - μ 1 0 - μ 1 1;
      μ 0 0 + μ 1 0 - μ 0 1 - μ 1 1, -(μ 0 0 + μ 0 1 + μ 1 0 + μ 1 1)] := by
  rw [adj_Kq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma conj_Gq (μ : Mat2) :
    Gq * μ * Gq.adjugate =
      !![μ 1 1 - μ 1 0, -μ 1 0; μ 0 0 + μ 1 0 - μ 0 1 - μ 1 1, μ 0 0 + μ 1 0] := by
  rw [adj_Gq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma Gq_Iq : Gq * Iq * Gq.adjugate = Jq := by rw [conj_Gq]; decide
lemma Gq_Jq : Gq * Jq * Gq.adjugate = Kq := by rw [conj_Gq]; decide
lemma Gq_Kq : Gq * Kq * Gq.adjugate = Iq := by rw [conj_Gq]; decide

lemma proj_I (μ : Mat2) :
    (μ 1 0 - μ 0 1) • Iq =
      μ + Iq * μ * Iq.adjugate - Jq * μ * Jq.adjugate - Kq * μ * Kq.adjugate := by
  rw [conj_Iq, conj_Jq, conj_Kq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma proj_J (μ : Mat2) :
    (μ 0 0 - μ 1 1 + μ 0 1 + μ 1 0) • Jq =
      μ - Iq * μ * Iq.adjugate + Jq * μ * Jq.adjugate - Kq * μ * Kq.adjugate := by
  rw [conj_Iq, conj_Jq, conj_Kq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma proj_K (μ : Mat2) :
    (μ 0 0 - μ 1 1 - μ 0 1 - μ 1 0) • Kq =
      μ - Iq * μ * Iq.adjugate - Jq * μ * Jq.adjugate + Kq * μ * Kq.adjugate := by
  rw [conj_Iq, conj_Jq, conj_Kq]
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma decomp (μ : Mat2) :
    μ = (-(μ 0 0 + μ 1 1)) • (1 : Mat2) + (μ 1 0 - μ 0 1) • Iq
      + (μ 0 0 - μ 1 1 + μ 0 1 + μ 1 0) • Jq + (μ 0 0 - μ 1 1 - μ 0 1 - μ 1 0) • Kq := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, μ = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two μ⟩
  revert p q r s
  decide

lemma nonscalar (ν : Mat2) (hν : ∀ c : F3, ν ≠ c • (1 : Mat2)) :
    ν 1 0 - ν 0 1 ≠ 0 ∨ ν 0 0 - ν 1 1 + ν 0 1 + ν 1 0 ≠ 0 ∨
      ν 0 0 - ν 1 1 - ν 0 1 - ν 1 0 ≠ 0 := by
  by_contra hcon
  simp only [not_or, ne_eq, not_not] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have key : ∀ p q r s : F3, r - q = 0 → p - s + q + r = 0 → p - s - q - r = 0 →
      q = 0 ∧ r = 0 ∧ p = s := by decide
  obtain ⟨e01, e10, e00⟩ := key (ν 0 0) (ν 0 1) (ν 1 0) (ν 1 1) h1 h2 h3
  apply hν (ν 0 0)
  ext a b
  fin_cases a <;> fin_cases b <;> simp [e00, e01, e10]

theorem eq_top_of_conj_nonscalar (S : AddSubgroup Mat2)
    (hconj : ∀ g : Mat2, g.det = 1 → ∀ μ ∈ S, g * μ * g.adjugate ∈ S)
    (h1 : (1 : Mat2) ∈ S) (ν : Mat2) (hν : ∀ c : F3, ν ≠ c • (1 : Mat2)) (hνS : ν ∈ S) :
    S = ⊤ := by
  have hI : ∀ μ ∈ S, Iq * μ * Iq.adjugate ∈ S := hconj Iq det_Iq
  have hJ : ∀ μ ∈ S, Jq * μ * Jq.adjugate ∈ S := hconj Jq det_Jq
  have hK : ∀ μ ∈ S, Kq * μ * Kq.adjugate ∈ S := hconj Kq det_Kq
  have hG : ∀ μ ∈ S, Gq * μ * Gq.adjugate ∈ S := hconj Gq det_Gq
  have hPI : (ν 1 0 - ν 0 1) • Iq ∈ S := by
    rw [proj_I ν]
    exact S.sub_mem (S.sub_mem (S.add_mem hνS (hI ν hνS)) (hJ ν hνS)) (hK ν hνS)
  have hPJ : (ν 0 0 - ν 1 1 + ν 0 1 + ν 1 0) • Jq ∈ S := by
    rw [proj_J ν]
    exact S.sub_mem (S.add_mem (S.sub_mem hνS (hI ν hνS)) (hJ ν hνS)) (hK ν hνS)
  have hPK : (ν 0 0 - ν 1 1 - ν 0 1 - ν 1 0) • Kq ∈ S := by
    rw [proj_K ν]
    exact S.add_mem (S.sub_mem (S.sub_mem hνS (hI ν hνS)) (hJ ν hνS)) (hK ν hνS)
  have hany : Iq ∈ S ∨ Jq ∈ S ∨ Kq ∈ S := by
    rcases nonscalar ν hν with h | h | h
    · exact Or.inl (mem_of_smul_mem_F3 S h hPI)
    · exact Or.inr (Or.inl (mem_of_smul_mem_F3 S h hPJ))
    · exact Or.inr (Or.inr (mem_of_smul_mem_F3 S h hPK))
  have c1 : Iq ∈ S → Jq ∈ S := fun h => by
    have := hG Iq h
    rwa [Gq_Iq] at this
  have c2 : Jq ∈ S → Kq ∈ S := fun h => by
    have := hG Jq h
    rwa [Gq_Jq] at this
  have c3 : Kq ∈ S → Iq ∈ S := fun h => by
    have := hG Kq h
    rwa [Gq_Kq] at this
  have hall : Iq ∈ S ∧ Jq ∈ S ∧ Kq ∈ S := by
    rcases hany with h | h | h
    · exact ⟨h, c1 h, c2 (c1 h)⟩
    · exact ⟨c3 (c2 h), h, c2 h⟩
    · exact ⟨c3 h, c1 (c3 h), h⟩
  obtain ⟨hi, hj, hk⟩ := hall
  refine eq_top_iff.mpr (fun μ _ => ?_)
  rw [decomp μ]
  exact S.add_mem (S.add_mem (S.add_mem (smul_mem_F3 S h1 _) (smul_mem_F3 S hi _))
    (smul_mem_F3 S hj _)) (smul_mem_F3 S hk _)

end CFSG.RankThree.PartTwo.Sec21.Hering2119S

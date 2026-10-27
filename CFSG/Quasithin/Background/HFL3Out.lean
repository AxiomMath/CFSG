module

public import CFSG.Quasithin.Background.HFL3Lift

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem uni3_mul_01 {x y : SpecialLinearGroup (Fin 3) K} (hx : x ∈ unitriangular 3 K)
    (hy : y ∈ unitriangular 3 K) :
    ((x * y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 =
      (y : Matrix (Fin 3) (Fin 3) K) 0 1 + (x : Matrix (Fin 3) (Fin 3) K) 0 1 := by
  obtain ⟨x00, -, -, -, -, -⟩ := uni3_entries hx
  obtain ⟨-, y11, -, -, -, y21⟩ := uni3_entries hy
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, x00, y11, y21]
  ring

omit [Finite K] [CharP K 2] in
theorem uni3_mul_12 {x y : SpecialLinearGroup (Fin 3) K} (hx : x ∈ unitriangular 3 K)
    (hy : y ∈ unitriangular 3 K) :
    ((x * y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
      (y : Matrix (Fin 3) (Fin 3) K) 1 2 + (x : Matrix (Fin 3) (Fin 3) K) 1 2 := by
  obtain ⟨-, x11, -, x10, -, -⟩ := uni3_entries hx
  obtain ⟨-, -, y22, -, -, -⟩ := uni3_entries hy
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, x11, y22, x10]
  ring

omit [Finite K] in
theorem add_eq_smul_add_of_eq {a b c d z : K} (h : a + z * c = b + z * d) :
    a + b = z * (c + d) := by
  linear_combination h + (b - z * c) * CharTwo.two_eq_zero (R := K)

theorem eq_zero_of_form {β c₀ c₁ c₂ c₃ z a b : K} (hβ : β ≠ 0) (hz : bar n z ≠ z)
    (h1 : β * a = c₀ * bar n a + c₁ * bar n b) (h2 : β * b = c₂ * bar n a + c₃ * bar n b)
    (h3 : β * (z * a) = c₀ * bar n (z * a) + c₁ * bar n (z * b))
    (h4 : β * (z * b) = c₂ * bar n (z * a) + c₃ * bar n (z * b)) : a = 0 ∧ b = 0 := by
  rw [map_mul, map_mul] at h3 h4
  have e1 : (z - bar n z) * β * a = 0 := by linear_combination h3 - bar n z * h1
  have e2 : (z - bar n z) * β * b = 0 := by linear_combination h4 - bar n z * h2
  have hz' : (z - bar n z) * β ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hz)) hβ
  exact ⟨(mul_eq_zero.mp e1).resolve_left hz', (mul_eq_zero.mp e2).resolve_left hz'⟩

theorem eq_zero_of_form' {β c₀ c₁ c₂ c₃ z a b : K} (hβ : β ≠ 0) (hz : bar n z ≠ z)
    (h1 : β * bar n a = c₀ * a + c₁ * b) (h2 : β * bar n b = c₂ * a + c₃ * b)
    (h3 : β * bar n (z * a) = c₀ * (z * a) + c₁ * (z * b))
    (h4 : β * bar n (z * b) = c₂ * (z * a) + c₃ * (z * b)) : a = 0 ∧ b = 0 := by
  rw [map_mul] at h3 h4
  have e1 : (bar n z - z) * β * bar n a = 0 := by linear_combination h3 - z * h1
  have e2 : (bar n z - z) * β * bar n b = 0 := by linear_combination h4 - z * h2
  have hz' : (bar n z - z) * β ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hz) hβ
  exact ⟨(map_eq_zero_iff _ (bar n).injective).1 ((mul_eq_zero.mp e1).resolve_left hz'),
    (map_eq_zero_iff _ (bar n).injective).1 ((mul_eq_zero.mp e2).resolve_left hz')⟩

theorem card_mul_self_le_of_pair {G : Type*} [Group G] {P : Subgroup G} (a b : G → K) (z : K)
    (hs : ∀ x ∈ P, x * x = 1)
    (hadd : ∀ x ∈ P, ∀ y ∈ P, a (x * y) = a y + a x ∧ b (x * y) = b y + b x)
    (h1 : ∀ x ∈ P, a x = 0 → b x = 0 → x = 1)
    (hform : ∀ x ∈ P, ∀ y ∈ P, a x = z * a y → b x = z * b y → a y = 0 ∧ b y = 0) :
    Nat.card P * Nat.card P ≤ Nat.card K * Nat.card K := by
  let F : ↥P × ↥P → K × K := fun q =>
    (a q.1 + z * a q.2, b q.1 + z * b q.2)
  have hF : Function.Injective F := by
    rintro ⟨p, p'⟩ ⟨q, q'⟩ h
    have ha := add_eq_smul_add_of_eq (congrArg Prod.fst h)
    have hb := add_eq_smul_add_of_eq (congrArg Prod.snd h)
    have hr := P.mul_mem p.2 q.2
    have hs' := P.mul_mem p'.2 q'.2
    obtain ⟨har, hbr⟩ := hadd _ p.2 _ q.2
    obtain ⟨has, hbs⟩ := hadd _ p'.2 _ q'.2
    have e1 : a (p.1 * q.1) = z * a (p'.1 * q'.1) := by rw [har, has, add_comm, ha, add_comm]
    have e2 : b (p.1 * q.1) = z * b (p'.1 * q'.1) := by rw [hbr, hbs, add_comm, hb, add_comm]
    obtain ⟨hs0, hs1⟩ := hform _ hr _ hs' e1 e2
    have hsq : p'.1 * q'.1 = 1 := h1 _ hs' hs0 hs1
    have hrq : p.1 * q.1 = 1 := h1 _ hr (by rw [e1, hs0, mul_zero]) (by rw [e2, hs1, mul_zero])
    have key : ∀ x ∈ P, ∀ y ∈ P, x * y = 1 → x = y := fun x _ y hy hxy => by
      have := congrArg (· * y) hxy
      simp only [mul_assoc, hs y hy, mul_one, one_mul] at this
      exact this
    exact Prod.ext (Subtype.ext (key _ p.2 _ q.2 hrq)) (Subtype.ext (key _ p'.2 _ q'.2 hsq))
  have hle := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_prod] at hle

omit [Finite K] [CharP K 2] in
theorem uni3_mul_apply {p : SpecialLinearGroup (Fin 3) K} (hp : p ∈ unitriangular 3 K)
    (B : Matrix (Fin 3) (Fin 3) K) (j : Fin 3) :
    ((p : Matrix (Fin 3) (Fin 3) K) * B) 0 j =
        B 0 j + (p : Matrix (Fin 3) (Fin 3) K) 0 1 * B 1 j +
          (p : Matrix (Fin 3) (Fin 3) K) 0 2 * B 2 j ∧
      ((p : Matrix (Fin 3) (Fin 3) K) * B) 1 j =
        B 1 j + (p : Matrix (Fin 3) (Fin 3) K) 1 2 * B 2 j ∧
      ((p : Matrix (Fin 3) (Fin 3) K) * B) 2 j = B 2 j := by
  obtain ⟨p00, p11, p22, p10, p20, p21⟩ := uni3_entries hp
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, p00, p11, p22, p10, p20, p21, one_mul,
      zero_mul, zero_add, add_zero]

theorem mul_conjM_uni3_apply {p : SpecialLinearGroup (Fin 3) K} (hp : p ∈ unitriangular 3 K)
    (B : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (B * conjM n (p : Matrix (Fin 3) (Fin 3) K)) i 0 = B i 0 ∧
      (B * conjM n (p : Matrix (Fin 3) (Fin 3) K)) i 1 =
        B i 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 1) + B i 1 ∧
      (B * conjM n (p : Matrix (Fin 3) (Fin 3) K)) i 2 =
        B i 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 2) +
          B i 1 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 1 2) + B i 2 := by
  obtain ⟨p00, p11, p22, p10, p20, p21⟩ := uni3_entries hp
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.map_apply, p00, p11, p22, p10,
      p20, p21, map_one, map_zero, mul_one, mul_zero, add_zero]

theorem card_le_of_twisted_comm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hs : ∀ x ∈ P, x * x = 1) {B : GL (Fin 3) K}
    (hB : ∀ p ∈ P, (p : Matrix (Fin 3) (Fin 3) K) * B =
      B * conjM n (p : Matrix (Fin 3) (Fin 3) K)) :
    Nat.card P ≤ Nat.card K := by
  classical
  obtain ⟨z, hz⟩ := exists_bar_ne hn hK
  by_cases hP1 : ∀ p ∈ P, p = 1
  · rw [(Subgroup.eq_bot_iff_forall P).2 hP1, Subgroup.card_bot]
    exact Nat.card_pos
  push Not at hP1
  obtain ⟨p₀, hp₀, hp₀1⟩ := hP1
  have hdet : (B : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (B.isUnit.map
    (Matrix.detMonoidHom (n := Fin 3) (R := K))).ne_zero
  have hent : ∀ p ∈ P, ∀ i j : Fin 3, ((p : Matrix (Fin 3) (Fin 3) K) * B) i j =
      ((B : Matrix (Fin 3) (Fin 3) K) * conjM n (p : Matrix (Fin 3) (Fin 3) K)) i j :=
    fun p hp i j => by rw [hB p hp]
  have hone : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 →
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 → (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 →
        x = 1 := fun x hx h1 h2 h3 =>
    uni3_ext (hPU hx) (one_mem _) (by simp [h1]) (by simp [h2]) (by simp [h3])
  apply Nat.mul_self_le_mul_self_iff.1
  rcases uni3_cases hPU hc hs with h12 | h01
  ·
    have hrel : ∀ p ∈ P, (B 1 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 1) = 0 ∧
        B 1 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 2) = 0 ∧
        B 2 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 1) = 0 ∧
        B 2 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 2) = 0) ∧
        B 0 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 1) =
          B 1 1 * (p : Matrix (Fin 3) (Fin 3) K) 0 1 + B 2 1 * (p : Matrix (Fin 3) (Fin 3) K) 0 2 ∧
        B 0 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 2) =
          B 1 2 * (p : Matrix (Fin 3) (Fin 3) K) 0 1 +
            B 2 2 * (p : Matrix (Fin 3) (Fin 3) K) 0 2 := by
      intro p hp
      have hp12 := h12 p hp
      have l : ∀ j : Fin 3, _ := fun j => uni3_mul_apply (hPU hp) (B : Matrix (Fin 3) (Fin 3) K) j
      have r : ∀ i : Fin 3, _ := fun i => mul_conjM_uni3_apply (n := n) (hPU hp)
        (B : Matrix (Fin 3) (Fin 3) K) i
      have e11 := hent p hp 1 1
      have e12 := hent p hp 1 2
      have e21 := hent p hp 2 1
      have e22 := hent p hp 2 2
      have e01 := hent p hp 0 1
      have e02 := hent p hp 0 2
      rw [(l 1).2.1, (r 1).2.1, hp12] at e11
      rw [(l 2).2.1, (r 1).2.2, hp12, map_zero] at e12
      rw [(l 1).2.2, (r 2).2.1] at e21
      rw [(l 2).2.2, (r 2).2.2, hp12, map_zero] at e22
      rw [(l 1).1, (r 0).2.1] at e01
      rw [(l 2).1, (r 0).2.2, hp12, map_zero] at e02
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · linear_combination -e11
      · linear_combination -e12
      · linear_combination -e21
      · linear_combination -e22
      · linear_combination -e01
      · linear_combination -e02
    have hp₀ab : (p₀ : Matrix (Fin 3) (Fin 3) K) 0 1 ≠ 0 ∨
        (p₀ : Matrix (Fin 3) (Fin 3) K) 0 2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hp₀1 (hone p₀ hp₀ h.1 h.2 (h12 p₀ hp₀))
    obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := hrel p₀ hp₀
    have hB10 : B 1 0 = 0 := by
      rcases hp₀ab with h | h
      · exact (mul_eq_zero.mp r1).resolve_right ((map_ne_zero (bar n)).mpr h)
      · exact (mul_eq_zero.mp r2).resolve_right ((map_ne_zero (bar n)).mpr h)
    have hB20 : B 2 0 = 0 := by
      rcases hp₀ab with h | h
      · exact (mul_eq_zero.mp r3).resolve_right ((map_ne_zero (bar n)).mpr h)
      · exact (mul_eq_zero.mp r4).resolve_right ((map_ne_zero (bar n)).mpr h)
    have hα : B 0 0 ≠ 0 := by
      intro h0
      apply hdet
      rw [Matrix.det_fin_three, hB10, hB20, h0]
      ring
    refine card_mul_self_le_of_pair (fun x => (x : Matrix (Fin 3) (Fin 3) K) 0 1)
      (fun x => (x : Matrix (Fin 3) (Fin 3) K) 0 2) z hs ?_ ?_ ?_
    · intro x hx y hy
      refine ⟨uni3_mul_01 (hPU hx) (hPU hy), ?_⟩
      show ((x * y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = _
      rw [uni3_mul_02 (hPU hx) (hPU hy), h12 y hy]
      ring
    · exact fun x hx h1 h2 => hone x hx h1 h2 (h12 x hx)
    · intro x hx y hy hxa hxb
      obtain ⟨-, hx1, hx2⟩ := hrel x hx
      obtain ⟨-, hy1, hy2⟩ := hrel y hy
      rw [hxa, hxb] at hx1 hx2
      exact eq_zero_of_form' hα hz hy1 hy2 hx1 hx2
  ·
    have hrel : ∀ p ∈ P, ((p : Matrix (Fin 3) (Fin 3) K) 0 2 * B 2 0 = 0 ∧
        (p : Matrix (Fin 3) (Fin 3) K) 0 2 * B 2 1 = 0 ∧
        (p : Matrix (Fin 3) (Fin 3) K) 1 2 * B 2 0 = 0 ∧
        (p : Matrix (Fin 3) (Fin 3) K) 1 2 * B 2 1 = 0) ∧
        B 2 2 * (p : Matrix (Fin 3) (Fin 3) K) 0 2 =
          B 0 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 2) +
            B 0 1 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 1 2) ∧
        B 2 2 * (p : Matrix (Fin 3) (Fin 3) K) 1 2 =
          B 1 0 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 0 2) +
            B 1 1 * bar n ((p : Matrix (Fin 3) (Fin 3) K) 1 2) := by
      intro p hp
      have hp01 := h01 p hp
      have l : ∀ j : Fin 3, _ := fun j => uni3_mul_apply (hPU hp) (B : Matrix (Fin 3) (Fin 3) K) j
      have r : ∀ i : Fin 3, _ := fun i => mul_conjM_uni3_apply (n := n) (hPU hp)
        (B : Matrix (Fin 3) (Fin 3) K) i
      have e00 := hent p hp 0 0
      have e01 := hent p hp 0 1
      have e10 := hent p hp 1 0
      have e11 := hent p hp 1 1
      have e02 := hent p hp 0 2
      have e12 := hent p hp 1 2
      rw [(l 0).1, (r 0).1, hp01] at e00
      rw [(l 1).1, (r 0).2.1, hp01, map_zero] at e01
      rw [(l 0).2.1, (r 1).1] at e10
      rw [(l 1).2.1, (r 1).2.1, hp01, map_zero] at e11
      rw [(l 2).1, (r 0).2.2, hp01] at e02
      rw [(l 2).2.1, (r 1).2.2] at e12
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · linear_combination e00
      · linear_combination e01
      · linear_combination e10
      · linear_combination e11
      · linear_combination e02
      · linear_combination e12
    have hp₀ab : (p₀ : Matrix (Fin 3) (Fin 3) K) 0 2 ≠ 0 ∨
        (p₀ : Matrix (Fin 3) (Fin 3) K) 1 2 ≠ 0 := by
      by_contra h
      push Not at h
      exact hp₀1 (hone p₀ hp₀ (h01 p₀ hp₀) h.1 h.2)
    obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := hrel p₀ hp₀
    have hB20 : B 2 0 = 0 := by
      rcases hp₀ab with h | h
      · exact (mul_eq_zero.mp r1).resolve_left h
      · exact (mul_eq_zero.mp r3).resolve_left h
    have hB21 : B 2 1 = 0 := by
      rcases hp₀ab with h | h
      · exact (mul_eq_zero.mp r2).resolve_left h
      · exact (mul_eq_zero.mp r4).resolve_left h
    have hβ : B 2 2 ≠ 0 := by
      intro h0
      apply hdet
      rw [Matrix.det_fin_three, hB20, hB21, h0]
      ring
    refine card_mul_self_le_of_pair (fun x => (x : Matrix (Fin 3) (Fin 3) K) 0 2)
      (fun x => (x : Matrix (Fin 3) (Fin 3) K) 1 2) z hs ?_ ?_ ?_
    · intro x hx y hy
      refine ⟨?_, uni3_mul_12 (hPU hx) (hPU hy)⟩
      show ((x * y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = _
      rw [uni3_mul_02 (hPU hx) (hPU hy), h01 x hx]
      ring
    · exact fun x hx h1 h2 => hone x hx (h01 x hx) h1 h2
    · intro x hx y hy hxa hxb
      obtain ⟨-, hx1, hx2⟩ := hrel x hx
      obtain ⟨-, hy1, hy2⟩ := hrel y hy
      rw [hxa, hxb] at hx1 hx2
      exact eq_zero_of_form hβ hz hy1 hy2 hx1 hx2

omit [Finite K] in
theorem trace_uni3 {p : SpecialLinearGroup (Fin 3) K} (hp : p ∈ unitriangular 3 K) :
    Matrix.trace (p : Matrix (Fin 3) (Fin 3) K) = 1 := by
  obtain ⟨p00, p11, p22, -, -, -⟩ := uni3_entries hp
  rw [Matrix.trace_fin_three, p00, p11, p22, CharTwo.add_self_eq_zero, zero_add]

theorem trace_conjM_uni3 {p : SpecialLinearGroup (Fin 3) K} (hp : p ∈ unitriangular 3 K) :
    Matrix.trace (conjM n (p : Matrix (Fin 3) (Fin 3) K)) = 1 := by
  obtain ⟨p00, p11, p22, -, -, -⟩ := uni3_entries hp
  rw [Matrix.trace_fin_three]
  simp only [conjM, Matrix.map_apply, p00, p11, p22, map_one]
  rw [CharTwo.add_self_eq_zero, zero_add]

theorem card_le_of_not_le_linImg (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ norm hK) (hAe : IsElemAbelian2 A)
    {a : MulAut (HMod n K)} (ha : a ∈ A) (haL : a ∉ linImg hK) :
    Nat.card A ≤ 2 * Nat.card K := by
  classical
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hinv : ∀ b ∈ A, b * b = 1 := fun b hb => by rw [← sq]; exact hAe.2 b hb
  have hout : ∀ b ∈ A, b ∉ linImg hK → ∃ B : GL (Fin 3) K, b = rhoT hK B * fldAut (bar n) := by
    intro b hb hbL
    obtain ⟨B, h | h⟩ := exists_of_involution hn hK (hA hb) (hinv b hb)
    · exact absurd ⟨B, h.symm⟩ hbL
    · exact ⟨B, h⟩
  have hbar2 : (bar n : K ≃+* K) * bar n = 1 := by
    ext x
    exact bar_bar hK x
  have hprod : ∀ b ∈ A, b ∉ linImg hK → a * b ∈ linImg hK := by
    intro b hb hbL
    obtain ⟨B, hB⟩ := hout a ha haL
    obtain ⟨B', hB'⟩ := hout b hb hbL
    refine ⟨B * mapGL (bar n) B', ?_⟩
    rw [hB, hB', map_mul, mul_assoc (rhoT hK B), ← mul_assoc (fldAut (bar n)),
      fldAut_mul_rhoT hK, mul_assoc (rhoT hK (mapGL (bar n) B')), ← fldAut_mul, hbar2,
      fldAut_one, mul_one]
  set A₀ := A ⊓ linImg hK with hA₀
  have hcard : Nat.card A ≤ 2 * Nat.card A₀ := by
    let f : ↥A → Bool × ↥A₀ := fun b =>
      if hb : (b : MulAut (HMod n K)) ∈ linImg hK then (true, ⟨b, b.2, hb⟩)
      else (false, ⟨a * b, A.mul_mem ha b.2, hprod b b.2 hb⟩)
    have hf : Function.Injective f := by
      intro b c h
      simp only [f] at h
      split_ifs at h with hb hc hc
      · exact Subtype.ext (congrArg (fun p => (p.2 : MulAut (HMod n K))) h)
      · exact absurd (congrArg Prod.fst h) (by simp)
      · exact absurd (congrArg Prod.fst h) (by simp)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun p => (p.2 : MulAut (HMod n K))) h))
    have h1 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1
  have hA₀2 : IsPGroup 2 ↥A₀ := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hAe.2 x x.2.1)⟩
  obtain ⟨g, P, hPU, -, hinj, hPmap⟩ := exists_conj_uni3 hK (inf_le_right : A₀ ≤ linImg hK) hA₀2
  have hcardP : Nat.card ↥P = Nat.card ↥A₀ := by
    rw [← card_map_rho_of_inj hK hinj, hPmap]
    exact Subgroup.card_map_of_injective (MulAut.conj (rho hK g)).injective
  have hmemP : ∀ x ∈ P, ∃ a₀ ∈ A₀, rho hK x = rho hK g * a₀ * (rho hK g)⁻¹ := by
    intro x hx
    have hx' : rho hK x ∈ P.map (rho hK) := ⟨x, hx, rfl⟩
    rw [hPmap] at hx'
    obtain ⟨a₀, ha₀, he⟩ := hx'
    exact ⟨a₀, ha₀, he.symm⟩
  have hcP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a₁, ha₁, e₁⟩ := hmemP x hx
    obtain ⟨a₂, ha₂, e₂⟩ := hmemP y hy
    have h1 : rho hK (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, e₁, e₂]
      have hc : a₁ * a₂ = a₂ * a₁ := hAe.1 _ ha₁.1 _ ha₂.1
      calc rho hK g * a₁ * (rho hK g)⁻¹ * (rho hK g * a₂ * (rho hK g)⁻¹) *
            (rho hK g * a₂ * (rho hK g)⁻¹ * (rho hK g * a₁ * (rho hK g)⁻¹))⁻¹ =
            rho hK g * (a₁ * a₂) * (a₂ * a₁)⁻¹ * (rho hK g)⁻¹ := by group
        _ = 1 := by rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem (P.mul_mem hy hx)))
      h1)
  have hsP : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    obtain ⟨a₁, ha₁, e₁⟩ := hmemP x hx
    refine hinj _ (P.mul_mem hx hx) ?_
    rw [map_mul, e₁]
    calc rho hK g * a₁ * (rho hK g)⁻¹ * (rho hK g * a₁ * (rho hK g)⁻¹) =
        rho hK g * (a₁ * a₁) * (rho hK g)⁻¹ := by group
      _ = 1 := by rw [hinv a₁ ha₁.1, mul_one, mul_inv_cancel]
  obtain ⟨B, hB⟩ := hout a ha haL
  set G := SpecialLinearGroup.toGL g with hG
  set B'' := G * B * mapGL (bar n) G⁻¹ with hB''
  have ha' : rho hK g * a * (rho hK g)⁻¹ = rhoT hK B'' * fldAut (bar n) := by
    have e1 : rho hK g = rhoT hK G := rfl
    rw [hB, e1, ← map_inv]
    calc rhoT hK G * (rhoT hK B * fldAut (bar n)) * rhoT hK G⁻¹ =
        rhoT hK G * rhoT hK B * (fldAut (bar n) * rhoT hK G⁻¹) := by group
      _ = rhoT hK G * rhoT hK B * (rhoT hK (mapGL (bar n) G⁻¹) * fldAut (bar n)) := by
          rw [fldAut_mul_rhoT hK]
      _ = rhoT hK B'' * fldAut (bar n) := by
          rw [hB'', map_mul, map_mul]
          group
  have hcomm : ∀ p ∈ P, rho hK p * (rhoT hK B'' * fldAut (bar n)) =
      rhoT hK B'' * fldAut (bar n) * rho hK p := by
    intro p hp
    obtain ⟨a₁, ha₁, e₁⟩ := hmemP p hp
    rw [← ha', e₁]
    have hc : a₁ * a = a * a₁ := hAe.1 _ ha₁.1 _ ha
    calc rho hK g * a₁ * (rho hK g)⁻¹ * (rho hK g * a * (rho hK g)⁻¹) =
        rho hK g * (a₁ * a) * (rho hK g)⁻¹ := by group
      _ = rho hK g * (a * a₁) * (rho hK g)⁻¹ := by rw [hc]
      _ = rho hK g * a * (rho hK g)⁻¹ * (rho hK g * a₁ * (rho hK g)⁻¹) := by group
  have hrel : ∀ p ∈ P, (p : Matrix (Fin 3) (Fin 3) K) * B'' =
      B'' * conjM n (p : Matrix (Fin 3) (Fin 3) K) := by
    intro p hp
    have h1 := hcomm p hp
    have e1 : rho hK p = rhoT hK (SpecialLinearGroup.toGL p) := rfl
    rw [e1, mul_assoc (rhoT hK B''), fldAut_mul_rhoT hK, ← mul_assoc, ← mul_assoc, ← map_mul,
      ← map_mul] at h1
    have h2 := mul_right_cancel h1
    have h3 : rhoT hK ((B'' * mapGL (bar n) (SpecialLinearGroup.toGL p))⁻¹ *
        (SpecialLinearGroup.toGL p * B'')) = 1 := by
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h3
    have hM : (p : Matrix (Fin 3) (Fin 3) K) * B'' =
        d • ((B'' : Matrix (Fin 3) (Fin 3) K) * conjM n (p : Matrix (Fin 3) (Fin 3) K)) := by
      set X := B'' * mapGL (bar n) (SpecialLinearGroup.toGL p) with hX
      set Y := SpecialLinearGroup.toGL p * B'' with hY
      have hXY : Y = X * (X⁻¹ * Y) := by group
      have h4 := congrArg (fun C : GL (Fin 3) K => (C : Matrix (Fin 3) (Fin 3) K)) hXY
      rw [Units.val_mul X (X⁻¹ * Y), hd] at h4
      calc (p : Matrix (Fin 3) (Fin 3) K) * B'' = (Y : Matrix (Fin 3) (Fin 3) K) := rfl
        _ = (X : Matrix (Fin 3) (Fin 3) K) * (d • 1) := h4
        _ = d • ((B'' : Matrix (Fin 3) (Fin 3) K) * conjM n (p : Matrix (Fin 3) (Fin 3) K)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
            rfl
    have hd1 : d = 1 := by
      have hinv1 : ((B''⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (B'' : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hinv2 : (B'' : Matrix (Fin 3) (Fin 3) K) *
          ((B''⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hL : Matrix.trace (((B''⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((p : Matrix (Fin 3) (Fin 3) K) * (B'' : Matrix (Fin 3) (Fin 3) K))) = 1 := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc, hinv2, Matrix.mul_one, trace_uni3 (hPU hp)]
      have hR : Matrix.trace (((B''⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (d • ((B'' : Matrix (Fin 3) (Fin 3) K) * conjM n (p : Matrix (Fin 3) (Fin 3) K)))) =
            d := by
        rw [Matrix.mul_smul, Matrix.trace_smul, ← Matrix.mul_assoc, hinv1, Matrix.one_mul,
          trace_conjM_uni3 (hPU hp), smul_eq_mul, mul_one]
      have h5 : Matrix.trace (((B''⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((p : Matrix (Fin 3) (Fin 3) K) * (B'' : Matrix (Fin 3) (Fin 3) K))) =
          Matrix.trace (((B''⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (d • ((B'' : Matrix (Fin 3) (Fin 3) K) * conjM n (p : Matrix (Fin 3) (Fin 3) K)))) := by
        rw [hM]
      rw [hL, hR] at h5
      exact h5.symm
    rw [hM, hd1, one_smul]
  have hP := card_le_of_twisted_comm hn hK hPU hcP hsP hrel
  omega

theorem le_img_of_card (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ norm hK) (hAe : IsElemAbelian2 A)
    (hcard : 2 ^ (2 * n + 1) < Nat.card A) : A ≤ img hK := by
  have hlin : A ≤ linImg hK := by
    intro a ha
    by_contra haL
    have h := card_le_of_not_le_linImg hn hK hA hAe ha haL
    rw [hK, ← pow_mul, mul_comm n 2, ← pow_succ'] at h
    omega
  exact le_img_of_isPGroup hK hlin fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hAe.2 x x.2)⟩

end CFSG.Quasithin.H.L3Nine

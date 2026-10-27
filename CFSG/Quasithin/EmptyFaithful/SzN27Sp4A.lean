module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.SzN27.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem lower_zero_of_comm
    (m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33 : K)
    (s02 : m00 * m32 + m10 * m22 + m20 * m12 + m30 * m02 = 0)
    (s03 : m00 * m33 + m10 * m23 + m20 * m13 + m30 * m03 = 1)
    (b₀ c₀ : K) (hg : b₀ ≠ 0 ∨ c₀ ≠ 0)
    (g00 : b₀ * m20 + c₀ * m30 = 0) (g01 : b₀ * m21 + c₀ * m31 = 0)
    (g02 : b₀ * m00 = b₀ * m22 + c₀ * m32)
    (g03 : c₀ * m00 + b₀ * m01 = b₀ * m23 + c₀ * m33)
    (g10 : b₀ * m30 = 0) (g11 : b₀ * m31 = 0)
    (g12 : b₀ * m10 = b₀ * m32) (g13 : c₀ * m10 + b₀ * m11 = b₀ * m33)
    (g22 : b₀ * m20 = 0) (g23 : c₀ * m20 + b₀ * m21 = 0)
    (g32 : b₀ * m30 = 0) (g33 : c₀ * m30 + b₀ * m31 = 0)
    (b c b' c' : K) (hne : b ≠ b' ∨ c ≠ c')
    (v02 : b * m00 = b' * m22 + c' * m32)
    (v03 : c * m00 + b * m01 = b' * m23 + c' * m33)
    (v12 : b * m10 = b' * m32) (v13 : c * m10 + b * m11 = b' * m33)
    (v23 : c * m20 + b * m21 = 0) :
    m10 = 0 ∧ m20 = 0 ∧ m21 = 0 ∧ m30 = 0 ∧ m31 = 0 ∧ m32 = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hb₀ : b₀ = 0
  ·
    have hc₀ : c₀ ≠ 0 := by
      rcases hg with h | h
      · exact absurd hb₀ h
      · exact h
    subst hb₀
    have m30z : m30 = 0 := by
      have : c₀ * m30 = 0 := by simpa using g00
      exact (mul_eq_zero.mp this).resolve_left hc₀
    have m31z : m31 = 0 := by
      have : c₀ * m31 = 0 := by simpa using g01
      exact (mul_eq_zero.mp this).resolve_left hc₀
    have m20z : m20 = 0 := by
      have : c₀ * m20 = 0 := by simpa using g23
      exact (mul_eq_zero.mp this).resolve_left hc₀
    have m32z : m32 = 0 := by
      have : c₀ * m32 = 0 := by simpa using g02.symm
      exact (mul_eq_zero.mp this).resolve_left hc₀
    have m00m33 : m00 = m33 := by
      have : c₀ * m00 = c₀ * m33 := by simpa using g03
      exact mul_left_cancel₀ hc₀ this
    have m10z : m10 = 0 := by
      have : c₀ * m10 = 0 := by simpa using g13
      exact (mul_eq_zero.mp this).resolve_left hc₀
    have hm33 : m33 ≠ 0 := by
      intro h
      rw [m10z, m20z, m30z, h] at s03
      simp at s03
    by_cases hb : b = 0
    · exfalso
      subst hb
      have hb' : b' = 0 := by
        have : b' * m33 = 0 := by simpa [m10z] using v13.symm
        exact (mul_eq_zero.mp this).resolve_right hm33
      have hcc : c = c' := by
        have : c * m00 = c' * m33 := by simpa [hb', m20z] using v03
        rw [m00m33] at this
        exact mul_right_cancel₀ hm33 this
      rcases hne with h | h
      · exact h (by rw [hb'])
      · exact h hcc
    · have m21z : m21 = 0 := by
        have : b * m21 = 0 := by simpa [m20z] using v23
        exact (mul_eq_zero.mp this).resolve_left hb
      exact ⟨m10z, m20z, m21z, m30z, m31z, m32z⟩
  ·
    have m20z : m20 = 0 := (mul_eq_zero.mp g22).resolve_left hb₀
    have m30z : m30 = 0 := (mul_eq_zero.mp g10).resolve_left hb₀
    have m31z : m31 = 0 := (mul_eq_zero.mp g11).resolve_left hb₀
    have m21z : m21 = 0 := by
      have : b₀ * m21 = 0 := by simpa [m20z] using g23
      exact (mul_eq_zero.mp this).resolve_left hb₀
    have m10m32 : m10 = m32 := mul_left_cancel₀ hb₀ g12
    have m10z : m10 = 0 := by
      by_contra hm10
      have m22m00 : m22 = m00 := by
        have h1 : m10 * (m00 + m22) = 0 := by
          rw [m20z, m30z] at s02
          rw [← m10m32] at s02
          linear_combination s02
        have h3 : m00 + m22 = 0 := (mul_eq_zero.mp h1).resolve_left hm10
        exact (CharTwo.add_eq_zero.mp h3).symm
      have hc₀ : c₀ = 0 := by
        have : c₀ * m10 = 0 := by
          rw [m22m00, ← m10m32] at g02
          linear_combination -g02
        exact (mul_eq_zero.mp this).resolve_right hm10
      have m11m33 : m11 = m33 := by
        have : b₀ * m11 = b₀ * m33 := by
          rw [hc₀] at g13
          simpa using g13
        exact mul_left_cancel₀ hb₀ this
      have hbb : b = b' := by
        rw [← m10m32] at v12
        have : m10 * b = m10 * b' := by linear_combination v12
        exact mul_left_cancel₀ hm10 this
      have hc'0 : c' = 0 := by
        rw [m22m00, ← m10m32, ← hbb] at v02
        have : c' * m10 = 0 := by linear_combination -v02
        exact (mul_eq_zero.mp this).resolve_right hm10
      have hc0 : c = 0 := by
        rw [m11m33, ← hbb] at v13
        have : c * m10 = 0 := by linear_combination v13
        exact (mul_eq_zero.mp this).resolve_right hm10
      rcases hne with h | h
      · exact h hbb
      · exact h (by rw [hc0, hc'0])
    exact ⟨m10z, m20z, m21z, m30z, m31z, by rw [← m10m32]; exact m10z⟩


structure ConjEq (m : Matrix (Fin 4) (Fin 4) K) (b c b' c' : K) : Prop where
  e00 : b' * m 2 0 + c' * m 3 0 = 0
  e01 : b' * m 2 1 + c' * m 3 1 = 0
  e02 : b * m 0 0 = b' * m 2 2 + c' * m 3 2
  e03 : c * m 0 0 + b * m 0 1 = b' * m 2 3 + c' * m 3 3
  e10 : b' * m 3 0 = 0
  e11 : b' * m 3 1 = 0
  e12 : b * m 1 0 = b' * m 3 2
  e13 : c * m 1 0 + b * m 1 1 = b' * m 3 3
  e22 : b * m 2 0 = 0
  e23 : c * m 2 0 + b * m 2 1 = 0
  e32 : b * m 3 0 = 0
  e33 : c * m 3 0 + b * m 3 1 = 0

theorem conjEq_of_mul_eq {y : antiSp K} {b c b' c' : K}
    (h : y * uElt 0 b c 0 = uElt 0 b' c' 0 * y) :
    ConjEq (glMat (y : GL (Fin 4) K)) b c b' c' := by
  have h1 := congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K)) h
  simp only [Subgroup.coe_mul, Units.val_mul, glMat_uElt] at h1
  have e : ∀ i j : Fin 4, (glMat (y : GL (Fin 4) K) * uMat (0 : K) b c 0) i j =
      (uMat (0 : K) b' c' 0 * glMat (y : GL (Fin 4) K)) i j := fun i j => by rw [h1]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e13 := e 1 3
  have e22 := e 2 2
  have e23 := e 2 3
  have e32 := e 3 2
  have e33 := e 3 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at e00 e01 e02 e03 e10 e11 e12 e13 e22 e23 e32 e33
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -e00
  · linear_combination -e01
  · linear_combination e02
  · linear_combination e03
  · rcases e10 with h | h <;> simp [h]
  · rcases e11 with h | h <;> simp [h]
  · linear_combination e12
  · linear_combination e13
  · rcases e22 with h | h <;> simp [h]
  · linear_combination e23
  · rcases e32 with h | h <;> simp [h]
  · linear_combination e33

omit [CharP K 2] in
theorem symp_entry (y : antiSp K) (i j : Fin 4) :
    glMat (y : GL (Fin 4) K) 0 i * glMat (y : GL (Fin 4) K) 3 j +
      glMat (y : GL (Fin 4) K) 1 i * glMat (y : GL (Fin 4) K) 2 j +
      glMat (y : GL (Fin 4) K) 2 i * glMat (y : GL (Fin 4) K) 1 j +
      glMat (y : GL (Fin 4) K) 3 i * glMat (y : GL (Fin 4) K) 0 j =
        if i.val + j.val = 3 then 1 else 0 := by
  have h := congrFun (congrFun (mem_antiSp.mp y.2) i) j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at h
  exact h

theorem upper_of_data {y : antiSp K} {b₀ c₀ b c b' c' : K} (hg : b₀ ≠ 0 ∨ c₀ ≠ 0)
    (hyg : y * uElt 0 b₀ c₀ 0 = uElt 0 b₀ c₀ 0 * y)
    (hv : y * uElt 0 b c 0 = uElt 0 b' c' 0 * y) (hne : b ≠ b' ∨ c ≠ c') :
    ∀ i j : Fin 4, j < i → glMat (y : GL (Fin 4) K) i j = 0 := by
  have hG := conjEq_of_mul_eq hyg
  have hV := conjEq_of_mul_eq hv
  have s02 := symp_entry y 0 2
  have s03 := symp_entry y 0 3
  norm_num at s02 s03
  obtain ⟨h10, h20, h21, h30, h31, h32⟩ := lower_zero_of_comm
    (glMat (y : GL (Fin 4) K) 0 0) (glMat (y : GL (Fin 4) K) 0 1) (glMat (y : GL (Fin 4) K) 0 2)
    (glMat (y : GL (Fin 4) K) 0 3) (glMat (y : GL (Fin 4) K) 1 0) (glMat (y : GL (Fin 4) K) 1 1)
    (glMat (y : GL (Fin 4) K) 1 2) (glMat (y : GL (Fin 4) K) 1 3) (glMat (y : GL (Fin 4) K) 2 0)
    (glMat (y : GL (Fin 4) K) 2 1) (glMat (y : GL (Fin 4) K) 2 2) (glMat (y : GL (Fin 4) K) 2 3)
    (glMat (y : GL (Fin 4) K) 3 0) (glMat (y : GL (Fin 4) K) 3 1) (glMat (y : GL (Fin 4) K) 3 2)
    (glMat (y : GL (Fin 4) K) 3 3) s02 s03 b₀ c₀ hg hG.e00 hG.e01 hG.e02 hG.e03 hG.e10 hG.e11 hG.e12
    hG.e13 hG.e22 hG.e23 hG.e32 hG.e33 b c b' c' hne hV.e02 hV.e03 hV.e12 hV.e13 hV.e23
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd hij (by decide)
    | assumption

theorem conj_radA1 (s b c d : K) :
    uElt s 0 0 0 * uElt 0 b c d * (uElt s 0 0 0)⁻¹ = uElt 0 (b + s * d) (c + s ^ 2 * d) d := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_inv, uElt_mul, uElt_mul]
  congr 1 <;> first | ring1 | (ring_nf; simp [h2])

theorem conj_radA2 (t a b c : K) :
    uElt 0 0 0 t * uElt a b c 0 * (uElt 0 0 0 t)⁻¹ = uElt a (b + a * t) c 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_inv, uElt_mul, uElt_mul]
  congr 1 <;> first | ring1 | (ring_nf; simp [h2])

theorem mul_radA1 (s b c d : K) :
    uElt 0 b c d * uElt 0 (b + s * d) (c + s ^ 2 * d) d = uElt 0 (s * d) (s ^ 2 * d) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul]
  congr 1 <;> first | ring1 | (ring_nf; simp [h2])

theorem mul_radA2 (t a b c : K) :
    uElt a b c 0 * uElt a (b + a * t) c 0 = uElt 0 (a * t) (a ^ 2 * t) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_mul]
  congr 1 <;> first | ring1 | (ring_nf; simp [h2])

theorem V_le_center [Finite K] {V : Subgroup (antiSp K)} (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v * v = 1) (hVU : V ≤ antiUnipotent K)
    (hN : antiUnipotent K ≤ Subgroup.normalizer (V : Set (antiSp K))) (hK : 4 ≤ Nat.card K) :
    V ≤ antiUnipotentCenter K := by
  classical
  have hfin : Finite (antiSp K) := inferInstance
  rcases elementary_le_radA1_or_radA2 hVU hV2 with h1 | h2
  · intro v hv
    obtain ⟨b, c, d, rfl⟩ := h1 hv
    by_cases hd : d = 0
    · exact ⟨b, c, by rw [hd]⟩
    · exfalso
      have hz : ∀ s : K, uElt 0 (s * d) (s ^ 2 * d) 0 ∈ V := by
        intro s
        have h := (Subgroup.mem_normalizer_iff.mp (hN (uElt_mem_antiUnipotent s 0 0 0)) _).mp hv
        rw [conj_radA1] at h
        have h' := V.mul_mem hv h
        rwa [mul_radA1] at h'
      let φ : K → V := fun s => ⟨uElt 0 (s * d) (s ^ 2 * d) 0, hz s⟩
      have hφ : Function.Injective φ := by
        intro s s' hss
        have := (uElt_inj (congrArg Subtype.val hss)).2.1
        exact mul_right_cancel₀ hd this
      have hle : Nat.card K ≤ Nat.card V := Nat.card_le_card_of_injective φ hφ
      have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hV4]; exact hK)
      obtain ⟨s, hs⟩ := hbij.2 ⟨uElt 0 b c d, hv⟩
      have := (uElt_inj (congrArg Subtype.val hs)).2.2.2
      exact hd this.symm
  · intro v hv
    obtain ⟨a, b, c, rfl⟩ := h2 hv
    by_cases ha : a = 0
    · exact ⟨b, c, by rw [ha]⟩
    · exfalso
      have hz : ∀ t : K, uElt 0 (a * t) (a ^ 2 * t) 0 ∈ V := by
        intro t
        have h := (Subgroup.mem_normalizer_iff.mp (hN (uElt_mem_antiUnipotent 0 0 0 t)) _).mp hv
        rw [conj_radA2] at h
        have h' := V.mul_mem hv h
        rwa [mul_radA2] at h'
      let φ : K → V := fun t => ⟨uElt 0 (a * t) (a ^ 2 * t) 0, hz t⟩
      have hφ : Function.Injective φ := by
        intro t t' htt
        have := (uElt_inj (congrArg Subtype.val htt)).2.1
        exact mul_left_cancel₀ ha this
      have hle : Nat.card K ≤ Nat.card V := Nat.card_le_card_of_injective φ hφ
      have hbij : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hV4]; exact hK)
      obtain ⟨t, ht⟩ := hbij.2 ⟨uElt a b c 0, hv⟩
      have := (uElt_inj (congrArg Subtype.val ht)).1
      exact ha this.symm

theorem y_upper {V : Subgroup (antiSp K)} {y : antiSp K} {b₀ c₀ : K}
    (hVz : V ≤ antiUnipotentCenter K) (hyV : y ∈ Subgroup.normalizer (V : Set (antiSp K)))
    (hnt : ¬ ∀ v ∈ V, y * v = v * y) (hx1 : uElt 0 b₀ c₀ 0 ≠ 1)
    (hxy : y * uElt 0 b₀ c₀ 0 = uElt 0 b₀ c₀ 0 * y) :
    ∀ i j : Fin 4, j < i → glMat (y : GL (Fin 4) K) i j = 0 := by
  push Not at hnt
  obtain ⟨v, hvV, hyv⟩ := hnt
  obtain ⟨b, c, rfl⟩ := hVz hvV
  have hv'V : y * uElt 0 b c 0 * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV _).mp hvV
  obtain ⟨b', c', hv'⟩ := hVz hv'V
  have hv : y * uElt 0 b c 0 = uElt 0 b' c' 0 * y := by
    rw [← hv']
    group
  have hne : b ≠ b' ∨ c ≠ c' := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact hyv hv
  have hg : b₀ ≠ 0 ∨ c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    exact hx1 uElt_zero_eq_one
  exact upper_of_data hg hxy hv hne

end CFSG.Quasithin.SzN27.Sp4

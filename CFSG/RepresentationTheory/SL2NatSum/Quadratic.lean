module

public import CFSG.RepresentationTheory.SL2NatSum.Core
public import CFSG.RepresentationTheory.SL2NatSum.Spectrum
public import CFSG.HardMathSupport.Seitz.Proving.SL2OrderThree

public section

namespace CFSG.RepresentationTheory.SL2NatSum

open CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
open scoped Matrix MatrixGroups

private lemma exists_order_three_sl2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    ∃ d : SL(2, K), d ^ 3 = 1 ∧ d ≠ 1 := by
  have hpow : (2 ^ n : ℕ) ^ 2 = 4 ^ n := by
    rw [← pow_mul, show n * 2 = 2 * n by omega, pow_mul]
    norm_num
  have hmod : 4 ^ n % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h3dvd : 3 ∣ Nat.card K ^ 2 - 1 := by
    rw [hK, hpow]
    exact Nat.dvd_iff_mod_eq_zero.mpr (by simpa using Nat.sub_mod_eq_zero_of_mod_eq hmod)
  obtain ⟨d, hdord⟩ :=
    CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_three_SL2 K h3dvd
  have hd3 : d ^ 3 = 1 := by rw [← hdord]; exact pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdord
    omega
  exact ⟨d, hd3, hd1⟩

private lemma matrix_relation_of_torus {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : n = 2 ∨ 4 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V, ρ c (ρ c v) + ρ c v + v = 0)
    {m : ℕ} (Rm : SL(2, K) →* Matrix (Fin m) (Fin m) (ZMod 2))
    (c : V ≃ₗ[ZMod 2] (Fin m → ZMod 2))
    (hc : ∀ (g : SL(2, K)) (v : V), c (ρ g v) = Rm g *ᵥ c v) :
    ∀ x y : K, (Rm (uMat y) - 1) * (Rm (uMat x) - 1) = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hn2 : 2 ≤ n := by rcases hn with rfl | h4 <;> omega
  have hq : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨d, hd3, hd1⟩ := exists_order_three_sl2 hK hn2
  have hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0 := hfpf d hd3 hd1
  obtain ⟨t, htgen⟩ := IsCyclic.exists_generator (α := Kˣ)
  have ht : orderOf t = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers htgen, Nat.card_units, hK]
  have htK : orderOf (t : K) = 2 ^ n - 1 := by rw [orderOf_units, ht]
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let I : Matrix (Fin m) (Fin m) (ZMod 2) →+* Matrix (Fin m) (Fin m) K :=
    RingHom.mapMatrix ι
  let P : K → Matrix (Fin m) (Fin m) K := fun x => I (Rm (uMat x)) - 1
  let h : Matrix (Fin m) (Fin m) K := I (Rm (hMat t))
  have hP0 : P 0 = 0 := by simp [P, uMat_zero]
  have hPadd : ∀ x y, P (x + y) = P x + P y + P x * P y := by
    intro x y
    simp only [P, ← uMat_mul, map_mul, neg_smul, one_smul]
    noncomm_ring
  have hh : ∀ x, h * P x = P ((t : K) ^ 2 * x) * h := by
    intro x
    simp only [h, P]
    calc
      I (Rm (hMat t)) * (I (Rm (uMat x)) - 1)
          = I (Rm (hMat t) * Rm (uMat x)) - I (Rm (hMat t)) := by
            rw [map_mul, mul_sub, mul_one]
      _ = I (Rm (hMat t * uMat x)) - I (Rm (hMat t)) := by rw [← map_mul]
      _ = I (Rm (uMat ((t : K) ^ 2 * x) * hMat t)) - I (Rm (hMat t)) := by
            rw [hMat_mul_uMat]
      _ = I (Rm (uMat ((t : K) ^ 2 * x))) * I (Rm (hMat t)) -
            I (Rm (hMat t)) := by rw [map_mul, map_mul]
      _ = (I (Rm (uMat ((t : K) ^ 2 * x))) - 1) * I (Rm (hMat t)) := by
            rw [sub_mul, one_mul]
  have hspec : ∀ e : ℕ, ¬ IsTorusWt n (e : ZMod (2 ^ n - 1)) →
      ∑ k ∈ Finset.range (2 ^ n - 1), (((t : K) ^ e)⁻¹) ^ k • h ^ k = 0 := by
    intro e he
    have he' : ∀ i : ℕ, (e : ZMod (2 ^ n - 1)) ≠ 2 ^ i ∧
        (e : ZMod (2 ^ n - 1)) ≠ -2 ^ i := by
      unfold IsTorusWt at he
      push Not at he
      exact he
    simpa [h, I] using
      torusProj_eq_zero hK t ht d hd3 hd1 ρ hdV Rm c hc e he'
  have hzero : ∀ x y : K, P x * P y = 0 :=
    mul_eq_zero_of_torus hq hn P hP0 hPadd htK h hh hspec
  intro x y
  have hinj : Function.Injective I :=
    Matrix.map_injective (ZMod.castHom_injective (R := K))
  refine hinj ?_
  simpa only [P, map_mul, map_sub, map_one, map_zero] using hzero y x

private lemma fixes_of_matrix_relation {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}
    (ρ : Representation (ZMod 2) SL(2, K) V)
    (Rm : SL(2, K) →* Matrix (Fin m) (Fin m) (ZMod 2))
    (c : V ≃ₗ[ZMod 2] (Fin m → ZMod 2))
    (hc : ∀ (g : SL(2, K)) (v : V), c (ρ g v) = Rm g *ᵥ c v) {x y : K}
    (hprod : (Rm (uMat y) - 1) * (Rm (uMat x) - 1) = 0) :
    ∀ v : V, ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v := by
  intro v
  apply c.injective
  let A : Matrix (Fin m) (Fin m) (ZMod 2) := Rm (uMat x)
  let B : Matrix (Fin m) (Fin m) (ZMod 2) := Rm (uMat y)
  have hprod' : (B - 1) * (A - 1) = 0 := by simpa [A, B] using hprod
  have hBA : B * (A - 1) = A - 1 := by
    calc B * (A - 1) = (B - 1) * (A - 1) + (A - 1) := by noncomm_ring
      _ = A - 1 := by rw [hprod', zero_add]
  calc
    c (ρ (uMat y) (ρ (uMat x) v - v))
        = B *ᵥ c (ρ (uMat x) v - v) := hc (uMat y) _
    _ = B *ᵥ (A *ᵥ c v - c v) := by rw [map_sub, hc (uMat x) v]
    _ = (B * (A - 1)) *ᵥ c v := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mulVec,
            mul_one]
    _ = (A - 1) *ᵥ c v := by rw [hBA]
    _ = A *ᵥ c v - c v := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    _ = c (ρ (uMat x) v) - c v := by rw [hc (uMat x) v]
    _ = c (ρ (uMat x) v - v) := by rw [map_sub]

theorem quadratic_of_ne_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : n = 2 ∨ 4 ≤ n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) SL(2, K) V)
    (hfpf : ∀ c : SL(2, K), c ^ 3 = 1 → c ≠ 1 → ∀ v : V, ρ c (ρ c v) + ρ c v + v = 0) :
    ∀ (x y : K) (v : V), ρ (uMat y) (ρ (uMat x) v - v) = ρ (uMat x) v - v := by
  obtain ⟨m, Rm, c, hc⟩ := exists_matrix_model ρ
  intro x y v
  exact fixes_of_matrix_relation ρ Rm c hc
    (matrix_relation_of_torus hK hn ρ hfpf Rm c hc x y) v

end CFSG.RepresentationTheory.SL2NatSum

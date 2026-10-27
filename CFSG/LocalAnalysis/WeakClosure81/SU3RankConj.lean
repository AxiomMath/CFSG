module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.ClassicalGroups.Unitary.InvolutionTransvection
import CFSG.RankThree.GF2n.Smith81.Sec220DihLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open Matrix

private theorem exists_dotProduct_ne_zero_of_ne_zero {K : Type*} [Field K] {n : ℕ}
    {r : Fin n → K} (hr : r ≠ 0) : ∃ x : Fin n → K, r ⬝ᵥ x ≠ 0 := by
  by_contra h
  push Not at h
  exact hr (funext fun i => by simpa using h (Pi.single i 1))

private theorem herm_basis {K : Type*} [Field K] (σ : K ≃+* K) (x : Fin 3 → K) :
    herm σ ![1, 1, 0] x = x 0 + x 1 := by
  simp [herm, Fin.sum_univ_three]

private theorem transvection_basis {K : Type*} [Field K] [CharP K 2]
    (σ : K ≃+* K) (x : Fin 3 → K) :
    x + (herm σ ![1, 1, 0] x) • ![1, 1, 0] = x ∘ Equiv.swap 0 1 := by
  rw [herm_basis σ x]
  funext i
  fin_cases i
  · simp
    linear_combination (CharTwo.add_self_eq_zero (x 0))
  · simp
    linear_combination (CharTwo.add_self_eq_zero (x 1))
  · simp [Equiv.swap_apply_of_ne_of_ne (show (2 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 1 by decide)]

private theorem exists_transvection_of_isometry {K : Type*} [Field K] [CharP K 2]
    {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    {T : (Fin n → K) → (Fin n → K)} {p r : Fin n → K}
    (hp : p ≠ 0) (hr : r ≠ 0) (hpr : r ⬝ᵥ p = 0)
    (hT : ∀ x, T x = x + (r ⬝ᵥ x) • p)
    (hiso : ∀ x y, herm σ (T x) (T y) = herm σ x y) :
    ∃ c : K, c ≠ 0 ∧ σ c = c ∧ herm σ p p = 0 ∧
      ∀ x, T x = x + (c * herm σ p x) • p := by
  have hkey : ∀ x y : Fin n → K, (r ⬝ᵥ y) * herm σ x p + σ (r ⬝ᵥ x) * herm σ p y
      + σ (r ⬝ᵥ x) * (r ⬝ᵥ y) * herm σ p p = 0 := by
    intro x y
    have h := hiso x y
    simp only [hT, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right] at h
    linear_combination h
  have hpp : herm σ p p = 0 := by
    obtain ⟨x, hx⟩ := exists_dotProduct_ne_zero_of_ne_zero hr
    have h := hkey x p
    rw [hpr] at h
    simp only [mul_zero, zero_mul, add_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hx)
  obtain ⟨y₀, hy₀⟩ := exists_dotProduct_ne_zero_of_ne_zero hr
  set x₀ : Fin n → K := (r ⬝ᵥ y₀)⁻¹ • y₀ with hx₀def
  have hx₀ : r ⬝ᵥ x₀ = 1 := by
    rw [hx₀def, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hy₀]
  have hrel : ∀ y : Fin n → K, herm σ p y = (r ⬝ᵥ y) * herm σ x₀ p := by
    intro y
    have h := hkey x₀ y
    rw [hpp] at h
    simp only [mul_zero, add_zero] at h
    rw [hx₀] at h
    simp only [map_one, one_mul] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  have hlam0 : herm σ x₀ p ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hp
    exact hy (by rw [hrel y, h0, mul_zero])
  have hc_eq : ∀ y : Fin n → K, r ⬝ᵥ y = (herm σ x₀ p)⁻¹ * herm σ p y := by
    intro y
    calc r ⬝ᵥ y = (r ⬝ᵥ y) * (herm σ x₀ p * (herm σ x₀ p)⁻¹) := by
          rw [mul_inv_cancel₀ hlam0, mul_one]
      _ = ((r ⬝ᵥ y) * herm σ x₀ p) * (herm σ x₀ p)⁻¹ := by ring
      _ = herm σ p y * (herm σ x₀ p)⁻¹ := by rw [← hrel y]
      _ = (herm σ x₀ p)⁻¹ * herm σ p y := by ring
  have hσc : σ ((herm σ x₀ p)⁻¹) = (herm σ x₀ p)⁻¹ := by
    have hzero : ∀ x y : Fin n → K,
        herm σ p y * herm σ x p * ((herm σ x₀ p)⁻¹ + σ ((herm σ x₀ p)⁻¹)) = 0 := by
      intro x y
      have h := hkey x y
      rw [hpp] at h
      simp only [mul_zero, add_zero] at h
      rw [hc_eq y, hc_eq x, map_mul] at h
      have hσh : σ (herm σ p x) = herm σ x p := by
        rw [herm_conj σ hσ x p]
        exact hσ (herm σ x p)
      rw [hσh] at h
      linear_combination h
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hp
    have hx : herm σ y p ≠ 0 := by
      intro h0
      exact hy (by rw [herm_conj σ hσ y p, h0, map_zero])
    have h := hzero y y
    have hsum : (herm σ x₀ p)⁻¹ + σ ((herm σ x₀ p)⁻¹) = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hy
        · exact absurd h2 hx
      · exact h1
    exact (CharTwo.add_eq_zero.mp hsum).symm
  refine ⟨(herm σ x₀ p)⁻¹, inv_ne_zero hlam0, hσc, hpp, fun x => ?_⟩
  rw [hT x, hc_eq x]

theorem exists_mul_mul_inv_eq_permSU_swap {n : ℕ} {F₀ : Type} [Field F₀] [Finite F₀]
    [CharP F₀ 2] (hcard : Nat.card F₀ = (2 ^ n) ^ 2) (g : ↥(StatedSU 3 (2 ^ n) F₀))
    (hg : Matrix.rank (((g : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀) - 1) = 1) :
    ∃ m : ↥(StatedSU 3 (2 ^ n) F₀), m * g * m⁻¹ = permSU n F₀ (Equiv.swap 0 1) := by
  classical
  let σ : F₀ ≃+* F₀ := unitaryInvolution F₀ 2 n
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := n) hcard
  have hSU : SUid σ 3 = StatedSU 3 (2 ^ n) F₀ :=
    SUid_eq_statedSU (p := 2) (f := n) hcard 3
  let t : SUid σ 3 := ⟨(g : GL (Fin 3) F₀), by rw [hSU]; exact g.2⟩
  let s : SUid σ 3 := ⟨(permSU n F₀ (Equiv.swap 0 1) : GL (Fin 3) F₀), by
    rw [hSU]; exact (permSU n F₀ (Equiv.swap 0 1)).2⟩
  have htval : (t : GL (Fin 3) F₀) = (g : GL (Fin 3) F₀) := rfl
  have hsval : (s : GL (Fin 3) F₀) = (permSU n F₀ (Equiv.swap 0 1) : GL (Fin 3) F₀) := rfl
  have hrank : (((t : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀) - 1).rank = 1 := by
    rw [htval]; exact hg
  have hdet : ((t : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀).det = 1 := by
    rw [htval]; exact CFSG.Open.StatedAPI.det_of_mem_statedSU g.2
  obtain ⟨p, r, hp, hr, hpr, hMeq⟩ :=
    CFSG.RankThree.GF2n.Smith81.exists_eq_dihTv_of_rank_eq_one hrank hdet
  have hT : ∀ x : Fin 3 → F₀, t • x = x + (r ⬝ᵥ x) • p := by
    intro x
    rw [smul_def, hMeq, CFSG.RankThree.GF2n.Smith81.dihTv_mulVec]
  have hiso : ∀ x y : Fin 3 → F₀, herm σ (t • x) (t • y) = herm σ x y :=
    fun x y => herm_smul_smul σ t x y
  obtain ⟨c, hc0, hcσ, hpp, htrans⟩ :=
    exists_transvection_of_isometry hσ.invol hp hr hpr hT hiso
  have he0 : (![1, 1, 0] : Fin 3 → F₀) ≠ 0 := by
    intro h
    have h0 : (1 : F₀) = 0 := by simpa using congrFun h 0
    exact one_ne_zero h0
  have he : herm σ (![1, 1, 0] : Fin 3 → F₀) (![1, 1, 0] : Fin 3 → F₀) = 0 := by
    rw [herm_basis σ ![1, 1, 0]]
    simp [CharTwo.add_self_eq_zero]
  obtain ⟨m₀, hm₀⟩ :=
    exists_conj_smul_eq_of_transvection hσ (by norm_num) hp hpp hc0 hcσ htrans he0 he
  have hms : m₀ * t * m₀⁻¹ = s := by
    refine ext_smul σ fun x => ?_
    rw [hm₀ x, smul_def]
    have hs : (s : GL (Fin 3) F₀) = CFSG.RankThree.Classical.permGL (Equiv.swap 0 1) := by
      rw [hsval]
      exact coe_permSU n F₀ (Equiv.swap 0 1)
    rw [hs, CFSG.RankThree.Classical.permGL_mulVec, Equiv.swap_inv]
    exact transvection_basis σ x
  refine ⟨⟨(m₀ : GL (Fin 3) F₀), by rw [← hSU]; exact m₀.2⟩, ?_⟩
  apply Subtype.ext
  have hval := congrArg (fun z : SUid σ 3 => (z : GL (Fin 3) F₀)) hms
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, htval, hsval] using hval

end CFSG.LocalAnalysis.WeakClosure81

end

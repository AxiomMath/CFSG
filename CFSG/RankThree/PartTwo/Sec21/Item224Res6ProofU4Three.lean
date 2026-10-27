module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofZab
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofUBT

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]
variable (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem exists_ne_zero_perp {m : ℕ} (hm : m < n) (w : Fin m → Fin n → K) :
    ∃ v : Fin n → K, v ≠ 0 ∧ ∀ i, (uF h n).β (w i) v = 0 := by
  let L : (Fin n → K) →ₗ[K] (Fin m → K) := LinearMap.pi fun i => (uF h n).toDual (w i)
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hm)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hv0, fun i => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hv) i
  simpa [L] using this

theorem exists_hyp_perp (hn : 4 ≤ n) {a b : Fin n → K} (haa : (uF h n).β a a = 0)
    (hbb : (uF h n).β b b = 0) (hab : (uF h n).β a b = 1) :
    ∃ c d : Fin n → K, (uF h n).β c c = 0 ∧ (uF h n).β d d = 0 ∧ (uF h n).β c d = 1 ∧
      (uF h n).β a c = 0 ∧ (uF h n).β b c = 0 ∧ (uF h n).β a d = 0 ∧ (uF h n).β b d = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hba : (uF h n).β b a = 1 := uF_swap_one h hab
  have hK := card_sq_of_unitary h
  obtain ⟨c, hc0, hcc, hac, hbc⟩ : ∃ c : Fin n → K, c ≠ 0 ∧ (uF h n).β c c = 0 ∧
      (uF h n).β a c = 0 ∧ (uF h n).β b c = 0 := by
    obtain ⟨u₁, hu₁0, hu₁⟩ := exists_ne_zero_perp h (m := 2) (by omega) ![a, b]
    have hau₁ : (uF h n).β a u₁ = 0 := hu₁ 0
    have hbu₁ : (uF h n).β b u₁ = 0 := hu₁ 1
    by_cases h11 : (uF h n).β u₁ u₁ = 0
    · exact ⟨u₁, hu₁0, h11, hau₁, hbu₁⟩
    obtain ⟨u₂, hu₂0, hu₂⟩ := exists_ne_zero_perp h (m := 3) (by omega) ![a, b, u₁]
    have hau₂ : (uF h n).β a u₂ = 0 := hu₂ 0
    have hbu₂ : (uF h n).β b u₂ = 0 := hu₂ 1
    have hu₁u₂ : (uF h n).β u₁ u₂ = 0 := hu₂ 2
    by_cases h22 : (uF h n).β u₂ u₂ = 0
    · exact ⟨u₂, hu₂0, h22, hau₂, hbu₂⟩
    have hu₂u₁ : (uF h n).β u₂ u₁ = 0 := by rw [uF_symm, hu₁u₂, map_zero]
    have hfix : (uF h n).σ ((uF h n).β u₁ u₁ / (uF h n).β u₂ u₂) =
        (uF h n).β u₁ u₁ / (uF h n).β u₂ u₂ := by
      rw [map_div₀, ← uF_symm, ← uF_symm]
    obtain ⟨t, ht⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hfix
      (div_ne_zero h11 h22)
    have ht' : (uF h n).σ t * t * (uF h n).β u₂ u₂ = (uF h n).β u₁ u₁ := by
      have ht'' : (uF h n).σ t * t = (uF h n).β u₁ u₁ / (uF h n).β u₂ u₂ := ht
      rw [ht'', div_mul_cancel₀ _ h22]
    refine ⟨u₁ + t • u₂, ?_, ?_, ?_, ?_⟩
    · intro h0
      apply h11
      have h3 := congrArg ((uF h n).β u₁) h0
      rw [(uF h n).add_right, (uF h n).smul_right, hu₁u₂, mul_zero, add_zero,
        (uF h n).β_zero_right] at h3
      exact h3
    · simp only [(uF h n).add_left, (uF h n).add_right, (uF h n).smul_left,
        (uF h n).smul_right, hu₁u₂, hu₂u₁]
      linear_combination ht' + (uF h n).β u₁ u₁ * h2
    · rw [(uF h n).add_right, (uF h n).smul_right, hau₁, hau₂, mul_zero, add_zero]
    · rw [(uF h n).add_right, (uF h n).smul_right, hbu₁, hbu₂, mul_zero, add_zero]
  obtain ⟨w, hw⟩ : ∃ w, (uF h n).β c w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc0 ((uF h n).nondeg c hall)
  have hca : (uF h n).β c a = 0 := by rw [uF_symm, hac, map_zero]
  have hcb : (uF h n).β c b = 0 := by rw [uF_symm, hbc, map_zero]
  obtain ⟨w', hw'⟩ : ∃ w' : Fin n → K,
      w' = w - (uF h n).β b w • a - (uF h n).β a w • b := ⟨_, rfl⟩
  have haw' : (uF h n).β a w' = 0 := by
    rw [hw', (uF h n).β_sub_right, (uF h n).β_sub_right, (uF h n).smul_right,
      (uF h n).smul_right, haa, hab]
    ring
  have hbw' : (uF h n).β b w' = 0 := by
    rw [hw', (uF h n).β_sub_right, (uF h n).β_sub_right, (uF h n).smul_right,
      (uF h n).smul_right, hba, hbb]
    ring
  have hcw' : (uF h n).β c w' = (uF h n).β c w := by
    rw [hw', (uF h n).β_sub_right, (uF h n).β_sub_right, (uF h n).smul_right,
      (uF h n).smul_right, hca, hcb]
    ring
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : Fin n → K, d₁ = ((uF h n).β c w)⁻¹ • w' := ⟨_, rfl⟩
  have hcd₁ : (uF h n).β c d₁ = 1 := by
    rw [hd₁, (uF h n).smul_right, hcw', inv_mul_cancel₀ hw]
  have had₁ : (uF h n).β a d₁ = 0 := by rw [hd₁, (uF h n).smul_right, haw', mul_zero]
  have hbd₁ : (uF h n).β b d₁ = 0 := by rw [hd₁, (uF h n).smul_right, hbw', mul_zero]
  have hd₁c : (uF h n).β d₁ c = 1 := uF_swap_one h hcd₁
  have hfix : (uF h n).σ ((uF h n).β d₁ d₁) = (uF h n).β d₁ d₁ := (uF_symm h d₁ d₁).symm
  obtain ⟨s, hs⟩ := exists_add_unitaryInvolution_eq hK hfix
  have hs' : s + (uF h n).σ s = (uF h n).β d₁ d₁ := hs
  refine ⟨c, d₁ + s • c, hcc, ?_, ?_, hac, hbc, ?_, ?_⟩
  · simp only [(uF h n).add_left, (uF h n).add_right, (uF h n).smul_left, (uF h n).smul_right,
      hcc, hd₁c, hcd₁]
    linear_combination hs' + (uF h n).β d₁ d₁ * h2
  · rw [(uF h n).add_right, (uF h n).smul_right, hcd₁, hcc, mul_zero, add_zero]
  · rw [(uF h n).add_right, (uF h n).smul_right, had₁, hac, mul_zero, add_zero]
  · rw [(uF h n).add_right, (uF h n).smul_right, hbd₁, hbc, mul_zero, add_zero]

section Mat

variable {M : Matrix (Fin n) (Fin n) K}
  (hMiso : ∀ u v, (uF h n).β (M *ᵥ u) (M *ᵥ v) = (uF h n).β u v)
  (hM3 : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v)) = v)

include hMiso in
theorem inner_mulVec_of_eigen {x : Fin n → K} {l : K} (hx : M *ᵥ x = l • x) (hl3 : l ^ 3 = 1)
    (hσl : (uF h n).σ l = l) (w : Fin n → K) :
    (uF h n).β x (M *ᵥ w) = l ^ 2 * (uF h n).β x w := by
  have hx' : M *ᵥ (l ^ 2 • x) = x := by
    rw [Matrix.mulVec_smul, hx, smul_smul, show l ^ 2 * l = 1 by linear_combination hl3,
      one_smul]
  calc (uF h n).β x (M *ᵥ w) = (uF h n).β (M *ᵥ (l ^ 2 • x)) (M *ᵥ w) := by rw [hx']
    _ = (uF h n).β (l ^ 2 • x) w := hMiso _ _
    _ = l ^ 2 * (uF h n).β x w := by rw [(uF h n).smul_left, map_pow, hσl]

include hMiso in
theorem inner_eq_zero_of_eigen {x y : Fin n → K} {l m : K} (hx : M *ᵥ x = l • x)
    (hy : M *ᵥ y = m • y) (hlm : (uF h n).σ l * m ≠ 1) : (uF h n).β x y = 0 := by
  have h1 := hMiso x y
  rw [hx, hy, (uF h n).smul_left, (uF h n).smul_right] at h1
  have h3 : ((uF h n).σ l * m - 1) * (uF h n).β x y = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hlm)

omit h [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
include hM3 in
theorem mulVec_comp {μ : K} (hμ : μ ^ 3 = 1) (w : Fin n → K) :
    M *ᵥ (w + μ ^ 2 • (M *ᵥ w) + μ • (M *ᵥ (M *ᵥ w))) =
      μ • (w + μ ^ 2 • (M *ᵥ w) + μ • (M *ᵥ (M *ᵥ w))) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM3]
  linear_combination (norm := module) -(hμ • (M *ᵥ w))

omit h [Finite K] [Fact (Nat.Prime 2)] [CharP K 2] in
theorem mulVec_eq_of_comp_eq_zero {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    {v : Fin n → K} (h1 : v + ω ^ 2 • (M *ᵥ v) + ω • (M *ᵥ (M *ᵥ v)) = 0)
    (h2 : v + (ω ^ 2) ^ 2 • (M *ᵥ v) + ω ^ 2 • (M *ᵥ (M *ᵥ v)) = 0) : M *ᵥ v = v := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hne : ω ^ 2 - ω ≠ 0 := by
    rw [show ω ^ 2 - ω = ω * (ω - 1) by ring]
    exact mul_ne_zero hω0 (sub_ne_zero.mpr hω1)
  have h3 : (ω ^ 2 - ω) • (M *ᵥ v - M *ᵥ (M *ᵥ v)) = 0 := by
    linear_combination (norm := module) h1 - h2 + (ω * hω3) • (M *ᵥ v)
  have hMM : M *ᵥ (M *ᵥ v) = M *ᵥ v := by
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hne
    · exact (sub_eq_zero.mp h4).symm
  linear_combination (norm := module) -h1 + hω • (M *ᵥ v) + ω • hMM

include hMiso hM3 in
theorem exists_eigen_pair {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hσω : (uF h n).σ ω = ω) {v : Fin n → K} (hv : M *ᵥ v ≠ v) :
    ∃ a b : Fin n → K, M *ᵥ a = ω • a ∧ M *ᵥ b = ω ^ 2 • b ∧ (uF h n).β a b = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω23 : (ω ^ 2) ^ 3 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  have hσω2 : (uF h n).σ (ω ^ 2) = ω ^ 2 := by rw [map_pow, hσω]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpartner : ∀ {x : Fin n → K} {l : K}, x ≠ 0 → M *ᵥ x = l • x → l ^ 3 = 1 →
      (uF h n).σ l = l → ∃ y, M *ᵥ y = l ^ 2 • y ∧ (uF h n).β x y = 1 := by
    intro x l hx0 hx hl3 hσl
    obtain ⟨w, hw⟩ : ∃ w, (uF h n).β x w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx0 ((uF h n).nondeg x hall)
    have hl23 : (l ^ 2) ^ 3 = 1 := by linear_combination (l ^ 3 + 1) * hl3
    have hMy' := mulVec_comp hM3 hl23 w
    have hxy' : (uF h n).β x (w + (l ^ 2) ^ 2 • (M *ᵥ w) + l ^ 2 • (M *ᵥ (M *ᵥ w))) =
        (uF h n).β x w := by
      simp only [(uF h n).add_right, (uF h n).smul_right,
        inner_mulVec_of_eigen h hMiso hx hl3 hσl]
      linear_combination (uF h n).β x w * l ^ 6 * h2
    refine ⟨((uF h n).β x (w + (l ^ 2) ^ 2 • (M *ᵥ w) + l ^ 2 • (M *ᵥ (M *ᵥ w))))⁻¹ •
      (w + (l ^ 2) ^ 2 • (M *ᵥ w) + l ^ 2 • (M *ᵥ (M *ᵥ w))), ?_, ?_⟩
    · rw [Matrix.mulVec_smul, hMy', smul_comm]
    · rw [(uF h n).smul_right, inv_mul_cancel₀ (hxy' ▸ hw)]
  have hcomp : (v + ω ^ 2 • (M *ᵥ v) + ω • (M *ᵥ (M *ᵥ v))) ≠ 0 ∨
      (v + (ω ^ 2) ^ 2 • (M *ᵥ v) + ω ^ 2 • (M *ᵥ (M *ᵥ v))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (mulVec_eq_of_comp_eq_zero hω hω1 hcon.1 hcon.2)
  rcases hcomp with hx0 | hx0
  · obtain ⟨y, hy, hxy⟩ := hpartner hx0 (mulVec_comp hM3 hω3 v) hω3 hσω
    exact ⟨_, y, mulVec_comp hM3 hω3 v, hy, hxy⟩
  · obtain ⟨y, hy, hxy⟩ := hpartner hx0 (mulVec_comp hM3 hω23 v) hω23 hσω2
    refine ⟨y, _, ?_, mulVec_comp hM3 hω23 v, uF_swap_one h hxy⟩
    rw [hy, show (ω ^ 2) ^ 2 = ω by linear_combination ω * hω3]

include hMiso hM3 in
theorem exists_zMat {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hσω : (uF h n).σ ω = ω)
    (hn : 4 ≤ n) {v : Fin n → K} (hv : M *ᵥ v ≠ v) :
    ∃ c d : Fin n → K, (uF h n).β c c = 0 ∧ (uF h n).β d d = 0 ∧ (uF h n).β c d = 1 ∧
      M * zMat f ω c d = zMat f ω c d * M ∧ zMat f ω c d *ᵥ c ≠ c ∧
      ∃ u, zMat f ω c d *ᵥ u = u ∧ M *ᵥ u ≠ u ∧ M *ᵥ (M *ᵥ u) ≠ u := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hω21 : ω ^ 2 ≠ 1 := by
    intro h21
    apply hω1
    linear_combination -ω * h21 + hω3
  have hσω2 : (uF h n).σ (ω ^ 2) = ω ^ 2 := by rw [map_pow, hσω]
  obtain ⟨a, b, ha, hb, hab⟩ := exists_eigen_pair h hMiso hM3 hω hω1 hσω hv
  have hba : (uF h n).β b a = 1 := uF_swap_one h hab
  have haa : (uF h n).β a a = 0 := inner_eq_zero_of_eigen h hMiso ha ha (by
    rw [hσω, ← sq]
    exact hω21)
  have hbb : (uF h n).β b b = 0 := inner_eq_zero_of_eigen h hMiso hb hb (by
    rw [hσω2, show ω ^ 2 * ω ^ 2 = ω by linear_combination ω * hω3]
    exact hω1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [(uF h n).β_zero_left] at hab
    exact zero_ne_one hab
  have hMa : M *ᵥ a ≠ a := by
    rw [ha]
    intro h1
    have h3 : (ω - 1) • a = 0 := by linear_combination (norm := module) h1
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact hω1 (sub_eq_zero.mp h4)
    · exact ha0 h4
  have hMMa : M *ᵥ (M *ᵥ a) ≠ a := by
    rw [ha, Matrix.mulVec_smul, ha, smul_smul]
    intro h1
    have h3 : (ω * ω - 1) • a = 0 := by linear_combination (norm := module) h1
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact hω21 (by linear_combination h4)
    · exact ha0 h4
  by_cases hA : ∃ u, (uF h n).β a u = 0 ∧ (uF h n).β b u = 0 ∧ M *ᵥ u ≠ u
  ·
    obtain ⟨u, hau, hbu, hMu⟩ := hA
    refine ⟨a, b, haa, hbb, hab, ?_, ?_, u, ?_, hMu, ?_⟩
    · exact zMat_comm h ω hbb hMiso ha hb (by rw [hσω]; linear_combination hω3)
        (by rw [hσω2]; linear_combination hω3)
    · rw [zMat_mulVec h ω hbb, hba, haa]
      intro h1
      have h3 : ω ^ 2 • a = 0 := by linear_combination (norm := module) h1
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact hω0 (pow_eq_zero_iff (by norm_num) |>.mp h4)
      · exact ha0 h4
    · rw [zMat_mulVec h ω hbb, hbu, hau, mul_zero, mul_zero, zero_smul, zero_smul, add_zero,
        add_zero]
    · intro h1
      apply hMu
      have h3 := hM3 u
      rw [h1] at h3
      exact h3
  ·
    push Not at hA
    obtain ⟨c, d, hcc, hdd, hcd, hac, hbc, had, hbd⟩ := exists_hyp_perp h hn haa hbb hab
    have hMc : M *ᵥ c = (1 : K) • c := by rw [one_smul]; exact hA c hac hbc
    have hMd : M *ᵥ d = (1 : K) • d := by rw [one_smul]; exact hA d had hbd
    have hca : (uF h n).β c a = 0 := by rw [uF_symm, hac, map_zero]
    have hda : (uF h n).β d a = 0 := by rw [uF_symm, had, map_zero]
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [(uF h n).β_zero_left] at hcd
      exact zero_ne_one hcd
    refine ⟨c, d, hcc, hdd, hcd, ?_, ?_, a, ?_, hMa, hMMa⟩
    · exact zMat_comm h ω hdd hMiso hMc hMd (by rw [map_one, one_mul])
        (by rw [map_one, one_mul])
    · rw [zMat_mulVec h ω hdd, uF_swap_one h hcd, hcc]
      intro h1
      have h3 : ω ^ 2 • c = 0 := by linear_combination (norm := module) h1
      rcases smul_eq_zero.mp h3 with h4 | h4
      · exact hω0 (pow_eq_zero_iff (by norm_num) |>.mp h4)
      · exact hc0 h4
    · rw [zMat_mulVec h ω hdd, hda, hca, mul_zero, mul_zero, zero_smul, zero_smul, add_zero,
        add_zero]

end Mat

theorem exists_commuting_three (hf : Even f) (hn : 4 ≤ n) {X : GL (Fin n) K} (hX : X ∈ uS h n)
    (hX3 : X ^ 3 = 1) (hX1 : X ≠ 1) :
    ∃ Z ∈ uS h n, Z ^ 3 = 1 ∧ Z * X = X * Z ∧ Z ≠ 1 ∧ Z ≠ X ∧ Z ≠ X ^ 2 := by
  classical
  obtain ⟨ω, hωp, hωq⟩ := exists_primitive_cube_root h hf
  have hω3 : ω ^ 3 = 1 := hωp.pow_eq_one
  have hω1 : ω ≠ 1 := hωp.ne_one (by norm_num)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  have hσω : (uF h n).σ ω = ω := by rw [uF_σ, UnitaryFieldData.bar_apply, hωq]
  have hMiso := uF_isometry_of_mem h hX
  have hXXX : X * X * X = 1 := by rw [← pow_three', hX3]
  have hM3 : ∀ v, (X : Matrix (Fin n) (Fin n) K) *ᵥ ((X : Matrix (Fin n) (Fin n) K) *ᵥ
      ((X : Matrix (Fin n) (Fin n) K) *ᵥ v)) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hXXX,
      Units.val_one, Matrix.one_mulVec]
  obtain ⟨v, hv⟩ : ∃ v, (X : Matrix (Fin n) (Fin n) K) *ᵥ v ≠ v := by
    by_contra hall
    push Not at hall
    apply hX1
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hall, Units.val_one, Matrix.one_mulVec]
  obtain ⟨c, d, hcc, hdd, hcd, hcomm, hzc, u, hzu, hMu, hMMu⟩ :=
    exists_zMat h hMiso hM3 hω hω1 hσω hn hv
  refine ⟨zGL h hω hcd, zGL_mem h hω hσω hcc hdd hcd, zGL_pow_three h hω hcc hdd hcd, ?_, ?_, ?_,
    ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_zGL]
    exact hcomm.symm
  · intro h1
    apply hzc
    rw [← coe_zGL h hω hcd, h1, Units.val_one, Matrix.one_mulVec]
  · intro h1
    apply hMu
    rw [← h1, coe_zGL, hzu]
  · intro h1
    apply hMMu
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← sq, ← h1, coe_zGL, hzu]

theorem exists_commuting_three_uP4 (hf : Even f) (x : uP h 4) (hx : orderOf x = 3) :
    ∃ z : uP h 4, orderOf z = 3 ∧ z * x = x * z ∧ z ∉ Subgroup.zpowers x := by
  classical
  have hZ : uZ h 4 = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num)]
    have h1 := Nat.Coprime.pow_right 2 (coprime_two_pow_add_one hf h.one_le).1
    rw [Nat.coprime_comm] at h1
    exact h1
  have hπ : Function.Injective (QuotientGroup.mk' (uZ h 4)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  obtain ⟨X, rfl⟩ := QuotientGroup.mk'_surjective (uZ h 4) x
  have hX3 : X ^ 3 = 1 := hπ (by rw [map_pow, ← hx, pow_orderOf_eq_one, map_one])
  have hX1 : X ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hx
    norm_num at hx
  have hXS3 : (X : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hX3, Subgroup.coe_one]
  have hXS1 : (X : GL (Fin 4) K) ≠ 1 := fun h1 => hX1 (Subtype.ext h1)
  obtain ⟨Z, hZS, hZ3, hZX, hZ1, hZX1, hZX2⟩ := exists_commuting_three h hf le_rfl X.2 hXS3 hXS1
  refine ⟨QuotientGroup.mk' (uZ h 4) ⟨Z, hZS⟩, ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · rw [← map_pow]
      have : (⟨Z, hZS⟩ : uS h 4) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZ3)
      rw [this, map_one]
    · intro h1
      apply hZ1
      have h2 := hπ (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hZX
  · intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← map_zpow] at hi
    have hmem' : (⟨Z, hZS⟩ : uS h 4) ∈ Subgroup.zpowers X :=
      Subgroup.mem_zpowers_iff.mpr ⟨i, hπ hi⟩
    rw [← mem_powers_iff_mem_zpowers] at hmem'
    obtain ⟨k, hk⟩ := hmem'
    change X ^ k = _ at hk
    have hXord : orderOf X = 3 := orderOf_eq_prime hX3 hX1
    rw [← pow_mod_orderOf, hXord] at hk
    obtain ⟨r, hr⟩ : ∃ r, k % 3 = r := ⟨_, rfl⟩
    have hr3 : r < 3 := hr ▸ Nat.mod_lt _ (by norm_num)
    rw [hr] at hk
    have hk' : (X : GL (Fin 4) K) ^ r = Z := by
      rw [← Subgroup.coe_pow, hk]
    interval_cases r
    · exact hZ1 (by rw [← hk', pow_zero])
    · exact hZX1 (by rw [← hk', pow_one])
    · exact hZX2 hk'.symm

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

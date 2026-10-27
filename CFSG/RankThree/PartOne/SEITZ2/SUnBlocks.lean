module

public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.RankThree.PartOne.SEITZ2.EmbVec
public import CFSG.RankThree.PartOne.SEITZ2.SUnPlane

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.CTP (u2 l2)

section Emb

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

theorem pi_single_mem {k : Subfield K} {n : ℕ} (j i : Fin n) {c : K} (hc : c ∈ k) :
    (Pi.single j c : Fin n → K) i ∈ k := by
  rcases eq_or_ne i j with rfl | h
  · simpa using hc
  · rw [Pi.single_eq_of_ne h]
    exact k.zero_mem

theorem embVec_isRat {k : Subfield K} {i : ℕ} {v : Fin 2 → K} (hv : ∀ x, v x ∈ k) :
    ∀ l : Fin m, embVec m i v l ∈ k := by
  intro l
  simp only [embVec]
  split_ifs
  · exact hv 0
  · exact hv 1
  · exact k.zero_mem

end Emb

section Block

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem isTv_blockEmb2 {n : ℕ} (i : Fin n) {X : Su K 2 f 2} {c : Fin 2 → K} {b : K}
    (hX : IsTv (unitaryInvolution K 2 f) X c b) :
    IsTv (unitaryInvolution K 2 f) (blockEmb2 K 2 f n i X) (embVec (n + 1) i c) b := by
  have h2 : (i : ℕ) + 2 ≤ n + 1 := by omega
  intro v
  rw [smul_def]
  funext l
  by_cases hl : (i : ℕ) ≤ l.val ∧ l.val < i + 2
  · obtain ⟨x, rfl⟩ : ∃ x : Fin 2, blockIdx i h2 x = l :=
      ⟨⟨l.val - i, by omega⟩, Fin.ext (by simp [blockIdx]; omega)⟩
    show (blockMat (n + 1) i ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
      (blockIdx i h2 x) = _
    rw [blockMat_mulVec_blockIdx h2]
    have := congrFun (hX (fun y => v (blockIdx i h2 y))) x
    rw [smul_def] at this
    rw [this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, embVec_blockIdx h2,
      herm_embVec_left h2]
  · show (blockMat (n + 1) i ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) l = _
    rw [blockMat_mulVec_of_not_mem _ _ hl, Pi.add_apply, Pi.smul_apply, embVec_of_not_mem c hl]
    simp

end Block

section Planes

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

omit [Finite K] in
theorem exists_mem_range_isTv_embVec (hσ : IsUnitaryInvolution σ) {m i : ℕ}
    {a₂ b₂ : Fin 2 → K} (ha₂ : herm σ a₂ a₂ = 0) (hb₂ : herm σ b₂ b₂ = 0)
    (hab₂ : herm σ a₂ b₂ = 1)
    (hexp : ∀ v : Fin 2 → K, v = herm σ b₂ v • a₂ + herm σ a₂ v • b₂)
    (ha : herm σ (embVec m i a₂) (embVec m i a₂) = 0)
    (hb : herm σ (embVec m i b₂) (embVec m i b₂) = 0)
    (hab : herm σ (embVec m i a₂) (embVec m i b₂) = 1)
    {c' : Fin 2 → K} (hc' : herm σ c' c' = 0) {c : K} (hc : σ c = c) :
    ∃ g ∈ (planeSUN hσ.invol ha hb hab).range, IsTv σ g (embVec m i c') c := by
  classical
  have hσi := hσ.invol
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set a := embVec m i a₂ with ha_def
  set b := embVec m i b₂ with hb_def
  set Θ := planeSUN hσi ha hb hab with hΘ
  set s := herm σ b₂ c' with hs
  set t := herm σ a₂ c' with ht
  have hba₂ : herm σ b₂ a₂ = 1 := by rw [herm_conj σ hσi, hab₂, map_one]
  have hc'exp : c' = s • a₂ + t • b₂ := hexp c'
  have hemb : embVec m i c' = s • a + t • b := by
    conv_lhs => rw [hc'exp]
    rw [embVec_add, embVec_smul, embVec_smul]
  have hiso : σ s * t + σ t * s = 0 := by
    have h0 := hc'
    rw [hc'exp] at h0
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, ha₂, hb₂, hab₂,
      hba₂] at h0
    linear_combination h0
  have hfix : ∀ x : K, σ x = x → x ∈ fixSub σ := fun x hx => mem_fixSub.2 hx
  have hNfix : ∀ x : K, σ (c * (σ x * x)) = c * (σ x * x) := fun x => by
    rw [map_mul, map_mul, hc, hσi]
    ring
  by_cases ht0 : t = 0
  ·
    have hemb0 : embVec m i c' = s • a := by rw [hemb, ht0]; simp
    refine ⟨Θ (u2 ⟨c * (σ s * s), hfix _ (hNfix s)⟩), ⟨_, rfl⟩, ?_⟩
    rw [hemb0, isTv_smul_vec]
    exact isTv_planeSUN_u2 hσi ha hb hab ⟨c * (σ s * s), hfix _ (hNfix s)⟩
  · have hσt0 : σ t ≠ 0 := (map_ne_zero σ).2 ht0
    have hst : σ s * t = σ t * s := by linear_combination hiso - (σ t * s) * h2
    have hu : σ (s / t) = s / t := by
      rw [map_div₀, div_eq_div_iff hσt0 ht0]
      linear_combination hst
    have hts : t * (s / t) = s := by field_simp
    have hb1 : Θ (u2 ⟨s / t, hfix _ hu⟩) • b = (s / t) • a + b := by
      have := isTv_planeSUN_u2 hσi ha hb hab ⟨s / t, hfix _ hu⟩ b
      rw [this, hab, mul_one, add_comm]
    refine ⟨Θ (u2 ⟨s / t, hfix _ hu⟩) * Θ (l2 ⟨c * (σ t * t), hfix _ (hNfix t)⟩) *
      (Θ (u2 ⟨s / t, hfix _ hu⟩))⁻¹, ?_, ?_⟩
    · rw [← map_inv, ← map_mul, ← map_mul]
      exact ⟨_, rfl⟩
    · have h1 := (isTv_planeSUN_l2 hσi ha hb hab ⟨c * (σ t * t), hfix _ (hNfix t)⟩).conj
        (Θ (u2 ⟨s / t, hfix _ hu⟩))
      rw [hb1] at h1
      have h3 : embVec m i c' = t • ((s / t) • a + b) := by
        rw [hemb, smul_add, smul_smul, hts]
      rw [h3, isTv_smul_vec]
      exact h1

end Planes

section Generation

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem range_blockEmb2_le (hσ : IsUnitaryInvolution (unitaryInvolution K 2 f)) {n : ℕ}
    (i : Fin n) {a₂ b₂ : Fin 2 → K} (ha₂ : herm (unitaryInvolution K 2 f) a₂ a₂ = 0)
    (hb₂ : herm (unitaryInvolution K 2 f) b₂ b₂ = 0)
    (hab₂ : herm (unitaryInvolution K 2 f) a₂ b₂ = 1)
    (hexp : ∀ v : Fin 2 → K, v = herm (unitaryInvolution K 2 f) b₂ v • a₂ +
      herm (unitaryInvolution K 2 f) a₂ v • b₂)
    (ha : herm (unitaryInvolution K 2 f) (embVec (n + 1) i a₂) (embVec (n + 1) i a₂) = 0)
    (hb : herm (unitaryInvolution K 2 f) (embVec (n + 1) i b₂) (embVec (n + 1) i b₂) = 0)
    (hab : herm (unitaryInvolution K 2 f) (embVec (n + 1) i a₂) (embVec (n + 1) i b₂) = 1)
    {M : Subgroup (Su K 2 f (n + 1))}
    (hM : (planeSUN hσ.invol ha hb hab).range ≤ M) : (blockEmb2 K 2 f n i).range ≤ M := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro _ ⟨X, rfl⟩
  have hT : X ∈ T (unitaryInvolution K 2 f) 2 := by
    rw [T_two_eq_top hσ]
    trivial
  induction hT using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨c', c, hc', hcσ, htv⟩ := ht
    have hσc : unitaryInvolution K 2 f c = c := by
      linear_combination hcσ - c * h2
    have h1 : IsTv (unitaryInvolution K 2 f) (blockEmb2 K 2 f n i t) (embVec (n + 1) i c') c :=
      isTv_blockEmb2 i htv
    obtain ⟨g, hg, hgtv⟩ := exists_mem_range_isTv_embVec hσ ha₂ hb₂ hab₂ hexp ha hb hab hc' hσc
    have : blockEmb2 K 2 f n i t = g := h1.unique hgtv
    rw [this]
    exact hM hg
  | one =>
    rw [map_one]
    exact M.one_mem
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact M.mul_mem hx hy
  | inv x _ hx =>
    rw [map_inv]
    exact M.inv_mem hx

theorem eq_top_of_blocks (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 2 ^ f ≠ 2) {n : ℕ}
    {M : Subgroup (Su K 2 f (n + 1))} (h : ∀ i : Fin n, (blockEmb2 K 2 f n i).range ≤ M) :
    M = ⊤ := by
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq n]
  exact iSup_le h

end Generation

end CFSG.RankThree.PartOne.SEITZ2

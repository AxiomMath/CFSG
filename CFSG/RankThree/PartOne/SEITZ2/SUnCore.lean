module

public import CFSG.RankThree.PartOne.SEITZ2.SUnPlane
public import CFSG.RankThree.PartOne.SEITZ2.SU3Core

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.RankThree.PartOne.CTP (u2 l2 sl2_eq_top_of_root_groups)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {n : ℕ}


theorem exists_isTv_fullN (hσ : IsUnitaryInvolution σ) {k : Subfield K} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    (hk4 : 4 ∣ Nat.card (ratFix σ k)) {a₀ b₀ : Fin n → K} (ha : herm σ a₀ a₀ = 0)
    (hb : herm σ b₀ b₀ = 0) (hab : herm σ a₀ b₀ = 1) (ha_rat : IsRat k a₀)
    {M : Subgroup (SUid σ n)}
    (hM_rat : ∀ a : Fin n → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c)
    (hM_trans : ∀ x x' : Fin n → K, IsRat k x → IsRat k x' → x ≠ 0 → x' ≠ 0 →
      herm σ x x = 0 → herm σ x' x' = 0 → ∃ r ∈ M, r • x = x')
    {y : Fin n → K} (hy : herm σ y y = 0)
    (hyM : ∀ c : K, c ∈ k → σ c = c → ∃ t ∈ M, IsTv σ t y c)
    {x : Fin n → K} (hx_rat : IsRat k x) (hx0 : x ≠ 0) (hx : herm σ x x = 0)
    (hxy : σ (herm σ x y) * herm σ x y ∉ k) :
    ∀ b : fixSub σ, ∃ t ∈ M, IsTv σ t a₀ (b : K) := by
  classical
  have hσi := hσ.invol
  have ha0 : a₀ ≠ 0 := fun h => by rw [h] at hab; simp at hab
  obtain ⟨r, hrM, hr⟩ := hM_trans x a₀ hx_rat ha_rat hx0 ha0 hx ha
  have hy' : herm σ (r • y) (r • y) = 0 := by rw [herm_smul_smul, hy]
  have hyM' : ∀ c : K, c ∈ k → σ c = c → ∃ t ∈ M, IsTv σ t (r • y) c := fun c hc hσc => by
    obtain ⟨t, htM, ht⟩ := hyM c hc hσc
    exact ⟨r * t * r⁻¹, M.mul_mem (M.mul_mem hrM htM) (M.inv_mem hrM), ht.conj r⟩
  have hη : herm σ a₀ (r • y) = herm σ x y := by rw [← hr, herm_smul_smul]
  have hNη : σ (herm σ a₀ (r • y)) * herm σ a₀ (r • y) ∉ k := by rw [hη]; exact hxy
  have hη0 : herm σ a₀ (r • y) ≠ 0 := fun h => hNη (by rw [h]; simp)
  obtain ⟨g, hga, hgy⟩ := exists_fix_smul_eq hσ ha hy' hb hη0 (by rw [hab]; exact one_ne_zero)
  rw [hab, div_one] at hgy
  set η := herm σ a₀ (r • y) with hηdef
  let aF : fixSub σ := ⟨σ η * η, mem_fixSub.2 (by rw [map_mul, hσi]; ring)⟩
  have haF : aF ∉ ratFix σ k := hNη
  let Θ := planeSUN hσi ha hb hab
  let S : Subgroup (SpecialLinearGroup (Fin 2) (fixSub σ)) :=
    (M.map (MulAut.conj g).toMonoidHom).comap Θ
  have hu : ∀ c ∈ ratFix σ k, u2 c ∈ S := by
    intro c hc
    obtain ⟨t, htM, ht⟩ := hM_rat a₀ ha_rat ha c (mem_ratFix.1 hc) (mem_fixSub.1 c.2)
    refine ⟨t, htM, ?_⟩
    have h1 := ht.conj g
    rw [hga] at h1
    exact h1.unique (isTv_planeSUN_u2 hσi ha hb hab c)
  have hl : ∀ c ∈ ratFix σ k, l2 (c * aF) ∈ S := by
    intro c hc
    obtain ⟨t, htM, ht⟩ := hyM' c (mem_ratFix.1 hc) (mem_fixSub.1 c.2)
    refine ⟨t, htM, ?_⟩
    have h1 := ht.conj g
    rw [hgy] at h1
    have h2 : IsTv σ (g * t * g⁻¹) b₀ ((c : K) * (σ η * η)) := isTv_smul_vec.1 h1
    have h3 := isTv_planeSUN_l2 hσi ha hb hab (c * aF)
    exact h2.unique (by simpa [aF] using h3)
  have hSt : S = ⊤ :=
    sl2_eq_top_of_root_lines hp hp2 hK hk4 haF hu hl
  intro b
  have hb' : u2 b ∈ S := hSt ▸ Subgroup.mem_top _
  obtain ⟨m, hmM, hm⟩ := hb'
  refine ⟨m, hmM, ?_⟩
  have h1 := (isTv_planeSUN_u2 hσi ha hb hab b).conj g⁻¹
  have h2 : g⁻¹ • a₀ = a₀ := inv_smul_eq_iff.2 hga.symm
  rw [h2] at h1
  have h3 : g⁻¹ * Θ (u2 b) * g⁻¹⁻¹ = m := by
    have : Θ (u2 b) = g * m * g⁻¹ := hm.symm
    rw [this]
    group
  rwa [h3] at h1

theorem range_planeSUN_le (hσ : IsUnitaryInvolution σ) {k : Subfield K} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    {a₀ b₀ : Fin n → K} (ha : herm σ a₀ a₀ = 0) (hb : herm σ b₀ b₀ = 0)
    (hab : herm σ a₀ b₀ = 1) (hb_rat : IsRat k b₀) {M : Subgroup (SUid σ n)}
    (hM_rat : ∀ a : Fin n → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c)
    (hfull : ∀ b : fixSub σ, ∃ t ∈ M, IsTv σ t a₀ (b : K)) :
    (planeSUN hσ.invol ha hb hab).range ≤ M := by
  classical
  have hσi := hσ.invol
  let Θ := planeSUN hσi ha hb hab
  obtain ⟨bb, hbb⟩ := exists_not_mem_ratFix (σ := σ) (k := k) hp.two_le hK
  have hu : ∀ b : fixSub σ, u2 b ∈ M.comap Θ := by
    intro b
    obtain ⟨t, htM, ht⟩ := hfull b
    have : Θ (u2 b) = t := (isTv_planeSUN_u2 hσi ha hb hab b).unique ht
    show Θ (u2 b) ∈ M
    rw [this]
    exact htM
  have hl : ∀ c ∈ ratFix σ k, l2 c ∈ M.comap Θ := by
    intro c hc
    obtain ⟨t, htM, ht⟩ := hM_rat b₀ hb_rat hb c (mem_ratFix.1 hc) (mem_fixSub.1 c.2)
    have : Θ (l2 c) = t := (isTv_planeSUN_l2 hσi ha hb hab c).unique ht
    show Θ (l2 c) ∈ M
    rw [this]
    exact htM
  have htop : M.comap Θ = ⊤ := by
    refine sl2_eq_top_of_root_groups (a₁ := 1) (a₂ := bb) (b₀ := 1) hp hp2 hK one_ne_zero
      (by simpa using hbb) one_ne_zero (fun c₁ _ c₂ _ => hu _) (hl 1 (ratFix σ k).one_mem)
  rintro _ ⟨X, rfl⟩
  have : X ∈ M.comap Θ := htop ▸ Subgroup.mem_top _
  exact this

end CFSG.RankThree.PartOne.SEITZ2

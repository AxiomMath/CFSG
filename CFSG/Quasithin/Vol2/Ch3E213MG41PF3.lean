module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PF2
public import CFSG.Quasithin.Vol2.Ch3E213MG41PF1

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] noncomputable def qvP (r s x : Fin 4 → k) : k :=
  (spBil x s / spBil r s) ^ 2 + (spBil x r / spBil r s) ^ 2 +
    spBil r s * (spBil x s / spBil r s) * (spBil x r / spBil r s)

omit [CharP k 2] in
theorem eq_prPL_add (r s x : Fin 4 → k) :
    x = (spBil x s / spBil r s) • r + (spBil x r / spBil r s) • s + prYL r s x := by
  rw [prYL_apply, prPL_apply]
  abel

omit [CharP k 2] in
theorem form_of_prYL (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {r s y : Fin 4 → k} (hr : Q r = 1)
    (hs : Q s = 1) (hyr : spBil y r = 0) (hys : spBil y s = 0) {x : Fin 4 → k} {l : k}
    (hx : prYL r s x = l • y) : Q x = qvP r s x + l ^ 2 * Q y := by
  have hxe : x = ((spBil x s / spBil r s) • r + (spBil x r / spBil r s) • s) + l • y := by
    conv_lhs => rw [eq_prPL_add r s x]
    rw [hx]
  have hpol := hQ ((spBil x s / spBil r s) • r + (spBil x r / spBil r s) • s) (l • y)
  rw [QuadraticMap.polar] at hpol
  have hp := form_smul_add Q hQ hr hs (spBil x s / spBil r s) (spBil x r / spBil r s)
  have hpy : spBil ((spBil x s / spBil r s) • r + (spBil x r / spBil r s) • s) (l • y) = 0 := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, map_smul, map_smul,
      bil_symm r y, bil_symm s y, hyr, hys]
    simp
  rw [hpy, QuadraticMap.map_smul, smul_eq_mul, ← hxe] at hpol
  rw [qvP]
  linear_combination hpol + hp

omit [CharP k 2] in
theorem form_add_smul (Q : QuadraticForm k (Fin 4 → k))
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spBil x y) {r s y : Fin 4 → k} (hr : Q r = 1)
    (hs : Q s = 1) (hyr : spBil y r = 0) (hys : spBil y s = 0) (a b l : k) :
    Q (a • r + b • s + l • y) = a ^ 2 + b ^ 2 + spBil r s * a * b + l ^ 2 * Q y := by
  have hpol := hQ (a • r + b • s) (l • y)
  rw [QuadraticMap.polar] at hpol
  have hp := form_smul_add Q hQ hr hs a b
  have hpy : spBil (a • r + b • s) (l • y) = 0 := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂, map_smul, map_smul,
      bil_symm r y, bil_symm s y, hyr, hys]
    simp
  rw [hpy, QuadraticMap.map_smul, smul_eq_mul] at hpol
  linear_combination hpol + hp

theorem homog_at [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)}
    (hone : Refl.OnePerCentre G₀)
    (hL4 : ∀ (G : Subgroup (antiSp k)) (F : Subfield k) (e e' : Fin 4 → k),
      Refl.OnePerCentre G → CaseB G F e e' →
      ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G, z 2 = 0 → proj z ≠ 0 → Q z = 1)
    {r s : Fin 4 → k} (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc : spBil r s ≠ 0)
    (hNoTwo : ∀ a b : k, a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0 → ∀ (π : Fin 4 → k) (l l' : k),
      π ∈ Refl.normC G₀ → spBil π r = 0 → spBil π s = 0 →
      a • r + b • s + l • π ∈ Refl.normC G₀ → a • r + b • s + l' • π ∈ Refl.normC G₀ → l = l')
    (hRatio : ∀ y : Fin 4 → k, spBil y r = 0 → spBil y s = 0 → ∀ t₀ μ ν : k,
      t₀ • y ∈ Refl.normC G₀ → μ • r + ν • y ∈ Refl.normC G₀ → ν = t₀ * (1 + μ))
    (Q₀ : QuadraticForm k (Fin 4 → k)) (hQ₀ : ∀ x y, QuadraticMap.polar Q₀ x y = spBil x y)
    (hQ₀r : Q₀ r = 1) (hQ₀s : Q₀ s = 1) {y : Fin 4 → k} (hy : y ≠ 0) (hyr : spBil y r = 0)
    (hys : spBil y s = 0) :
    ∃ D : k, ∀ x ∈ Refl.normC G₀, ∀ l : k, prYL r s x = l • y → Q₀ x + 1 = l ^ 2 * D := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hry : spBil r y = 0 := by rw [bil_symm]; exact hyr
  have hsy : spBil s y = 0 := by rw [bil_symm]; exact hys
  have hnot : ∀ x, spBil x s ≠ 0 ∨ spBil x r ≠ 0 → x ∉ k ∙ y := by
    intro x hx h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    rcases hx with h1 | h1
    · exact h1 (by rw [LinearMap.map_smul₂, hys, smul_zero])
    · exact h1 (by rw [LinearMap.map_smul₂, hyr, smul_zero])
  have hrn : r ∉ k ∙ y := hnot r (Or.inl hc)
  have hsn : s ∉ k ∙ y := hnot s (Or.inr (by rw [bil_symm]; exact hc))
  have hperp : ∀ x (l : k), prYL r s x = l • y → spBil x y = 0 := by
    intro x l hx
    rw [eq_prPL_add r s x, hx]
    simp only [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hry, hsy, smul_zero, add_zero]
  have hlsm : ∀ (t l : k), prYL r s (t • y) = l • y → l = t := fun t l h => by
    rw [prYL_of_perp (by rw [LinearMap.map_smul₂, hyr, smul_zero])
      (by rw [LinearMap.map_smul₂, hys, smul_zero])] at h
    exact (smul_left_injective k hy h).symm
  have hQ₀x : ∀ x (l : k), prYL r s x = l • y → Q₀ x = qvP r s x + l ^ 2 * Q₀ y :=
    fun x l hx => form_of_prYL Q₀ hQ₀ hQ₀r hQ₀s hyr hys hx
  rcases split_at hn hk hone hL4 hy hr hs hry hsy hc with ⟨⟨Q, hQ, hQy, hQ1⟩, hspan⟩ |
      ⟨⟨Q, hQ, hQy, hQ1⟩, ⟨F₁, hF₁, hcov⟩⟩
  · have hQr : Q r = 1 := hQ1 r hr hry hrn
    have hQs : Q s = 1 := hQ1 s hs hsy hsn
    have hQx : ∀ x (l : k), prYL r s x = l • y → Q x = qvP r s x := fun x l hx => by
      rw [form_of_prYL Q hQ hQr hQs hyr hys hx, hQy, mul_zero, add_zero]
    by_cases hR : ∃ t₀ : k, t₀ • y ∈ Refl.normC G₀
    · obtain ⟨t₀, ht₀⟩ := hR
      have ht₀0 : t₀ ≠ 0 := fun h => ht₀.1 (by rw [h, zero_smul])
      have hπr : spBil (t₀ • y) r = 0 := by rw [LinearMap.map_smul₂, hyr, smul_zero]
      have hπs : spBil (t₀ • y) s = 0 := by rw [LinearMap.map_smul₂, hys, smul_zero]
      have hfib : ∀ x ∈ Refl.normC G₀, ∀ x' ∈ Refl.normC G₀, spBil x y = 0 → x ∉ k ∙ y →
          x' - x ∈ k ∙ y → x' = x := by
        intro x hx x' hx' hxy hxn hdiff
        obtain ⟨a, b, l, hxe⟩ := exists_eq_add_smul hc hy hyr hys hxy
        obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hdiff
        have hx'e : x' = a • r + b • s + (l + m) • y := by
          rw [← sub_add_cancel x' x, ← hm, hxe, add_smul]
          abel
        have hqv : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0 := by
          have h1 := hQ1 x hx hxy hxn
          rw [hxe, form_add_smul Q hQ hQr hQs hyr hys, hQy, mul_zero, add_zero] at h1
          rw [h1]
          exact one_ne_zero
        have hl : l * t₀⁻¹ = (l + m) * t₀⁻¹ := by
          refine hNoTwo a b hqv (t₀ • y) _ _ ht₀ hπr hπs ?_ ?_
          · rw [smul_smul, mul_assoc, inv_mul_cancel₀ ht₀0, mul_one, ← hxe]
            exact hx
          · rw [smul_smul, mul_assoc, inv_mul_cancel₀ ht₀0, mul_one, ← hx'e]
            exact hx'
        have hm0 : m = 0 := by
          have h3 := mul_right_cancel₀ (inv_ne_zero ht₀0) hl
          linear_combination -h3
        rw [hx'e, hxe, hm0, add_zero]
      refine ⟨Q₀ y + t₀⁻¹ ^ 2, fun x hx l hxl => ?_⟩
      by_cases hxn : x ∈ k ∙ y
      · obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hxn
        have hμ : μ = t₀ := by
          have h1 : (μ * t₀⁻¹) • (t₀ • y) ∈ Refl.normC G₀ := by
            rw [smul_smul, mul_assoc, inv_mul_cancel₀ ht₀0, mul_one]
            exact hx
          exact (mul_inv_eq_one₀ ht₀0).mp (Refl.eq_one_of_smul_mem hone ht₀ h1)
        rw [hlsm μ l hxl, hμ, QuadraticMap.map_smul, smul_eq_mul, mul_add, ← mul_pow,
          mul_inv_cancel₀ ht₀0, one_pow]
        ring
      · obtain ⟨α, β, hαβ⟩ := hspan hfib x hx (hperp x l hxl) hxn
        have hl : l = 0 := by
          rw [hαβ, prYL_smul_add hc] at hxl
          exact (smul_eq_zero.mp hxl.symm).resolve_right hy
        have h1 := hQ1 x hx (hperp x l hxl) hxn
        rw [hQx x l hxl] at h1
        rw [hQ₀x x l hxl, h1, hl]
        linear_combination h2
    · refine ⟨Q₀ y, fun x hx l hxl => ?_⟩
      have hxn : x ∉ k ∙ y := fun h => by
        obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp h
        exact hR ⟨μ, hx⟩
      have h1 := hQ1 x hx (hperp x l hxl) hxn
      rw [hQx x l hxl] at h1
      rw [hQ₀x x l hxl, h1]
      linear_combination h2
  · have hQr : Q r = 1 := hQ1 r hr hry hrn
    have hQs : Q s = 1 := hQ1 s hs hsy hsn
    refine ⟨Q₀ y + Q y, fun x hx l hxl => ?_⟩
    by_cases hxn : x ∈ k ∙ y
    · obtain ⟨t₀, rfl⟩ := Submodule.mem_span_singleton.mp hxn
      obtain ⟨μ, hμ, hμ0, hμ1⟩ := exists_mem_ne_ne (by omega : 3 ≤ Nat.card F₁) 0 1
      obtain ⟨x', hx', hdiff⟩ := hcov r hr hry hrn μ hμ hμ0
      obtain ⟨ν, hν⟩ := Submodule.mem_span_singleton.mp hdiff
      have hx'e : x' = μ • r + ν • y := by
        rw [← sub_add_cancel x' (μ • r), ← hν]
        abel
      have hx'e0 : x' = μ • r + (0 : k) • s + ν • y := by rw [hx'e, zero_smul, add_zero]
      have hx's : spBil x' s ≠ 0 := by
        rw [hx'e]
        simp only [LinearMap.map_add₂, LinearMap.map_smul₂, hys, smul_eq_mul, mul_zero, add_zero]
        exact mul_ne_zero hμ0 hc
      have hx'y : spBil x' y = 0 := by
        rw [hx'e]
        simp only [LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hry, smul_eq_mul, mul_zero,
          add_zero]
      have hQx' := hQ1 x' hx' hx'y (hnot x' (Or.inl hx's))
      have hνt : ν = t₀ * (1 + μ) := hRatio y hyr hys t₀ μ ν hx (by rw [← hx'e]; exact hx')
      rw [hx'e0, form_add_smul Q hQ hQr hQs hyr hys, hνt] at hQx'
      have h1μ : 1 + μ ≠ 0 := fun h => hμ1 (by linear_combination h - h2)
      have h3 : (1 + μ) ^ 2 * (t₀ ^ 2 * Q y - 1) = 0 := by
        linear_combination hQx' + (-μ - μ ^ 2) * h2
      have hκ : t₀ ^ 2 * Q y = 1 :=
        sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 h1μ))
      rw [hlsm t₀ l hxl, QuadraticMap.map_smul, smul_eq_mul]
      linear_combination -hκ
    · have h1 := hQ1 x hx (hperp x l hxl) hxn
      rw [form_of_prYL Q hQ hQr hQs hyr hys hxl] at h1
      rw [hQ₀x x l hxl]
      linear_combination h1 + (1 - l ^ 2 * Q y) * h2

end CFSG.Quasithin.Ch3E213M.G41.Big

module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PF5
public import CFSG.Quasithin.Vol2.Ch3E213MG41PE8
public import CFSG.Quasithin.Vol2.Ch3E213MG41PF4

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

theorem sectionSplit_of_L4 [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)}
    (hone : Refl.OnePerCentre G₀)
    (hL4 : ∀ (G : Subgroup (antiSp k)) (F : Subfield k) (e e' : Fin 4 → k),
      Refl.OnePerCentre G → CaseB G F e e' →
      ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G, z 2 = 0 → proj z ≠ 0 → Q z = 1) :
    SectionSplit G₀ := by
  intro ρ x w hρ hx hw hxρ hwρ hwx
  right
  have hxw : spBil x w ≠ 0 := by rwa [bil_symm]
  obtain ⟨Q, hQ, hQ1⟩ : ∃ Q : QuadraticForm k (Fin 4 → k),
      (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        ∀ u ∈ Refl.normC G₀, spBil u ρ = 0 → u ∉ k ∙ ρ → Q u = 1 := by
    rcases split_at hn hk hone hL4 hρ hx hw hxρ hwρ hxw with ⟨⟨Q, hQ, -, hQ1⟩, -⟩ |
        ⟨⟨Q, hQ, -, hQ1⟩, -⟩
    · exact ⟨Q, hQ, hQ1⟩
    · exact ⟨Q, hQ, hQ1⟩
  refine ⟨Q, fun a b _ _ => ?_, fun c a _ => ?_, hQ1⟩
  · have h := hQ a b
    rw [QuadraticMap.polar] at h
    linear_combination h
  · rw [QuadraticMap.map_smul, smul_eq_mul, sq]

omit [CharP k 2] in
theorem three_le_card [Finite k] {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) : 3 ≤ Nat.card k := by
  let f : Fin 3 → k := ![0, 1, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> simp_all [eq_comm]
  have h := Nat.card_le_card_of_injective f hf
  simpa using h

theorem exists_card_two_pow [Finite k] {c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card k = 2 ^ n := by
  classical
  let _ := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  have h3 := three_le_card hc0 hc1
  rw [Nat.card_eq_fintype_card, hn] at h3
  refine ⟨n, ?_, by rw [Nat.card_eq_fintype_card, hn]⟩
  by_contra h
  have hn1 : (n : ℕ) ≤ 1 := by omega
  have : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
  omega

theorem factSp4ReflBig_of_L4
    (hL4 : ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (G : Subgroup (antiSp k)) (F : Subfield k)
      (e e' : Fin 4 → k), Refl.OnePerCentre G → CaseB G F e e' →
      ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
        Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G, z 2 = 0 → proj z ≠ 0 → Q z = 1) :
    FactSp4ReflBig := by
  intro k _ _ _ G₀ hirr hD hone ⟨r, s, hr1, hs1, hc0, hc1⟩
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hone' : Refl.OnePerCentre G₀ := hone
  have hr : r ∈ Refl.normC G₀ := ⟨fun h => hc0 (by rw [h]; simp), hr1⟩
  have hs : s ∈ Refl.normC G₀ := ⟨fun h => hc0 (by rw [h, map_zero]), hs1⟩
  obtain ⟨n, hn, hk⟩ := exists_card_two_pow hc0 hc1
  have hL4k := hL4 k
  have hS := sectionSplit_of_L4 hn hk hone' hL4k
  have hq : (1 : k) ^ 2 + 0 ^ 2 + spBil r s * 1 * 0 ≠ 0 := by simp
  have hrP : r = (1 : k) • r + (0 : k) • s := by rw [one_smul, zero_smul, add_zero]
  have hNoTwo : ∀ a b : k, a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0 → ∀ (π : Fin 4 → k) (l l' : k),
      π ∈ Refl.normC G₀ → spBil π r = 0 → spBil π s = 0 →
      a • r + b • s + l • π ∈ Refl.normC G₀ → a • r + b • s + l' • π ∈ Refl.normC G₀ → l = l' :=
    fun a b hab π l l' hπ hπr hπs h₁ h₂ =>
      no_two_lifts hS hone' hirr hr hs hc0 hc1 hab rfl hπ hπr hπs h₁ h₂
  have hRatio : ∀ y : Fin 4 → k, spBil y r = 0 → spBil y s = 0 → ∀ t₀ μ ν : k,
      t₀ • y ∈ Refl.normC G₀ → μ • r + ν • y ∈ Refl.normC G₀ → ν = t₀ * (1 + μ) :=
    fun y hyr hys t₀ μ ν ht₀ hz =>
      ratio_eq_of_zero hS hone' hirr hr hs hc0 hc1 hq hrP hr hyr hys ht₀ hz
  have hL4' : ∀ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) →
      (∀ u ∈ Refl.normC G₀, spBil u r = 0 → u ∉ k ∙ r → Q u = 1) → ∀ F₁ : Subfield k,
      4 ≤ Nat.card F₁ → ∀ x₀ ∈ Refl.normC G₀, spBil x₀ r = 0 → x₀ ∉ k ∙ r →
      (∀ μ ∈ F₁, μ ≠ 0 → ∃ x' ∈ Refl.normC G₀, x' - μ • x₀ ∈ k ∙ r) → Q r = 1 :=
    fun Q hpol hQ1 F₁ hF₁ x₀ _ hx₀r hx₀n hcov =>
      quad_eq_one_at hS hone' hirr hr hs hc0 hc1 hq hrP hr Q hpol hQ1 hF₁ hx₀r hx₀n hcov
  obtain ⟨Q₀, hQ₀, hQ₀r, hQ₀s⟩ := exists_form_one hc0
  obtain ⟨ℓ, hℓ⟩ := exists_linear_YO hn hk hone' hL4k hr hs hc0 hNoTwo hRatio hL4' Q₀ hQ₀ hQ₀r
    hQ₀s
  obtain ⟨y₀, hy₀, hy₀r, hy₀s⟩ := exists_perp_ne_zero hc0
  obtain ⟨D₀, hD₀⟩ := homog_at hn hk hone' hL4k hr hs hc0 hNoTwo hRatio Q₀ hQ₀ hQ₀r hQ₀s hy₀
    hy₀r hy₀s
  refine Refl.orthW_of_forall (Refl.span_normC hirr hD)
    (Q₀ + QuadraticMap.linMulLin (ℓ.comp (prYL r s)) (ℓ.comp (prYL r s))) (fun x y => ?_)
    (fun x hx => ?_)
  · rw [FunLike.coe_add, QuadraticMap.polar_add, hQ₀]
    have h0 : QuadraticMap.polar
        (QuadraticMap.linMulLin (ℓ.comp (prYL r s)) (ℓ.comp (prYL r s))) x y = 0 := by
      simp only [QuadraticMap.polar, QuadraticMap.linMulLin_apply, map_add]
      linear_combination (ℓ.comp (prYL r s) x * ℓ.comp (prYL r s) y) * h2
    rw [h0, add_zero]
  rw [add_apply, QuadraticMap.linMulLin_apply, LinearMap.comp_apply]
  by_cases hY : prYL r s x = 0
  · have e := hD₀ x hx 0 (by rw [hY, zero_smul])
    rw [hY, map_zero]
    linear_combination e - h2
  · obtain ⟨μ, hμ0, x', hx', hx'r, hx'Y⟩ := exists_smul_mem_YO hn hk hone' hL4k hr hs hc0 hx hY
    obtain ⟨D, hD⟩ := homog_at hn hk hone' hL4k hr hs hc0 hNoTwo hRatio Q₀ hQ₀ hQ₀r hQ₀s hY
      (bil_prYL_left hc0 x) (bil_prYL_right hc0 x)
    have e1 := hD x hx 1 (one_smul _ _).symm
    have e2 := hD x' hx' μ hx'Y
    have e3 := hℓ x' hx' hx'r
    rw [hx'Y, map_smul, smul_eq_mul] at e3
    have hDℓ : D = ℓ (prYL r s x) ^ 2 := by
      have h3 : μ ^ 2 * (D - ℓ (prYL r s x) ^ 2) = 0 := by linear_combination -e2 + e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 hμ0))
    rw [hDℓ] at e1
    linear_combination e1 + (ℓ (prYL r s x) ^ 2 - 1) * h2

end CFSG.Quasithin.Ch3E213M.G41.Big

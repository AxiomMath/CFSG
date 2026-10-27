module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PE2
public import CFSG.Quasithin.Vol2.Ch3E213MG41PE5
public import CFSG.Quasithin.Vol2.Ch3E213MG41PE4

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

namespace IPL

theorem coord_eq_zero {r s : Fin 4 → k} (hc : spBil r s ≠ 0) {a b : k}
    (hr' : spBil (a • r + b • s) r = 0) (hs' : spBil (a • r + b • s) s = 0) : a = 0 ∧ b = 0 := by
  have hsr : spBil s r = spBil r s := bil_symm s r
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, bil_self,
    hsr, mul_zero, zero_add, add_zero] at hr' hs'
  exact ⟨(mul_eq_zero.mp hs').resolve_right hc, (mul_eq_zero.mp hr').resolve_right hc⟩

omit [CharP k 2] in
theorem bil_coord_perp {r s y : Fin 4 → k} (hyr : spBil y r = 0) (hys : spBil y s = 0)
    (a b : k) : spBil (a • r + b • s) y = 0 := by
  simp [map_add, map_smul, bil_symm r y, bil_symm s y, hyr, hys]

theorem add_smul_not_mem {r s : Fin 4 → k} (hc : spBil r s ≠ 0) {a b : k} {ρ₀ y : Fin 4 → k}
    (hρ₀P : ρ₀ = a • r + b • s) (hy : y ≠ 0) (hyr : spBil y r = 0) (hys : spBil y s = 0)
    (a' : k) {m : k} (hm : m ≠ 0) : a' • ρ₀ + m • y ∉ k ∙ ρ₀ := by
  intro hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have hy' : y = ((t - a') / m * a) • r + ((t - a') / m * b) • s := by
    have hmy : m • y = (t - a') • ρ₀ := by rw [sub_smul, ht]; abel
    calc y = m⁻¹ • (m • y) := by rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
      _ = _ := by
        rw [hmy, hρ₀P, smul_smul, smul_add, smul_smul, smul_smul, div_eq_mul_inv]
        congr 2 <;> ring
  obtain ⟨h1, h2⟩ := coord_eq_zero hc (hy' ▸ hyr) (hy' ▸ hys)
  exact hy (by rw [hy', h1, h2, zero_smul, zero_smul, add_zero])

theorem eq_div_of_add_eq_zero {a₁ b₁ h X : k} (ha : a₁ ≠ 0) (e : a₁ * X + b₁ * h = 0) :
    X = b₁ * h / a₁ := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [eq_div_iff ha]
  linear_combination e - (b₁ * h) * h0

theorem bil_rotP_inv {r s π : Fin 4 → k} (hπr : spBil π r = 0) (hπs : spBil π s = 0)
    (w : Fin 4 → k) (a b a' b' : k) (j : ℕ) :
    spBil (natAct (rotP r s ^ j)⁻¹ w) (a' • (a • r + b • s) + b' • π) =
      a' * (spBil w r * ((rotC (spBil r s))^[j] (a, b)).1 +
        spBil w s * ((rotC (spBil r s))^[j] (a, b)).2) + b' * spBil w π := by
  rw [bil_act_inv, act_add, act_smul, act_smul, act_rotP_pow_of_perp hπr hπs,
    show a • r + b • s = (a, b).1 • r + (a, b).2 • s from rfl, act_rotP_pow]
  simp only [map_add, map_smul, smul_eq_mul]
  ring

end IPL

theorem exists_w' [Finite k] (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)))
    {r s : Fin 4 → k} (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀)
    (hc0 : spBil r s ≠ 0) (hc1 : spBil r s ≠ 1) {a b : k}
    (hq : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0) {π : Fin 4 → k} (hπ : π ≠ 0)
    (hπr : spBil π r = 0) (hπs : spBil π s = 0) {a₁ b₁ a₂ b₂ : k} (ha₁ : a₁ ≠ 0)
    (ha₂ : a₂ ≠ 0) :
    ∃ w' ∈ Refl.normC G₀, spBil w' π ≠ 0 ∧ spBil w' (a₁ • (a • r + b • s) + b₁ • π) ≠ 0 ∧
      spBil w' (a₂ • (a • r + b • s) + b₂ • π) ≠ 0 := by
  obtain ⟨w, hw, hwπ, hwP⟩ := IPL.exists_w hirr hc0 hπ hπr hπs
  have hv : IPL.qC (spBil r s) (a, b) ≠ 0 := hq
  have bad : ∀ a' b' : k, a' ≠ 0 → ∀ i j l, i < 5 → j < 5 → l < 5 →
      spBil (natAct (IPL.rotP r s ^ i)⁻¹ w) (a' • (a • r + b • s) + b' • π) = 0 →
      spBil (natAct (IPL.rotP r s ^ j)⁻¹ w) (a' • (a • r + b • s) + b' • π) = 0 →
      spBil (natAct (IPL.rotP r s ^ l)⁻¹ w) (a' • (a • r + b • s) + b' • π) = 0 →
      i = j ∨ i = l ∨ j = l := by
    intro a' b' ha' i j l hi hj hl h₁ h₂ h₃
    rw [IPL.bil_rotP_inv hπr hπs] at h₁ h₂ h₃
    exact IPL.orbit_line hc0 hc1 hv hwP _ i j l hi hj hl (IPL.eq_div_of_add_eq_zero ha' h₁)
      (IPL.eq_div_of_add_eq_zero ha' h₂) (IPL.eq_div_of_add_eq_zero ha' h₃)
  obtain ⟨j, -, h₁, h₂⟩ := IPL.exists_lt_five_not (bad a₁ b₁ ha₁) (bad a₂ b₂ ha₂)
  refine ⟨natAct (IPL.rotP r s ^ j)⁻¹ w,
    Refl.act_mem_normC hw (G₀.inv_mem (G₀.pow_mem (IPL.rotP_mem hr hs) j)), ?_, h₁, h₂⟩
  rw [bil_act_inv, IPL.act_rotP_pow_of_perp hπr hπs]
  exact hwπ

theorem IPL.ratio_of_w (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀) {r s : Fin 4 → k}
    (hc0 : spBil r s ≠ 0) {a b : k} {ρ₀ y w : Fin 4 → k} (hρ₀P : ρ₀ = a • r + b • s)
    (hρ₀ : ρ₀ ∈ Refl.normC G₀) (hy : y ≠ 0) (hyr : spBil y r = 0) (hys : spBil y s = 0)
    (hw : w ∈ Refl.normC G₀) {a₁ a₂ m₁ m₂ : k} (hm₁ : m₁ ≠ 0)
    (hz₁ : a₁ • ρ₀ + m₁ • y ∈ Refl.normC G₀) (hz₂ : a₂ • ρ₀ + m₂ • y ∈ Refl.normC G₀)
    (hw₀ : spBil w ρ₀ ≠ 0) (hw₁ : spBil w (a₁ • ρ₀ + m₁ • y) ≠ 0)
    (hw₂ : spBil w (a₂ • ρ₀ + m₂ • y) ≠ 0) : (1 + a₁) * m₂ = (1 + a₂) * m₁ := by
  have h0 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hρy : spBil ρ₀ y = 0 := by rw [hρ₀P]; exact IPL.bil_coord_perp hyr hys a b
  have hxy : spBil ρ₀ (a₁ • ρ₀ + m₁ • y) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, bil_self, hρy, mul_zero, add_zero]
  have hne : ρ₀ ≠ a₁ • ρ₀ + m₁ • y := fun h =>
    IPL.add_smul_not_mem hc0 hρ₀P hy hyr hys a₁ hm₁ (h ▸ Submodule.mem_span_singleton_self ρ₀)
  have hz : a₂ • ρ₀ + m₂ • y = (a₂ - a₁ * m₂ / m₁) • ρ₀ + (m₂ / m₁) • (a₁ • ρ₀ + m₁ • y) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have key := ipl hS hone hρ₀ hz₁ hz₂ hw hxy hne hz hw₀ hw₁ hw₂
  have key' : (a₂ - a₁ * m₂ / m₁ + m₂ / m₁) * m₁ = 1 * m₁ := by rw [key]
  rw [add_mul, sub_mul, div_mul_cancel₀ _ hm₁, div_mul_cancel₀ _ hm₁, one_mul] at key'
  linear_combination key' + (a₁ * m₂ - a₂ * m₁) * h0

theorem no_two_lifts [Finite k] (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀)
    (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀))) {r s : Fin 4 → k}
    (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc0 : spBil r s ≠ 0)
    (hc1 : spBil r s ≠ 1) {a b : k} (hq : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0)
    {p π : Fin 4 → k} (hp : p = a • r + b • s) (hπ : π ∈ Refl.normC G₀)
    (hπr : spBil π r = 0) (hπs : spBil π s = 0) {l l' : k}
    (h₁ : p + l • π ∈ Refl.normC G₀) (h₂ : p + l' • π ∈ Refl.normC G₀) : l = l' := by
  obtain ⟨w, hw, hwπ, hw₁, hw₂⟩ := exists_w' (b₁ := l) (b₂ := l') hirr hr hs hc0 hc1 hq hπ.1
    hπr hπs one_ne_zero one_ne_zero
  rw [one_smul, ← hp] at hw₁ hw₂
  have hπp : spBil π p = 0 := by
    rw [bil_symm, hp]
    exact IPL.bil_coord_perp hπr hπs a b
  have hxy : spBil π (p + l • π) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, hπp, bil_self, mul_zero, add_zero]
  have hne : π ≠ p + l • π := by
    intro h
    have hp' : p = (1 - l) • π := by rw [sub_smul, one_smul, eq_sub_iff_add_eq, ← h]
    obtain ⟨ha, hb⟩ := IPL.coord_eq_zero hc0 (a := a) (b := b)
      (by rw [← hp, hp', map_smul, LinearMap.smul_apply, hπr, smul_zero])
      (by rw [← hp, hp', map_smul, LinearMap.smul_apply, hπs, smul_zero])
    exact hq (by rw [ha, hb]; ring)
  have hz : p + l' • π = (l' - l) • π + (1 : k) • (p + l • π) := by
    rw [one_smul, sub_smul]
    abel
  have key := ipl hS hone hπ h₁ h₂ hw hxy hne hz hwπ hw₁ hw₂
  linear_combination -key

theorem ratio_eq_of_zero [Finite k] (hS : SectionSplit G₀) (hone : Refl.OnePerCentre G₀)
    (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀))) {r s : Fin 4 → k}
    (hr : r ∈ Refl.normC G₀) (hs : s ∈ Refl.normC G₀) (hc0 : spBil r s ≠ 0)
    (hc1 : spBil r s ≠ 1) {a b : k} (hq : a ^ 2 + b ^ 2 + spBil r s * a * b ≠ 0)
    {ρ₀ : Fin 4 → k} (hρ₀P : ρ₀ = a • r + b • s) (hρ₀ : ρ₀ ∈ Refl.normC G₀) {y : Fin 4 → k}
    (hyr : spBil y r = 0) (hys : spBil y s = 0) {t₀ μ ν : k} (ht₀ : t₀ • y ∈ Refl.normC G₀)
    (hz : μ • ρ₀ + ν • y ∈ Refl.normC G₀) : ν = t₀ * (1 + μ) := by
  have hy0 : y ≠ 0 := fun h => ht₀.1 (by rw [h, smul_zero])
  have ht0 : t₀ ≠ 0 := fun h => ht₀.1 (by rw [h, zero_smul])
  by_cases hμ : μ = 0
  · rw [hμ, zero_smul, zero_add] at hz
    have h1 : ν / t₀ = 1 := Refl.eq_one_of_smul_mem hone ht₀
      (by rwa [smul_smul, div_mul_cancel₀ _ ht0])
    rw [(div_eq_one_iff_eq ht0).mp h1, hμ, add_zero, mul_one]
  · obtain ⟨w, hw, hwy, hw₀, hw₁⟩ := exists_w' (b₁ := 0) (b₂ := ν) hirr hr hs hc0 hc1 hq hy0
      hyr hys one_ne_zero hμ
    rw [one_smul, zero_smul, add_zero, ← hρ₀P] at hw₀
    rw [← hρ₀P] at hw₁
    have key := IPL.ratio_of_w hS hone hc0 hρ₀P hρ₀ hy0 hyr hys hw (a₁ := 0) ht0
      (by rwa [zero_smul, zero_add]) hz hw₀
      (by rw [zero_smul, zero_add, map_smul, smul_eq_mul]; exact mul_ne_zero ht0 hwy) hw₁
    linear_combination key

end CFSG.Quasithin.Ch3E213M.G41.Big

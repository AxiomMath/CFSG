module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Syl
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem conj_mem_rootU_of_mem_bSU {b x : SU (unitaryInvolution F p f) 3}
    (hb : b ∈ bSU (unitaryInvolution F p f)) (hx : x ∈ rootU hF) : b * x * b⁻¹ ∈ rootU hF := by
  obtain ⟨μ, hμ⟩ := exists_mul_tSU hF hb
  have e : b * x * b⁻¹ = (b * (tSU hF μ)⁻¹) * (tSU hF μ * x * (tSU hF μ)⁻¹) *
      (b * (tSU hF μ)⁻¹)⁻¹ := by group
  rw [e]
  exact (rootU hF).mul_mem ((rootU hF).mul_mem hμ (tSU_conj_mem_rootU hF μ hx))
    ((rootU hF).inv_mem hμ)

omit hF in
theorem fixCol_of_conj_diag {a b c : F} (hac : a ≠ c) (hbc : b ≠ c)
    {g h : SU (unitaryInvolution F p f) 3} (hh : h ∈ bSU (unitaryInvolution F p f))
    (hmat : Matrix.diagonal ![a, b, c] * mat (unitaryInvolution F p f) 3 g =
      mat (unitaryInvolution F p f) 3 g * mat (unitaryInvolution F p f) 3 h) :
    (mat (unitaryInvolution F p f) 3 g 1 0 = 0 ∧ mat (unitaryInvolution F p f) 3 g 2 0 = 0) ∨
    (mat (unitaryInvolution F p f) 3 g 1 0 = 0 ∧ mat (unitaryInvolution F p f) 3 g 0 0 = 0) := by
  obtain ⟨hm1, hm2⟩ := hh
  have E : ∀ i, ![a, b, c] i * mat (unitaryInvolution F p f) 3 g i 0 =
      (mat (unitaryInvolution F p f) 3 g * mat (unitaryInvolution F p f) 3 h) i 0 := fun i => by
    have := congrFun (congrFun hmat i) 0
    rwa [Matrix.diagonal_mul] at this
  have e0 := E 0
  have e1 := E 1
  have e2 := E 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hm1, hm2, mul_zero, add_zero, cons_val_zero,
    cons_val_one, cons_val_two, head_cons, tail_cons] at e0 e1 e2
  generalize mat (unitaryInvolution F p f) 3 h 0 0 = l at e0 e1 e2
  have iso := sum_mat_mul_mat g 0 0
  have r0 : Fin.rev (0 : Fin 3) = 2 := rfl
  have r1 : Fin.rev (1 : Fin 3) = 1 := rfl
  have r2 : Fin.rev (2 : Fin 3) = 0 := rfl
  simp only [Fin.sum_univ_three, r0, r1, r2] at iso
  rw [ite_eq_right (by decide)] at iso
  by_cases hv2 : mat (unitaryInvolution F p f) 3 g 2 0 = 0
  · left
    refine ⟨?_, hv2⟩
    simp only [hv2, map_zero, mul_zero, zero_mul, add_zero, zero_add] at iso
    rcases mul_eq_zero.1 iso with h1 | h1
    · exact (map_eq_zero (unitaryInvolution F p f)).1 h1
    · exact h1
  · right
    have hl : l = c := by
      have : mat (unitaryInvolution F p f) 3 g 2 0 * (c - l) = 0 := by linear_combination e2
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 hv2
      · linear_combination -h1
    subst hl
    refine ⟨?_, ?_⟩
    · have : (b - l) * mat (unitaryInvolution F p f) 3 g 1 0 = 0 := by linear_combination e1
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) hbc
      · exact h1
    · have : (a - l) * mat (unitaryInvolution F p f) 3 g 0 0 = 0 := by linear_combination e0
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) hac
      · exact h1

omit hF in
theorem sSU_mul_mem_bSU {g : SU (unitaryInvolution F p f) 3}
    (h1 : mat (unitaryInvolution F p f) 3 g 1 0 = 0) (h0 : mat (unitaryInvolution F p f) 3 g 0 0 = 0) :
    sSU * g ∈ bSU (unitaryInvolution F p f) := by
  have hs : mat (unitaryInvolution F p f) 3 (sSU : SU (unitaryInvolution F p f) 3) = sMat := by
    rw [mat_apply]
    rfl
  rw [mem_bSU, map_mul, hs]
  simp [Matrix.mul_apply, Fin.sum_univ_three, sMat, h1, h0]

theorem mem_rootU_or_conj {ω' : Fˣ} (hω1 : ω' ≠ 1) (hω3 : ω' ^ 3 = 1) (hq3 : p ^ f % 3 = 1)
    {a : SU (unitaryInvolution F p f) 3} (ha : orderOf a = p)
    (hda : tSU hF ω' * a * (tSU hF ω')⁻¹ = a ^ 2) :
    a ∈ rootU hF ∨ sSU * a * sSU⁻¹ ∈ rootU hF := by
  obtain ⟨g, hg⟩ := exists_conj_mem_rootU hF ha
  set u := g⁻¹ * a * g with hu
  have hu1 : u ≠ 1 := by
    intro h1
    have : a = 1 := by
      calc a = g * u * g⁻¹ := by rw [hu]; group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at ha
    exact (Fact.out : p.Prime).ne_one ha.symm
  have hH : g⁻¹ * (tSU hF ω')⁻¹ * g ∈ bSU (unitaryInvolution F p f) := by
    refine fix_B hF hg hu1 ?_
    have e : (g⁻¹ * (tSU hF ω')⁻¹ * g)⁻¹ * u * (g⁻¹ * (tSU hF ω')⁻¹ * g) = u ^ 2 := by
      calc (g⁻¹ * (tSU hF ω')⁻¹ * g)⁻¹ * u * (g⁻¹ * (tSU hF ω')⁻¹ * g)
          = g⁻¹ * (tSU hF ω' * a * (tSU hF ω')⁻¹) * g := by rw [hu]; group
        _ = g⁻¹ * a ^ 2 * g := by rw [hda]
        _ = u ^ 2 := by rw [hu]; simp only [pow_two]; group
    rw [e]
    exact rootU_le_bSU hF ((rootU hF).pow_mem hg 2)
  have hh : g⁻¹ * tSU hF ω' * g ∈ bSU (unitaryInvolution F p f) := by
    have e : g⁻¹ * tSU hF ω' * g = (g⁻¹ * (tSU hF ω')⁻¹ * g)⁻¹ := by group
    rw [e]
    exact (bSU (unitaryInvolution F p f)).inv_mem hH
  have hmat : mat (unitaryInvolution F p f) 3 (tSU hF ω') * mat (unitaryInvolution F p f) 3 g =
      mat (unitaryInvolution F p f) 3 g * mat (unitaryInvolution F p f) 3 (g⁻¹ * tSU hF ω' * g) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 3 * m + 1 := ⟨p ^ f / 3, by omega⟩
  have d11 : ((ω' ^ (p ^ f - 1) : Fˣ) : F) = 1 := by
    rw [hm, Nat.add_sub_cancel, pow_mul, hω3, one_pow, Units.val_one]
  have d22 : (((ω' ^ (p ^ f))⁻¹ : Fˣ) : F) = ((ω'⁻¹ : Fˣ) : F) := by
    rw [hm, pow_succ, pow_mul, hω3, one_pow, one_mul]
  rw [mat_tSU hF ω', d11, d22] at hmat
  have hbc : (1 : F) ≠ ((ω'⁻¹ : Fˣ) : F) := fun h => hω1 (by
    have : ω'⁻¹ = 1 := Units.ext h.symm
    simpa using this)
  have hac : (ω' : F) ≠ ((ω'⁻¹ : Fˣ) : F) := fun h => hω1 (by
    have h' : ω' = ω'⁻¹ := Units.ext h
    have h2 : ω' ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.2 h'
    have h3 : ω' ^ 3 = ω' * ω' ^ 2 := pow_succ' ω' 2
    rw [h2, mul_one, hω3] at h3
    exact h3.symm)
  rcases fixCol_of_conj_diag hac hbc hh hmat with ⟨h1, h2⟩ | ⟨h1, h0⟩
  · left
    have := conj_mem_rootU_of_mem_bSU hF (show g ∈ bSU (unitaryInvolution F p f) from ⟨h1, h2⟩) hg
    have e : g * u * g⁻¹ = a := by rw [hu]; group
    rwa [e] at this
  · right
    have := conj_mem_rootU_of_mem_bSU hF (sSU_mul_mem_bSU h1 h0) hg
    have e : sSU * g * u * (sSU * g)⁻¹ = sSU * a * sSU⁻¹ := by rw [hu]; group
    rwa [e] at this

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

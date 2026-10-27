module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddBad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCountSU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.IsolatedInvolution

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
include hF hp2

theorem commute_zSU_of_offblock {x : SU (unitaryInvolution F p f) 3} (h01 : mat3 x 0 1 = 0)
    (h10 : mat3 x 1 0 = 0) (h12 : mat3 x 1 2 = 0) (h21 : mat3 x 2 1 = 0) :
    x * zSU hF = zSU hF * x := by
  apply mat3_injective
  rw [mat3_mul, mat3_mul, mat3_zSU hF hp2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, h01, h10, h12, h21]

theorem commute_zSU_of_commute_tSU_sq {ν : Fˣ} (hν : (ν ^ (p ^ f))⁻¹ = ν) (hν6 : ν ^ 6 ≠ 1)
    {x : SU (unitaryInvolution F p f) 3} (hx : x * tSU hF (ν * ν) = tSU hF (ν * ν) * x) :
    x * zSU hF = zSU hF * x := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hνq : ν ^ (p ^ f) = ν⁻¹ := inv_eq_iff_eq_inv.1 hν
  have d2 : ((ν * ν) ^ (p ^ f))⁻¹ = ν * ν := by
    rw [mul_pow, hνq, _root_.mul_inv_rev, inv_inv]
  have d1 : (ν * ν) ^ (p ^ f - 1) = (ν ^ 4)⁻¹ := by
    refine mul_right_cancel (b := ν * ν) ?_
    rw [← pow_succ, Nat.sub_add_cancel hq1, mul_pow, hνq]
    group
  have hm : mat3 x * mat3 (tSU hF (ν * ν)) = mat3 (tSU hF (ν * ν)) * mat3 x := by
    rw [← mat3_mul, ← mat3_mul, hx]
  rw [mat3_tSU hF, d1, d2] at hm
  have hab : (((ν * ν : Fˣ)) : F) ≠ (((ν ^ 4)⁻¹ : Fˣ) : F) := by
    intro h
    apply hν6
    have h' : ν * ν = (ν ^ 4)⁻¹ := Units.ext h
    calc ν ^ 6 = ν ^ 4 * (ν * ν) := by group
      _ = 1 := by rw [h']; exact mul_inv_cancel _
  set a : F := (((ν * ν : Fˣ)) : F) with ha
  set b : F := (((ν ^ 4)⁻¹ : Fˣ) : F) with hb
  have key : ∀ i j : Fin 3, (![a, b, a] j - ![a, b, a] i) * mat3 x i j = 0 := by
    intro i j
    have := congrFun (congrFun hm i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    linear_combination this
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab
  have k01 : (b - a) * mat3 x 0 1 = 0 := key 0 1
  have k10 : (a - b) * mat3 x 1 0 = 0 := key 1 0
  have k12 : (a - b) * mat3 x 1 2 = 0 := key 1 2
  have k21 : (b - a) * mat3 x 2 1 = 0 := key 2 1
  exact commute_zSU_of_offblock hF hp2 ((mul_eq_zero.1 k01).resolve_left hba)
    ((mul_eq_zero.1 k10).resolve_left hab') ((mul_eq_zero.1 k12).resolve_left hab')
    ((mul_eq_zero.1 k21).resolve_left hba)

theorem isSolvable_of_centralizer_le {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : p ^ f % 3 = 1)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    (hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω) : Group.IsSolvable W := by
  have hTN := range_tSU_le_normA0 hF hω hq3
  have hzT : zSU hF ∈ (tSU hF).range := ⟨-1, rfl⟩
  have hzW : zSU hF ∈ W := hNW (hTN hzT)
  obtain ⟨ν, hνo, -, hνq⟩ := exists_unit_orderOf_card_add_one hF hp2
  have hodd := odd_prime_pow (p := p) (f := f) hp2
  have hq2 := two_le_prime_pow_of_card hF
  have hν6 : ν ^ 6 ≠ 1 := by
    intro h
    have h1 := Nat.le_of_dvd (by norm_num) (hνo ▸ orderOf_dvd_of_pow_eq_one h)
    obtain ⟨m, hm⟩ := hodd
    omega
  obtain ⟨ι, hι⟩ : IsSquare (-1 : F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF]
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    have : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    omega
  have hι0 : ι ≠ 0 := fun h => by
    rw [h, mul_zero] at hι
    exact one_ne_zero (neg_eq_zero.1 hι)
  set ι' : Fˣ := Units.mk0 ι hι0 with hι'
  have hιz : tSU hF ι' * tSU hF ι' = zSU hF := by
    rw [← map_mul, zSU]
    congr 1
    exact Units.ext (by simpa [hι'] using hι.symm)
  have hiso : ∀ g ∈ W, (g * zSU hF * g⁻¹) * zSU hF = zSU hF * (g * zSU hF * g⁻¹) →
      g * zSU hF * g⁻¹ = zSU hF := by
    intro g hg hc
    have hyW : g * zSU hF * g⁻¹ ∈ W := W.mul_mem (W.mul_mem hg hzW) (W.inv_mem hg)
    have hyN := hbad _ hyW hc
    have hp₀y := tSU_comm_normA0 hF hω hq3 hνq _ hyN
    have hp₀W : tSU hF ν ∈ W := hNW (hTN ⟨ν, rfl⟩)
    have hp₁W : g⁻¹ * tSU hF ν * g ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hg) hp₀W) hg
    have hp₁z : (g⁻¹ * tSU hF ν * g) * zSU hF = zSU hF * (g⁻¹ * tSU hF ν * g) := by
      calc (g⁻¹ * tSU hF ν * g) * zSU hF = g⁻¹ * (tSU hF ν * (g * zSU hF * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * zSU hF * g⁻¹) * tSU hF ν) * g := by rw [hp₀y]
        _ = zSU hF * (g⁻¹ * tSU hF ν * g) := by group
    have hp₁N := hbad _ hp₁W hp₁z
    have hr : g⁻¹ * tSU hF (ν * ν) * g ∈ (tSU hF).range := by
      have e : g⁻¹ * tSU hF (ν * ν) * g = (g⁻¹ * tSU hF ν * g) * (g⁻¹ * tSU hF ν * g) := by
        rw [map_mul]
        group
      rw [e]
      exact mul_self_mem_of_relIndex_eq_two (relIndex_range_normA0 hF hω hq3) hp₁N
    have hT : ∀ t ∈ (tSU hF).range, g * t * g⁻¹ ∈ normA0 hF ω := by
      intro t ht
      have htW : g * t * g⁻¹ ∈ W := W.mul_mem (W.mul_mem hg (hNW (hTN ht))) (W.inv_mem hg)
      refine hbad _ htW (commute_zSU_of_commute_tSU_sq hF hp2 hνq hν6 ?_)
      obtain ⟨μ, rfl⟩ := ht
      obtain ⟨κ, hκ⟩ := hr
      have e : tSU hF μ * (g⁻¹ * tSU hF (ν * ν) * g) = (g⁻¹ * tSU hF (ν * ν) * g) * tSU hF μ := by
        rw [← hκ, ← map_mul, ← map_mul, mul_comm]
      calc g * tSU hF μ * g⁻¹ * tSU hF (ν * ν)
          = g * (tSU hF μ * (g⁻¹ * tSU hF (ν * ν) * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * tSU hF (ν * ν) * g) * tSU hF μ) * g⁻¹ := by rw [e]
        _ = tSU hF (ν * ν) * (g * tSU hF μ * g⁻¹) := by group
    have hyT : g * zSU hF * g⁻¹ ∈ (tSU hF).range := by
      have e : g * zSU hF * g⁻¹ = (g * tSU hF ι' * g⁻¹) * (g * tSU hF ι' * g⁻¹) := by
        conv_lhs => rw [← hιz]
        group
      rw [e]
      exact mul_self_mem_of_relIndex_eq_two (relIndex_range_normA0 hF hω hq3) (hT _ ⟨ι', rfl⟩)
    have hyy : (g * zSU hF * g⁻¹) * (g * zSU hF * g⁻¹) = 1 := by
      calc (g * zSU hF * g⁻¹) * (g * zSU hF * g⁻¹) = g * (zSU hF * zSU hF) * g⁻¹ := by group
        _ = 1 := by rw [zSU_mul_self hF]; group
    have hy1 : g * zSU hF * g⁻¹ ≠ 1 := fun h1 => zSU_ne_one hF hp2 (by
      calc zSU hF = g⁻¹ * (g * zSU hF * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
    exact eq_of_sq_eq_one_of_isCyclic (isCyclic_range_tSU hF) hyT hzT hyy (zSU_mul_self hF) hy1
      (zSU_ne_one hF hp2)
  refine CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.IsolatedInvolution.isSolvable_of_isolated
    (t := (⟨zSU hF, hzW⟩ : W)) ?_ ?_ ?_ ?_
  · intro h1
    exact zSU_ne_one hF hp2 (congrArg Subtype.val h1)
  · exact Subtype.ext (zSU_mul_self hF)
  · intro g hc
    exact Subtype.ext (hiso g g.2 (congrArg Subtype.val hc))
  · have hN : Group.IsSolvable (normA0 hF ω) :=
      isSolvable_of_relIndex_eq_two (isCyclic_range_tSU hF) (relIndex_range_normA0 hF hω hq3)
    let ψ : Subgroup.centralizer ({(⟨zSU hF, hzW⟩ : W)} : Set W) →* normA0 hF ω :=
      { toFun := fun x => ⟨(x : W), hbad _ (x : W).2 (by
          have := Subgroup.mem_centralizer_singleton_iff.1 x.2
          exact congrArg Subtype.val this)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := ψ) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun u : normA0 hF ω => (u : SU (unitaryInvolution F p f) 3)) hxy))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

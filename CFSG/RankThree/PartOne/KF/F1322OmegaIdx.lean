module

public import CFSG.RankThree.PartOne.KF.BloomOmega

public section

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartOne.KFBloom
open scoped MatrixGroups

theorem natCard_range_adGL_mul_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (adGL (K := ZMod p)).range * 2 = p * (p ^ 2 - 1) := by
  have hpr : p.Prime := Fact.out
  have hSL := card_sl2_zmod p
  have hker : Nat.card (adGL (K := ZMod p)).ker = 2 := by
    have h1 : Nat.card (adGL (K := ZMod p)).ker =
        Set.ncard ((adGL (K := ZMod p)).ker : Set SL(2, ZMod p)) := Nat.card_coe_set_eq _
    have hne : (1 : SL(2, ZMod p)) ≠ negOne := by
      intro h
      have h2 := congrArg (fun g : SL(2, ZMod p) => (g 0 0)) h
      simp only [negOne, Matrix.SpecialLinearGroup.coe_one] at h2
      have h3 : (2 : ZMod p) = 0 := by
        simp at h2
        linear_combination h2
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp this)
    rw [h1, ker_adGL_eq hp2, Set.ncard_pair hne]
  have h1 := (adGL (K := ZMod p)).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (adGL (K := ZMod p))).toEquiv,
    hker, hSL] at h1
  exact h1.symm

theorem index_omegaGL_soGL {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0) :
    ((omegaGL M).subgroupOf (soGL M)).index = 2 := by
  have hp2 : p ≠ 2 := by omega
  have hcardS : Nat.card (soGL M) = p * (p ^ 2 - 1) := card_soGL_three hp2 hMt hdet
  obtain ⟨g, c, hc, hg⟩ := exists_congr_splitForm hp2 M hMt hdet
  have hΩ : (omegaGL M).comap (MulAut.conj g : GL (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p)) =
      omegaGL (splitForm p) := by
    rw [← omegaGL_congr, hg, omegaGL_smul _ hc]
  have hcard : Nat.card (omegaGL M) = Nat.card (omegaGL (splitForm p)) :=
    natCard_eq_of_comap (MulAut.conj g) (omegaGL (splitForm p)) (omegaGL M) hΩ
  rw [omegaGL_splitForm_eq_range hp] at hcard
  have hcard2 : Nat.card (omegaGL M) * 2 = p * (p ^ 2 - 1) := by
    rw [hcard]
    exact natCard_range_adGL_mul_two hp2
  have h := Subgroup.card_mul_index ((omegaGL M).subgroupOf (soGL M))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (omegaGL_le_soGL M)).toEquiv, hcardS] at h
  have hpos : 0 < Nat.card (omegaGL M) := Nat.card_pos
  have : Nat.card (omegaGL M) * ((omegaGL M).subgroupOf (soGL M)).index =
      Nat.card (omegaGL M) * 2 := by
    rw [h, hcard2]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem sq_mem_omegaGL {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    {y : GL (Fin 3) (ZMod p)} (hy : y ∈ soGL M) : y * y ∈ omegaGL M := by
  have h := Subgroup.mul_mem_iff_of_index_two (index_omegaGL_soGL hp hMt hdet)
    (a := (⟨y, hy⟩ : soGL M)) (b := ⟨y, hy⟩)
  have : (⟨y, hy⟩ * ⟨y, hy⟩ : soGL M) ∈ (omegaGL M).subgroupOf (soGL M) := h.mpr Iff.rfl
  exact Subgroup.mem_subgroupOf.mp this

theorem mul_mem_omegaGL_of_not_mem {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    {x y : GL (Fin 3) (ZMod p)} (hx : x ∈ soGL M) (hy : y ∈ soGL M) (hx' : x ∉ omegaGL M)
    (hy' : y ∉ omegaGL M) : x * y ∈ omegaGL M := by
  have h := Subgroup.mul_mem_iff_of_index_two (index_omegaGL_soGL hp hMt hdet)
    (a := (⟨x, hx⟩ : soGL M)) (b := ⟨y, hy⟩)
  have h1 : (⟨x, hx⟩ : soGL M) ∉ (omegaGL M).subgroupOf (soGL M) := fun hh =>
    hx' (Subgroup.mem_subgroupOf.mp hh)
  have h2 : (⟨y, hy⟩ : soGL M) ∉ (omegaGL M).subgroupOf (soGL M) := fun hh =>
    hy' (Subgroup.mem_subgroupOf.mp hh)
  have : (⟨x, hx⟩ * ⟨y, hy⟩ : soGL M) ∈ (omegaGL M).subgroupOf (soGL M) :=
    h.mpr ⟨fun a => absurd a h1, fun b => absurd b h2⟩
  exact Subgroup.mem_subgroupOf.mp this

end CFSG.RankThree.PartOne.KF1322

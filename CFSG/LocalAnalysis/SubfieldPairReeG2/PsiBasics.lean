module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.Walter.ReeOrder.JT.Defs
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalSL2

public section

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Seitz.TrialityOdd.Proving (sl2Range)

namespace CFSG.LocalAnalysis.SubfieldPairReeG2

theorem mem_sl2Range_fixSubfield_iff {K : Type} [Field K] [Finite K] (β : K ≃+* K)
    (g : SL2 K) :
    g ∈ sl2Range (fixSubfield β) K ↔
      Matrix.SpecialLinearGroup.map β.toRingHom g = g := by
  constructor
  · rintro ⟨h, rfl⟩
    apply Subtype.ext
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (h i j).2
  · intro hg
    have hfix : ∀ i j, g i j ∈ fixSubfield β := fun i j => by
      have := congrArg (fun m : SL2 K => (m : Matrix (Fin 2) (Fin 2) K) i j) hg
      simpa using this
    let M : Matrix (Fin 2) (Fin 2) (fixSubfield β) := Matrix.of fun i j => ⟨g i j, hfix i j⟩
    have hmap : (algebraMap (fixSubfield β) K).mapMatrix M = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j; rfl
    have hdet : M.det = 1 := by
      apply (algebraMap (fixSubfield β) K).injective
      rw [RingHom.map_det, hmap, map_one]
      exact g.2
    let h : Matrix.SpecialLinearGroup (Fin 2) (fixSubfield β) := ⟨M, hdet⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hmap



theorem eq_zero_of_apply_eq_neg {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {β : K ≃+* K} {p : ℕ}
    (hp : Odd p) (hβ : orderOf β = p) {y : K} (hy : β y = -y) : y = 0 := by
  have hpow : ∀ n : ℕ, (β ^ n) y = (-1) ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RingAut.mul_apply, hy, map_neg, ih]; ring
  have h1 : (β ^ p) y = y := by rw [← hβ, pow_orderOf_eq_one]; rfl
  rw [hpow, hp.neg_one_pow] at h1
  have : 2 * y = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 this).resolve_left h2



theorem exists_involution_range_psi {Γ : Type*} [Group Γ] {K : Type} [Field K]
    (ψ : SL2 K →* Γ) (hker : ∀ g, ψ g = 1 ↔ g = 1 ∨ g = -1) :
    ∃ s ∈ ψ.range, orderOf s = 2 := by
  have hW2 : (WSL : SL2 K) * WSL = -1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hW1 : (WSL : SL2 K) ≠ 1 := by
    intro h
    have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [coe_WSL] at this
  have hW1' : (WSL : SL2 K) ≠ -1 := by
    intro h
    have := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simp [coe_WSL] at this
  refine ⟨ψ WSL, ⟨WSL, rfl⟩, ?_⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← map_mul, hW2]; exact (hker _).2 (Or.inr rfl)
  · intro h; rcases (hker _).1 h with h | h
    · exact hW1 h
    · exact hW1' h

theorem exists_mul_of_internalDirectProduct {Γ : Type*} [Group Γ] {t : Γ} (ht2 : orderOf t = 2)
    {L : Subgroup Γ}
    (hIDP : CFSG.Walter.JT.IsInternalDirectProduct (Subgroup.zpowers t) L
      (Subgroup.centralizer {t})) {x : Γ} (hx : x * t = t * x) :
    ∃ y ∈ L, x = y ∨ x = t * y := by
  obtain ⟨hsup, -, hcomm⟩ := hIDP
  have hxc : x ∈ Subgroup.centralizer ({t} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact hx
  rw [← hsup] at hxc
  have hc : ∀ (e : ℤ) (y : Γ), y ∈ L → t ^ e * y = y * t ^ e := fun e y hy =>
    (Subgroup.mem_centralizer_iff.1 (hcomm (Subgroup.zpow_mem_zpowers t e)) y hy).symm
  let T : Subgroup Γ :=
    { carrier := {z | ∃ e : ℤ, ∃ y ∈ L, z = t ^ e * y}
      one_mem' := ⟨0, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨e, y, hy, rfl⟩ ⟨f, y', hy', rfl⟩
        refine ⟨e + f, y * y', L.mul_mem hy hy', ?_⟩
        calc t ^ e * y * (t ^ f * y') = t ^ e * (y * t ^ f) * y' := by group
          _ = t ^ e * (t ^ f * y) * y' := by rw [hc f y hy]
          _ = t ^ (e + f) * (y * y') := by rw [zpow_add]; group
      inv_mem' := by
        rintro _ ⟨e, y, hy, rfl⟩
        refine ⟨-e, y⁻¹, L.inv_mem hy, ?_⟩
        calc (t ^ e * y)⁻¹ = y⁻¹ * (t ^ e)⁻¹ := by rw [mul_inv_rev]
          _ = y⁻¹ * t ^ (-e) := by rw [zpow_neg]
          _ = t ^ (-e) * y⁻¹ := (hc (-e) y⁻¹ (L.inv_mem hy)).symm }
  have hle : Subgroup.zpowers t ⊔ L ≤ T := by
    refine sup_le ?_ ?_
    · rintro _ ⟨e, rfl⟩
      exact ⟨e, 1, L.one_mem, by simp⟩
    · intro y hy
      exact ⟨0, y, hy, by simp⟩
  obtain ⟨e, y, hy, rfl⟩ := hle hxc
  refine ⟨y, hy, ?_⟩
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  rcases Int.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have : t ^ e = 1 := by
      rw [hk, ← two_mul, zpow_mul]; simp [ht2']
    rw [this, one_mul]
  · right
    have : t ^ e = t := by
      rw [hk, zpow_add, zpow_mul]; simp [ht2']
    rw [this]

end CFSG.LocalAnalysis.SubfieldPairReeG2

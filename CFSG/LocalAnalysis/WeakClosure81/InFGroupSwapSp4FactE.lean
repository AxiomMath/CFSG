module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.Ch4.L436

open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem uT_mulVec_zero {K : Type} [Field K] (t : K) (x : Fin 2 → K) :
    (Matrix.mulVec (((CFSG.Quasithin.H13.Ch4.L436.uT K t : ↥(StatedSL 2 K)) :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x) 0 = x 0 + t * x 1 := by
  simp [CFSG.Quasithin.H13.Ch4.L436.uT, Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead,
    Matrix.vecTail]

private theorem uT_zero {K : Type} [Field K] : CFSG.Quasithin.H13.Ch4.L436.uT K 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.Quasithin.H13.Ch4.L436.uT]

private theorem uT_fixed {K : Type} [Field K] {t : K} (ht : t ≠ 0) {x : Fin 2 → K}
    (h : x = Matrix.mulVec (((CFSG.Quasithin.H13.Ch4.L436.uT K t : ↥(StatedSL 2 K)) :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) x) : x 1 = 0 := by
  have h0 : x 0 = x 0 + t * x 1 := by
    have h' := congrFun h 0
    rwa [uT_mulVec_zero] at h'
  have h1 : t * x 1 = 0 :=
    add_left_cancel (by rw [add_zero]; exact h0.symm)
  exact (mul_eq_zero.mp h1).resolve_left ht

private theorem exists_mul_of_eq_sup {G : Type*} [Group G] {U H K : Subgroup G}
    (hU : U = H ⊔ K) (hn : K ≤ Subgroup.normalizer (H : Set G)) {u : G} (hu : u ∈ U) :
    ∃ v ∈ H, ∃ q ∈ K, v * q = u := by
  rw [hU] at hu
  have hset : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left H K hn
  have hu' : u ∈ (↑(H ⊔ K) : Set G) := hu
  rw [hset, Set.mem_mul] at hu'
  exact hu'

private theorem conj_eq_of_mul_self {G : Type*} [Group G] {v q : G} (hv : v * v = 1)
    (hq : q * q = 1) (hu : (v * q) * (v * q) = 1) : q * v * q⁻¹ = v := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hcomm : v * q = q * v := by
    have hinv : (v * q)⁻¹ = v * q := inv_eq_of_mul_eq_one_right hu
    calc v * q = (v * q)⁻¹ := hinv.symm
      _ = q⁻¹ * v⁻¹ := mul_inv_rev v q
      _ = q * v := by rw [hqinv, hvinv]
  calc q * v * q⁻¹ = q * v * q := by rw [hqinv]
    _ = v * q * q := by rw [← hcomm]
    _ = v * (q * q) := by rw [mul_assoc]
    _ = v := by rw [hq, mul_one]

theorem mem_or_mem_of_mul_self (h : Setting L T P₀ P₁ n w) {u : Q} (hu : u ∈ T ⊓ L)
    (hu2 : u * u = 1) : u ∈ pCoreOf 2 (perfectCore P₀) ∨ u ∈ pCoreOf 2 (perfectCore P₁) := by
  obtain ⟨K, hKfld, hKfin, -, α, β, -, hαker, -, -, hequiv, hmemS, hCZ⟩ := h.concl₁.coord
  letI := hKfld
  letI := hKfin
  have hS : (T ⊓ L : Subgroup Q) =
      pCoreOf 2 (perfectCore P₁) ⊔ pCoreOf 2 (perfectCore P₀) := by
    rw [h.concl₁.S_eq, sp4Q₁_one h]
  have hle₁ : pCoreOf 2 (perfectCore P₁) ≤ T ⊓ L := hS ▸ le_sup_left
  have hle₀ : pCoreOf 2 (perfectCore P₀) ≤ T ⊓ L := hS ▸ le_sup_right
  have hnorm : (T ⊓ L : Subgroup Q) ≤
      Subgroup.normalizer (pCoreOf 2 (perfectCore P₁) : Set Q) :=
    h.concl₁.S_le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (perfectCore P₁))
  obtain ⟨v, hv, q, hq, hvq⟩ := exists_mul_of_eq_sup hS (hle₀.trans hnorm) hu
  by_cases hq₁ : q ∈ pCoreOf 2 (perfectCore P₁)
  · exact Or.inr (hvq ▸ (pCoreOf 2 (perfectCore P₁)).mul_mem hv hq₁)
  left
  have hqP : q ∈ perfectCore P₁ := h.concl₁.S_le (hle₀ hq)
  have hαne : α ⟨q, hqP⟩ ≠ 1 := fun h1 => hq₁ ((hαker ⟨q, hqP⟩).mp h1)
  obtain ⟨t, ht⟩ := (hmemS ⟨q, hqP⟩).mp (hle₀ hq)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hαne (ht.trans uT_zero)
  have hv2 : v * v = 1 := by
    simpa [pow_two] using h.concl₁.V_sq v hv
  have hq2 : q * q = 1 := by
    simpa [pow_two] using h.concl₀.V_sq q hq
  have hconj : q * v * q⁻¹ = v :=
    conj_eq_of_mul_self hv2 hq2 (by rw [hvq]; exact hu2)
  have heq : Multiplicative.toAdd (β ⟨v, hv⟩) =
      Matrix.mulVec (((α ⟨q, hqP⟩ : GL (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) (Multiplicative.toAdd (β ⟨v, hv⟩)) :=
    hequiv ⟨q, hqP⟩ ⟨v, hv⟩ ⟨v, hv⟩ (by simpa using hconj.symm)
  rw [ht] at heq
  have hx1 : Multiplicative.toAdd (β ⟨v, hv⟩) 1 = 0 := uT_fixed ht0 heq
  have hmem : v ∈ sp4C P₁ (pCoreOf 2 (perfectCore P₁)) ⊔
      sp4Z P₁ (T ⊓ L) (pCoreOf 2 (perfectCore P₁)) := (hCZ ⟨v, hv⟩).mpr hx1
  have hmem' : v ∈ pCoreOf 2 (perfectCore P₀) ⊓ pCoreOf 2 (perfectCore P₁) := by
    rw [rad_inf_rad h]
    rw [sp4C_zero_eq h, sup_comm]
    exact hmem
  exact hvq ▸ (pCoreOf 2 (perfectCore P₀)).mul_mem (Subgroup.mem_inf.mp hmem').1 hq

theorem le_or_le_of_isElemAbelian (h : Setting L T P₀ P₁ n w) {B : Subgroup Q}
    (hB : B ≤ T ⊓ L) (hB2 : IsElemAbelian 2 B) :
    B ≤ pCoreOf 2 (perfectCore P₀) ∨ B ≤ pCoreOf 2 (perfectCore P₁) := by
  refine SubgroupClass.subset_union.mp fun x hx => ?_
  exact mem_or_mem_of_mul_self h (hB hx) (hB2.mul_self_eq_one hx)

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

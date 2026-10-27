module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab
public import Mathlib.Data.Fin.Tuple.Sort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.AGLEmbedding.LinearThreeKit Matrix Subgroup
open scoped commutatorElement MatrixGroups

section

variable {K : Type} [Field K]

local notation "M₃" => Matrix (Fin 3) (Fin 3) K

local notation "PS" => stabilizer (flagSpace 3 K 1)

private theorem mem_stab_of_entries {g : SL(3, K)} (h1 : (g : M₃) 1 0 = 0)
    (h2 : (g : M₃) 2 0 = 0) : g ∈ PS := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, flagSpace_one_eq_span] at hv
  rw [flagSpace_one_eq_span]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine Submodule.mem_span_singleton.mpr ⟨c * (g : M₃) 0 0, ?_⟩
  ext k
  fin_cases k <;> simp [h1, h2, mul_comm]

private theorem entry_ne_zero {g : SL(3, K)} (hg : g ∈ PS) : (g : M₃) 0 0 ≠ 0 := by
  intro h
  have h1 := mulVec_single_zero_of_mem_stabilizer_one hg
  rw [h, zero_smul] at h1
  have h2 := congrArg (((g⁻¹ : SL(3, K)) : M₃) *ᵥ ·) h1
  rw [mulVec_mulVec, coe_inv_mul_coe, one_mulVec, mulVec_zero] at h2
  simpa using congrFun h2 0

private theorem minor_mulVec {g : SL(3, K)} (hg : g ∈ PS) {v : Fin 3 → K}
    (hv : (g : M₃) *ᵥ v = ((g : M₃) 0 0)⁻¹ • v) (x : Fin 3 → K) :
    v 1 * ((g : M₃) *ᵥ x) 2 - v 2 * ((g : M₃) *ᵥ x) 1 = v 1 * x 2 - v 2 * x 1 := by
  have h10 := apply_zero_eq_zero_of_mem_stabilizer_one hg (k := 1) (by decide)
  have h20 := apply_zero_eq_zero_of_mem_stabilizer_one hg (k := 2) (by decide)
  have hdet : (g : M₃).det = 1 := g.2
  rw [det_fin_three, h10, h20] at hdet
  have hv1 := congrFun hv 1
  have hv2 := congrFun hv 2
  have hμ : ((g : M₃) 0 0)⁻¹ * (g : M₃) 0 0 = 1 := inv_mul_cancel₀ (entry_ne_zero hg)
  simp only [mulVec, dotProduct, Fin.sum_univ_three, h10, h20, Pi.smul_apply, smul_eq_mul,
    zero_mul, zero_add] at hv1 hv2 ⊢
  linear_combination (v 1 * x 2 - v 2 * x 1) * hdet
    - (v 1 * ((g : M₃) 2 1 * x 1 + (g : M₃) 2 2 * x 2)
      - v 2 * ((g : M₃) 1 1 * x 1 + (g : M₃) 1 2 * x 2)) * hμ
    - (g : M₃) 0 0 * ((g : M₃) 2 1 * x 1 + (g : M₃) 2 2 * x 2) * hv1
    + (g : M₃) 0 0 * ((g : M₃) 1 1 * x 1 + (g : M₃) 1 2 * x 2) * hv2

variable [CharP K 2]

private theorem exists_fixed {E₀ : Subgroup SL(3, K)} [Finite E₀] (hodd : Odd (Nat.card E₀))
    (hE₀ : E₀ ≤ PS) {v : Fin 3 → K} (hv : v 1 ≠ 0 ∨ v 2 ≠ 0)
    (hgv : ∀ g ∈ E₀, (g : M₃) *ᵥ v = ((g : M₃) 0 0)⁻¹ • v) :
    ∃ w : Fin 3 → K, (∀ g ∈ E₀, (g : M₃) *ᵥ w = w) ∧ v 1 * w 2 - v 2 * w 1 ≠ 0 := by
  classical
  have : Fintype E₀ := Fintype.ofFinite _
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → K, v 1 * x 2 - v 2 * x 1 ≠ 0 := by
    by_cases h2 : v 2 = 0
    · exact ⟨Pi.single 2 1, by simpa [h2] using hv.resolve_right (not_not.mpr h2)⟩
    · exact ⟨Pi.single 1 1, by simpa using h2⟩
  refine ⟨∑ g : E₀, ((g : SL(3, K)) : M₃) *ᵥ x, fun h hh => ?_, ?_⟩
  · rw [mulVec_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft ⟨h, hh⟩) _ _ fun g => ?_
    rw [mulVec_mulVec]
    rfl
  · rw [Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun (g : E₀) _ => minor_mulVec (hE₀ g.2) (hgv _ g.2) x,
      Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, nsmul_eq_mul]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add,
      Nat.cast_one, one_mul]
    exact hx

private theorem exists_diag {E₀ : Subgroup SL(3, K)} [Finite E₀] (hodd : Odd (Nat.card E₀))
    (hE₀ : E₀ ≤ PS) {v : Fin 3 → K} (hv : v 1 ≠ 0 ∨ v 2 ≠ 0)
    (hgv : ∀ g ∈ E₀, (g : M₃) *ᵥ v = ((g : M₃) 0 0)⁻¹ • v) :
    ∃ S : SL(3, K), S ∈ PS ∧ ∀ g ∈ E₀,
      ((S⁻¹ * g * S : SL(3, K)) : M₃) = diagonal ![(g : M₃) 0 0, ((g : M₃) 0 0)⁻¹, 1] := by
  obtain ⟨w, hw, hδ⟩ := exists_fixed hodd hE₀ hv hgv
  set δ := v 1 * w 2 - v 2 * w 1 with hδdef
  set S₀ : M₃ := !![1, v 0, δ⁻¹ * w 0; 0, v 1, δ⁻¹ * w 1; 0, v 2, δ⁻¹ * w 2] with hS₀
  have hdet : S₀.det = 1 := by
    rw [hS₀, det_fin_three]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one, head_cons, tail_cons, head_fin_const]
    calc _ = δ⁻¹ * (v 1 * w 2 - v 2 * w 1) := by ring
      _ = 1 := by rw [← hδdef, inv_mul_cancel₀ hδ]
  set S : SL(3, K) := ⟨S₀, hdet⟩ with hS
  refine ⟨S, mem_stab_of_entries (by simp [hS, hS₀]) (by simp [hS, hS₀]), fun g hg => ?_⟩
  have c0 : ∀ i, ((g : M₃) * S₀) i 0 = S₀ i 0 * (g : M₃) 0 0 := fun i => by
    change ((g : M₃) *ᵥ fun k => S₀ k 0) i = _
    rw [show (fun k => S₀ k 0) = Pi.single 0 1 by ext k; fin_cases k <;> simp [hS₀],
      mulVec_single_zero_of_mem_stabilizer_one (hE₀ hg)]
    fin_cases i <;> simp [hS₀]
  have c1 : ∀ i, ((g : M₃) * S₀) i 1 = S₀ i 1 * ((g : M₃) 0 0)⁻¹ := fun i => by
    change ((g : M₃) *ᵥ fun k => S₀ k 1) i = _
    rw [show (fun k => S₀ k 1) = v by ext k; fin_cases k <;> simp [hS₀], hgv g hg]
    fin_cases i <;> simp [hS₀, mul_comm]
  have c2 : ∀ i, ((g : M₃) * S₀) i 2 = S₀ i 2 := fun i => by
    change ((g : M₃) *ᵥ fun k => S₀ k 2) i = _
    rw [show (fun k => S₀ k 2) = δ⁻¹ • w by ext k; fin_cases k <;> simp [hS₀], mulVec_smul,
      hw g hg]
    fin_cases i <;> simp [hS₀]
  have hgS : (g : M₃) * S₀ = S₀ * diagonal ![(g : M₃) 0 0, ((g : M₃) 0 0)⁻¹, 1] := by
    ext i j
    rw [mul_diagonal]
    fin_cases j
    · simpa using c0 i
    · simpa using c1 i
    · simpa using c2 i
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
  change ((S⁻¹ : SL(3, K)) : M₃) * ((g : M₃) * S₀) = _
  rw [hgS, ← mul_assoc, show S₀ = (S : M₃) from rfl, coe_inv_mul_coe, one_mul]

private def rhoT : SL(3, K) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by simp [det_fin_three, CharTwo.neg_eq]⟩

private def sigmaT : SL(3, K) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [det_fin_three, CharTwo.neg_eq]⟩

private theorem rhoT_inv : (rhoT : SL(3, K))⁻¹ = rhoT := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : M₃) * !![0, 0, 1; 0, 1, 0; 1, 0, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

private theorem sigmaT_inv : (sigmaT : SL(3, K))⁻¹ = sigmaT := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : M₃) * !![1, 0, 0; 0, 0, 1; 0, 1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

private theorem sigmaT_mem : (sigmaT : SL(3, K)) ∈ PS :=
  mem_stab_of_entries (by simp [sigmaT]) (by simp [sigmaT])

private theorem rho_conj {δ : SL(3, K)} {x : K} (h : (δ : M₃) = diagonal ![x, x⁻¹, 1]) :
    ((rhoT * δ * rhoT : SL(3, K)) : M₃) = diagonal ![1, x⁻¹, x] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rhoT, mul_apply, Fin.sum_univ_three, vecMul_diagonal]

private theorem sigma_conj {δ : SL(3, K)} {x : K} (h : (δ : M₃) = diagonal ![x, x⁻¹, 1]) :
    ((sigmaT * δ * sigmaT : SL(3, K)) : M₃) = diagonal ![x, 1, x⁻¹] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaT, mul_apply, Fin.sum_univ_three, vecMul_diagonal]

private theorem conj_eq_commutator {S g : SL(3, K)} {x : K} (hx : x ≠ 0)
    (h : ((S⁻¹ * g * S : SL(3, K)) : M₃) = diagonal ![x, x⁻¹, 1]) :
    S * rhoT * S⁻¹ * g * (S * rhoT * S⁻¹)⁻¹ = ⁅g, S * sigmaT * S⁻¹⁆ := by
  obtain ⟨δ, rfl⟩ : ∃ δ, g = S * δ * S⁻¹ := ⟨S⁻¹ * g * S, by group⟩
  rw [show S⁻¹ * (S * δ * S⁻¹) * S = δ by group] at h
  have hD : rhoT * δ * rhoT * (sigmaT * δ * sigmaT) = δ := by
    refine Subtype.ext ?_
    change ((rhoT * δ * rhoT : SL(3, K)) : M₃) * ((sigmaT * δ * sigmaT : SL(3, K)) : M₃) = δ
    rw [rho_conj h, sigma_conj h, diagonal_mul_diagonal, h]
    congr 1
    ext i
    fin_cases i <;> simp [hx]
  have key : rhoT * δ * rhoT = δ * sigmaT * δ⁻¹ * sigmaT⁻¹ := by
    calc rhoT * δ * rhoT
        = rhoT * δ * rhoT * (sigmaT * δ * sigmaT) * (sigmaT * δ * sigmaT)⁻¹ := by group
      _ = δ * (sigmaT * δ * sigmaT)⁻¹ := by rw [hD]
      _ = δ * sigmaT * δ⁻¹ * sigmaT⁻¹ := by simp only [_root_.mul_inv_rev, sigmaT_inv]; group
  calc S * rhoT * S⁻¹ * (S * δ * S⁻¹) * (S * rhoT * S⁻¹)⁻¹
      = S * (rhoT * δ * rhoT⁻¹) * S⁻¹ := by group
    _ = S * (δ * sigmaT * δ⁻¹ * sigmaT⁻¹) * S⁻¹ := by rw [rhoT_inv, key]
    _ = ⁅S * δ * S⁻¹, S * sigmaT * S⁻¹⁆ := by rw [commutatorElement_def]; group

private theorem conj_commute {S g g' : SL(3, K)} {x y : K}
    (h : ((S⁻¹ * g * S : SL(3, K)) : M₃) = diagonal ![x, x⁻¹, 1])
    (h' : ((S⁻¹ * g' * S : SL(3, K)) : M₃) = diagonal ![y, y⁻¹, 1]) :
    S * rhoT * S⁻¹ * g * (S * rhoT * S⁻¹)⁻¹ * g' =
      g' * (S * rhoT * S⁻¹ * g * (S * rhoT * S⁻¹)⁻¹) := by
  obtain ⟨δ, rfl⟩ : ∃ δ, g = S * δ * S⁻¹ := ⟨S⁻¹ * g * S, by group⟩
  obtain ⟨δ', rfl⟩ : ∃ δ', g' = S * δ' * S⁻¹ := ⟨S⁻¹ * g' * S, by group⟩
  rw [show S⁻¹ * (S * δ * S⁻¹) * S = δ by group] at h
  rw [show S⁻¹ * (S * δ' * S⁻¹) * S = δ' by group] at h'
  have hc : rhoT * δ * rhoT * δ' = δ' * (rhoT * δ * rhoT) := by
    refine Subtype.ext ?_
    change ((rhoT * δ * rhoT : SL(3, K)) : M₃) * δ' = δ' * ((rhoT * δ * rhoT : SL(3, K)) : M₃)
    rw [rho_conj h, h', diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    exact mul_comm _ _
  calc S * rhoT * S⁻¹ * (S * δ * S⁻¹) * (S * rhoT * S⁻¹)⁻¹ * (S * δ' * S⁻¹)
      = S * (rhoT * δ * rhoT⁻¹ * δ') * S⁻¹ := by group
    _ = S * (δ' * (rhoT * δ * rhoT⁻¹)) * S⁻¹ := by rw [rhoT_inv, hc]
    _ = _ := by group

theorem exists_point_eigenbasis {E₀ : Subgroup SL(3, K)} (hodd : Odd (Nat.card E₀))
    (hE₀ : E₀ ≤ PS) {t : SL(3, K)} (ht : t ∉ PS)
    (htg : ∀ g ∈ E₀, (g : M₃) *ᵥ ((t : M₃) *ᵥ Pi.single 0 1) =
      ((g : M₃) 0 0)⁻¹ • ((t : M₃) *ᵥ Pi.single 0 1)) :
    ∃ S ∈ PS, ∃ σ ∈ PS, ∃ ρ : SL(3, K), ∀ g ∈ E₀,
      ((S⁻¹ * g * S : SL(3, K)) : M₃) = diagonal ![(g : M₃) 0 0, ((g : M₃) 0 0)⁻¹, 1] ∧
        ρ * g * ρ⁻¹ = ⁅g, σ⁆ ∧ ∀ g' ∈ E₀, ρ * g * ρ⁻¹ * g' = g' * (ρ * g * ρ⁻¹) := by
  have : Finite E₀ := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hv : ((t : M₃) *ᵥ Pi.single 0 1) 1 ≠ 0 ∨ ((t : M₃) *ᵥ Pi.single 0 1) 2 ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    refine ht (mem_stab_of_entries ?_ ?_)
    · simpa [mulVec_single_one] using hcon.1
    · simpa [mulVec_single_one] using hcon.2
  obtain ⟨S, hS, hdiag⟩ := exists_diag hodd hE₀ hv htg
  refine ⟨S, hS, S * sigmaT * S⁻¹, mul_mem (mul_mem hS sigmaT_mem) (inv_mem hS), S * rhoT * S⁻¹,
    fun g hg => ⟨hdiag g hg, conj_eq_commutator (entry_ne_zero (hE₀ hg)) (hdiag g hg),
      fun g' hg' => conj_commute (hdiag g hg) (hdiag g' hg')⟩⟩

end

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

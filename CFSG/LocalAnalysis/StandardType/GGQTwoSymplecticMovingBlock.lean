module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticPlaneActions
public import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticSupport
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.LieType.SeitzGeneration.SpBlockPlanes
public import CFSG.Sporadic.Suz.Setup

public section

open Matrix CFSG.Open Polynomial CFSG.Assembly
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.Classical (spSupported)
open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley
open scoped MatrixGroups commutatorElement

namespace CFSG.StandardType.QTwoSymplecticCav

variable {K : Type} [Field K] {r : ℕ}



section FourBlocks

variable {n : ℕ} (i : Fin 4 → Fin n)

theorem mat_longBlock_four (hi : Function.Injective i) (A : Fin 4 → SL(2, K)) :
    mat n K (longBlock K n (i 0) (A 0) * longBlock K n (i 1) (A 1) *
        longBlock K n (i 2) (A 2) * longBlock K n (i 3) (A 3)) =
      WitSpNs.planeMat (fun j => if j = i 0 then ((A 0 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        else if j = i 1 then ((A 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        else if j = i 2 then ((A 2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
        else if j = i 3 then ((A 3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) else 1) := by
  have h01 : i 0 ≠ i 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (hi h)
  have h02 : i 0 ≠ i 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hi h)
  have h03 : i 0 ≠ i 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (hi h)
  have h12 : i 1 ≠ i 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (hi h)
  have h13 : i 1 ≠ i 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hi h)
  have h23 : i 2 ≠ i 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (hi h)
  rw [map_mul, map_mul, map_mul,
    WitSpNs.mat_longBlock_eq_planeMat, WitSpNs.mat_longBlock_eq_planeMat,
    WitSpNs.mat_longBlock_eq_planeMat, WitSpNs.mat_longBlock_eq_planeMat,
    WitSpNs.planeMat_mul, WitSpNs.planeMat_mul, WitSpNs.planeMat_mul]
  congr 1
  funext j
  by_cases h0 : j = i 0
  · subst h0
    simp [Function.update, h01, h02, h03]
  by_cases h1 : j = i 1
  · subst h1
    simp [Function.update, h01.symm, h12, h13]
  by_cases h2 : j = i 2
  · subst h2
    simp [Function.update, h02.symm, h12.symm, h23]
  by_cases h3 : j = i 3
  · subst h3
    simp [Function.update, h03.symm, h13.symm, h23.symm]
  · simp [Function.update, h0, h1, h2, h3]

theorem mat_longBlock_four_range (hi : Function.Injective i) (W : Fin n → SL(2, K)) :
    mat n K (longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
        longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3))) =
      WitSpNs.planeMat (fun j => if j ∈ Set.range i then
        ((W j) : Matrix (Fin 2) (Fin 2) K) else 1) := by
  have h01 : i 0 ≠ i 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (hi h)
  have h02 : i 0 ≠ i 2 := fun h => (by decide : (0 : Fin 4) ≠ 2) (hi h)
  have h03 : i 0 ≠ i 3 := fun h => (by decide : (0 : Fin 4) ≠ 3) (hi h)
  have h12 : i 1 ≠ i 2 := fun h => (by decide : (1 : Fin 4) ≠ 2) (hi h)
  have h13 : i 1 ≠ i 3 := fun h => (by decide : (1 : Fin 4) ≠ 3) (hi h)
  have h23 : i 2 ≠ i 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (hi h)
  rw [mat_longBlock_four i hi (fun a => W (i a))]
  congr 1
  funext j
  by_cases hj : j ∈ Set.range i
  · obtain ⟨a, ha⟩ := hj
    subst ha
    fin_cases a
    · simp [h01, h02, h03]
    · simp [h01.symm, h12, h13]
    · simp [h02.symm, h12.symm, h23]
    · simp [h03.symm, h13.symm, h23.symm]
  · have h0 : j ≠ i 0 := fun h => hj ⟨0, h.symm⟩
    have h1 : j ≠ i 1 := fun h => hj ⟨1, h.symm⟩
    have h2 : j ≠ i 2 := fun h => hj ⟨2, h.symm⟩
    have h3 : j ≠ i 3 := fun h => hj ⟨3, h.symm⟩
    simp [hj, h0, h1, h2, h3]


theorem prod_four_longBlock_mul_self {n : ℕ} (i : Fin 4 → Fin n)
    (hi : Function.Injective i) (W : Fin n → SL(2, K))
    (hW : ∀ j, W j * W j = 1) :
    (longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
        longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3))) *
      (longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
        longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3))) = 1 := by
  let U := longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
    longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3))
  let Q : Fin n → Matrix (Fin 2) (Fin 2) K := fun j =>
    if j ∈ Set.range i then (W j : Matrix (Fin 2) (Fin 2) K) else 1
  have hU : mat n K U = WitSpNs.planeMat Q := mat_longBlock_four_range i hi W
  change U * U = 1
  apply mat_injective
  rw [map_mul, map_one, hU]
  rw [WitSpNs.planeMat_mul]
  have hQ : (fun j => Q j * Q j) = fun _ => (1 : Matrix (Fin 2) (Fin 2) K) := by
    funext j
    by_cases hj : j ∈ Set.range i
    · have hj' : ∃ y, i y = j := hj
      have hWj : (W j : Matrix (Fin 2) (Fin 2) K) * (W j : Matrix (Fin 2) (Fin 2) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, hW j, Matrix.SpecialLinearGroup.coe_one]
      simp [Q, hj', hWj]
    · have hj' : ¬ ∃ y, i y = j := hj
      simp [Q, hj']
  rw [hQ, WitSpNs.planeMat_one]

theorem mat_conj_four_longBlock {n : ℕ} (i : Fin 4 → Fin n)
    (hi : Function.Injective i) (W : Fin n → SL(2, K))
    {g : StatedSp n K} {P : Fin n → Matrix (Fin 2) (Fin 2) K}
    (hg : mat n K g = WitSpNs.planeMat P) :
    mat n K ((longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
        longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3))) * g *
      (longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
        longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3)))) =
      WitSpNs.planeMat (fun j => if j ∈ Set.range i then
        (W j : Matrix (Fin 2) (Fin 2) K) * P j *
          (W j : Matrix (Fin 2) (Fin 2) K) else P j) := by
  let U := longBlock K n (i 0) (W (i 0)) * longBlock K n (i 1) (W (i 1)) *
    longBlock K n (i 2) (W (i 2)) * longBlock K n (i 3) (W (i 3))
  let Q : Fin n → Matrix (Fin 2) (Fin 2) K := fun j =>
    if j ∈ Set.range i then (W j : Matrix (Fin 2) (Fin 2) K) else 1
  have hU : mat n K U = WitSpNs.planeMat Q := mat_longBlock_four_range i hi W
  change mat n K (U * g * U) = _
  rw [map_mul, map_mul, hg, hU]
  rw [WitSpNs.planeMat_mul, WitSpNs.planeMat_mul]
  congr 1
  funext j
  by_cases hj : j ∈ Set.range i
  · have hj' : ∃ y, i y = j := hj
    simp [Q, hj', if_true]
  · have hj' : ¬ ∃ y, i y = j := hj
    simp [Q, hj', if_false]

end FourBlocks

section PermSp

theorem spIncl_mul_of_injective {m n p : ℕ} {σ : Fin n → Fin p} {τ : Fin m → Fin n}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ) :
    CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl (K := K) σ *
      CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl (K := K) τ =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl (K := K) (σ ∘ τ) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl_apply]
  rw [Finset.sum_eq_single (Sum.map τ τ b)]
  · rw [Sum.map_map]; simp
  · intro c _ hc
    by_cases hcb : c = Sum.map τ τ b
    · exact absurd hcb hc
    · simp [hcb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem permSp_mul_of_injective {n : ℕ} (π ρ : Equiv.Perm (Fin n)) :
    permSp K (π * ρ) = permSp K π * permSp K ρ := by
  apply mat_injective
  rw [map_mul, mat_permSp, mat_permSp, mat_permSp,
    spIncl_mul_of_injective π.injective ρ.injective]
  rfl

theorem permSp_one_of_injective {n : ℕ} : permSp K (1 : Equiv.Perm (Fin n)) = 1 := by
  apply mat_injective
  rw [map_one, mat_permSp]
  ext a b
  by_cases h : a = b <;> simp [h, CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl_apply,
    Matrix.one_apply]

theorem permSp_inv_of_injective {n : ℕ} (π : Equiv.Perm (Fin n)) :
    permSp K π⁻¹ = (permSp K π)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← permSp_mul_of_injective, mul_inv_cancel, permSp_one_of_injective]

end PermSp


theorem WSL_mul_self_of_char_two [CharP K 2] : (WSL : SL(2, K)) * WSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
    CFSG.LieType.Chevalley.coe_WSL]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

section WSLConj

theorem WSL_conj_M [Finite K] (hK : Nat.card K = 2) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0) :
    ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M *
      ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = M ^ 2 := by
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hK)
  have hW2 : (WSL : SL(2, K)) * WSL = 1 := WSL_mul_self_of_char_two
  have hWi : (WSL : SL(2, K))⁻¹ = WSL := inv_eq_of_mul_eq_one_right hW2
  have h3SL : (mkSL M hdet : SL(2, K)) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_mkSL, Matrix.SpecialLinearGroup.coe_one]
    exact CFSG.StandardType.SymplecticPlaneActions.pow_three_eq_one_of_sq_add_self_add_one hM
  have hsq : (mkSL M hdet : SL(2, K)) ^ 2 = (mkSL M hdet : SL(2, K))⁻¹ := by
    have hpow : (mkSL M hdet : SL(2, K)) * (mkSL M hdet : SL(2, K)) ^ 2 =
        (mkSL M hdet : SL(2, K)) ^ 3 := by
      rw [show (3 : ℕ) = 1 + 2 by norm_num, pow_add, pow_one]
    exact (inv_eq_of_mul_eq_one_right (hpow.trans h3SL)).symm
  have hconj := CFSG.StandardType.SymplecticPlaneActions.WSL_conj_mkSL_eq_inv hK hdet hM
  rw [hWi, ← hsq] at hconj
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    coe_mkSL, Matrix.SpecialLinearGroup.coe_one] using
    congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K)) hconj

theorem WSL_conj_M_sq [Finite K] (hK : Nat.card K = 2) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0) :
    ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M ^ 2 *
      ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = M := by
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hK)
  have hW : ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    simpa using congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K))
      (WSL_mul_self_of_char_two (K := K))
  have h := WSL_conj_M hK hdet hM
  calc ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M ^ 2 *
        ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
      = ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          (((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * M *
            ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *
          ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
        rw [h]
    _ = (((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) * M *
          (((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
            ((WSL : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) := by
        noncomm_ring
    _ = M := by
        rw [hW]; simp

end WSLConj


section MovingFrame

variable {E : Subgroup (StatedSp r K)} {A0 : StatedSp r K}
  {M : Matrix (Fin 2) (Fin 2) K} {k : Fin r → ↥E →* Multiplicative (ZMod 3)}
  {t : ↥E}

@[expose] noncomputable def movingW (k : Fin r → ↥E →* Multiplicative (ZMod 3))
    (t : ↥E) (j : Fin r) : SL(2, K) :=
  if Multiplicative.toAdd (k j t) = 2 then WSL else 1

@[expose] noncomputable def movingU (i : Fin 4 → Fin r)
    (k : Fin r → ↥E →* Multiplicative (ZMod 3)) (t : ↥E) : StatedSp r K :=
  longBlock K r (i 0) (movingW k t (i 0)) * longBlock K r (i 1) (movingW k t (i 1)) *
    longBlock K r (i 2) (movingW k t (i 2)) * longBlock K r (i 3) (movingW k t (i 3))

theorem movingW_mul_self [CharP K 2] (j : Fin r) :
    movingW k t j * movingW k t j = 1 := by
  unfold movingW
  split_ifs
  · exact WSL_mul_self_of_char_two
  · simp

theorem movingU_mul_self [CharP K 2] (i : Fin 4 → Fin r) (hi : Function.Injective i) :
    movingU i k t * movingU i k t = 1 := by
  unfold movingU
  exact prod_four_longBlock_mul_self i hi (movingW k t) (fun j => movingW_mul_self j)

theorem mat_movingU (i : Fin 4 → Fin r) (hi : Function.Injective i) :
    mat r K (movingU i k t) =
      WitSpNs.planeMat (fun j => if j ∈ Set.range i then
        ((movingW k t j) : Matrix (Fin 2) (Fin 2) K) else 1) := by
  unfold movingU
  exact mat_longBlock_four_range i hi (movingW k t)


end MovingFrame

end CFSG.StandardType.QTwoSymplecticCav

end

module

public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem det_eq_one_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (hg : g ∈ StatedSL n K) : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

theorem card_statedSL_two (K : Type) [Field K] [Fintype K] :
    Nat.card (StatedSL 2 K) = Fintype.card K * (Fintype.card K ^ 2 - 1) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv, Matrix.card_SL_field,
    Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have hpos : 0 < Fintype.card K - 1 := by have := Fintype.one_lt_card (α := K); omega
  have h1 : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (Fintype.card K ^ 2 - 1) * (Fintype.card K * (Fintype.card K - 1)) =
    Fintype.card K * (Fintype.card K ^ 2 - 1) * (Fintype.card K - 1) by ring,
    Nat.mul_div_cancel _ hpos]

theorem tensorPair_faithful {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Γ₁ Γ₂ : Subgroup (GL ι F))
    (hsc : ∀ g ∈ Γ₁, ∀ c : F, (g : Matrix ι ι F) = Matrix.scalar ι c → c = 1) :
    (tensorPairModel Γ₁ Γ₂).Faithful := by
  rintro ⟨g, h⟩ hγ
  have key : ∀ X : Matrix ι ι F,
      ((g : GL ι F) : Matrix ι ι F) * X * ((h : GL ι F) : Matrix ι ι F)ᵀ = X := by
    intro X
    have h1 := Subgroup.mem_bot.mp (hγ (Multiplicative.ofAdd X) trivial)
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [tensorPairModel, tensorPairAct] at h2
    exact add_neg_eq_zero.mp h2
  have hinv : ((h : GL ι F) : Matrix ι ι F)ᵀ = (((g : GL ι F)⁻¹ : GL ι F) : Matrix ι ι F) := by
    have h1 := key 1
    rw [mul_one] at h1
    calc ((h : GL ι F) : Matrix ι ι F)ᵀ
        = (((g : GL ι F)⁻¹ : GL ι F) : Matrix ι ι F) * (((g : GL ι F) : Matrix ι ι F) *
          ((h : GL ι F) : Matrix ι ι F)ᵀ) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [h1, mul_one]
  have hcomm : ∀ X : Matrix ι ι F, Commute X ((g : GL ι F) : Matrix ι ι F) := by
    intro X
    have h1 := key X
    rw [hinv] at h1
    calc X * ((g : GL ι F) : Matrix ι ι F)
        = ((g : GL ι F) : Matrix ι ι F) * X * (((g : GL ι F)⁻¹ : GL ι F) : Matrix ι ι F) *
          ((g : GL ι F) : Matrix ι ι F) := by rw [h1]
      _ = ((g : GL ι F) : Matrix ι ι F) * X := by rw [mul_assoc _ _ ((g : GL ι F) : Matrix ι ι F),
          Units.inv_mul, mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  have hc1 := hsc _ g.2 c hc.symm
  have hg1 : (g : GL ι F) = 1 := Units.ext (by rw [← hc, hc1]; simp)
  have hh1 : (h : GL ι F) = 1 := by
    rw [hg1, inv_one, Units.val_one] at hinv
    exact Units.ext (by rw [← Matrix.transpose_transpose ((h : GL ι F) : Matrix ι ι F), hinv,
      Matrix.transpose_one, Units.val_one])
  exact Prod.ext (Subtype.ext hg1) (Subtype.ext hh1)

theorem scalar_statedSL_two {K : Type} [Field K] [CharP K 2] :
    ∀ g ∈ StatedSL 2 K, ∀ c : K, (g : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) c →
      c = 1 := by
  intro g hg c hc
  have hdet := det_eq_one_of_mem_statedSL hg
  rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
  have h2 : (c - 1) * (c - 1) = 0 := by
    have : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination hdet - (c - 1) * this
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem scalar_statedSL_three_two :
    ∀ g ∈ StatedSL 3 (ZMod 2), ∀ c : ZMod 2,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = Matrix.scalar (Fin 3) c → c = 1 := by
  intro g hg c hc
  have hdet := det_eq_one_of_mem_statedSL hg
  rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl
  · simp at hdet
  · rfl

theorem frobPow_single_transpose {F : Type} [Field F] (a : ℕ) (i j : Fin 2) :
    (frobPow a (Matrix.single i j (1 : F)))ᵀ = Matrix.single j i 1 := by
  ext k l
  simp only [Matrix.transpose_apply, frobPow, Matrix.map_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2
  · exact one_pow _
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · exact zero_pow (by positivity)

theorem twistTensor_faithful {F : Type} [Field F] [CharP F 2] (a : ℕ) :
    (FFModel.twistTensor a (StatedSL 2 F)).Faithful := by
  rintro ⟨g, hg⟩ hγ
  have key : ∀ X : Matrix (Fin 2) (Fin 2) F, (frobPow a X)ᵀ = X →
      (g : Matrix (Fin 2) (Fin 2) F) * X * (frobPow a (g : Matrix (Fin 2) (Fin 2) F))ᵀ = X := by
    intro X hX
    have h1 := Subgroup.mem_bot.mp (hγ (Multiplicative.ofAdd X) hX)
    have h2 := congrArg Multiplicative.toAdd h1
    simp only [FFModel.twistTensor, twistAct] at h2
    exact add_neg_eq_zero.mp h2
  have hE (i : Fin 2) := key _ ((frobPow_single_transpose a i i).trans rfl)
  have hX4 := key (Matrix.single 0 1 1 + Matrix.single 1 0 1) (by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [frobPow])
  have hdet := det_eq_one_of_mem_statedSL hg
  set m := (g : Matrix (Fin 2) (Fin 2) F) with hm
  have e00 := congrFun (congrFun (hE 0) 1) 1
  have e11 := congrFun (congrFun (hE 1) 0) 0
  have e0 := congrFun (congrFun (hE 0) 0) 0
  have e4 := congrFun (congrFun hX4 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.transpose_apply,
    frobPow, Matrix.map_apply, Matrix.add_apply] at e00 e11 e0 e4
  simp at e00 e11 e0 e4
  rw [Matrix.det_fin_two] at hdet
  have hdet' : m 0 0 * m 1 1 = 1 := by
    rw [e00, e11] at hdet
    simpa using hdet
  have e4' : m 0 0 * m 1 1 ^ 2 ^ a = 1 := by
    rw [e11] at e4
    simpa using e4
  have hpow : m 0 0 ^ 2 ^ a * m 1 1 ^ 2 ^ a = 1 := by rw [← mul_pow, hdet', one_pow]
  have hs' : m 1 1 ^ 2 ^ a ≠ 0 := fun h => by
    rw [h, mul_zero] at e4'
    exact zero_ne_one e4'
  have hpp : m 0 0 = m 0 0 ^ 2 ^ a := mul_right_cancel₀ hs' (e4'.trans hpow.symm)
  have hp2 : m 0 0 * m 0 0 = 1 := by
    rw [← hpp] at e0
    exact e0
  have hp1 : m 0 0 = 1 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have : (m 0 0 - 1) * (m 0 0 - 1) = 0 := by linear_combination hp2 - (m 0 0 - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  have hs1 : m 1 1 = 1 := by
    rw [hp1, one_mul] at hdet'
    exact hdet'
  apply Subtype.ext
  apply Units.ext
  change m = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp1, hs1, e00, e11]

theorem card_eq_of_realizesVia_top {V : Type*} [CommGroup V] {D : FFModel}
    {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ ⊥ π) :
    Nat.card V = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  rw [← Subgroup.card_top (G := V)]
  exact Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)

theorem card_top_quot_bot (A : Type*) [Group A] :
    Nat.card (↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤) = Nat.card A := by
  rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
    Subgroup.card_top]

theorem card_eq_of_realizesVia_faithful {V : Type*} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H} (h : D.RealizesVia H ⊤ ⊥ π) :
    Nat.card ↥H = Nat.card D.Gam :=
  (Nat.card_congr (Equiv.ofBijective π ⟨h.injective_of_faithful hD, h.1⟩)).symm

theorem card_eq_of_realizesVia_tensorPair {V : Type*} [CommGroup V] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {Γ₁ Γ₂ : Subgroup (GL ι F)} {H : Subgroup (MulAut V)}
    {π : (tensorPairModel Γ₁ Γ₂).Gam →* ↥H} (h : (tensorPairModel Γ₁ Γ₂).RealizesVia H ⊤ ⊥ π) :
    Nat.card V = Nat.card F ^ (Fintype.card ι * Fintype.card ι) := by
  rw [card_eq_of_realizesVia_top h]
  change Nat.card (↥(⊤ : Subgroup (Multiplicative (Matrix ι ι F))) ⧸
    (⊥ : Subgroup (Multiplicative (Matrix ι ι F))).subgroupOf ⊤) = _
  rw [card_top_quot_bot, Nat.card_congr Multiplicative.toAdd, Matrix.card_matrix,
    Nat.card_eq_fintype_card (α := ι)]

end CFSG.Quasithin.Vol2.Ch10.SecA

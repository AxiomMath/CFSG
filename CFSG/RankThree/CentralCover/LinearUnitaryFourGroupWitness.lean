module

public import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.LieType.Universal.SpinOmega.Center

public noncomputable section

namespace CFSG.RankThree.CentralCover

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped Pointwise

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

abbrev statedProjMk (S : Subgroup (GL ι F)) : S →* StatedProj S :=
  QuotientGroup.mk' _

theorem statedProjMk_surjective (S : Subgroup (GL ι F)) :
    Function.Surjective (statedProjMk S) :=
  QuotientGroup.mk'_surjective _

theorem ker_statedProjMk_le_center (S : Subgroup (GL ι F)) :
    (statedProjMk S).ker ≤ center S := by
  rw [QuotientGroup.ker_mk']
  exact CFSG.LieType.Universal.Spin.statedScalars_subgroupOf_le_center S

end Proj

namespace CycledFourGroup

variable {S T : Type*} [Group S] [Group T] {r₁ r₂ r₃ a₀ b₀ : S}

theorem quotient_package (h : CycledFourGroup r₁ r₂ r₃ a₀) (hb : b₀⁻¹ * a₀ * b₀ = a₀⁻¹)
    (hb2 : b₀ ^ 2 = 1) (ρ : S →* T) (hρ : ρ.ker ≤ center S) :
    IsKleinFour ((closure {r₁, r₂, r₃}).map ρ) ∧
      (((closure {r₁, r₂, r₃}).map ρ : Subgroup T) : Set T) = {1, ρ r₁, ρ r₂, ρ r₃} ∧
      ρ r₁ ≠ 1 ∧ ρ r₂ ≠ 1 ∧ ρ r₃ ≠ 1 ∧ ρ r₁ ≠ ρ r₂ ∧ ρ r₁ ≠ ρ r₃ ∧ ρ r₂ ≠ ρ r₃ ∧
      orderOf (ρ a₀) = 3 ∧ ρ a₀ * ρ r₁ * (ρ a₀)⁻¹ = ρ r₂ ∧ ρ a₀ * ρ r₂ * (ρ a₀)⁻¹ = ρ r₃ ∧
      ρ a₀ * ρ r₃ * (ρ a₀)⁻¹ = ρ r₁ ∧
      orderOf (ρ b₀) = 2 ∧ (ρ b₀)⁻¹ * ρ a₀ * ρ b₀ = (ρ a₀)⁻¹ ∧
      ρ a₀ ∈ normalizer (((closure {r₁, r₂, r₃}).map ρ : Subgroup T) : Set T) ∧
      (closure {r₁, r₂, r₃}).map ρ ⊓ zpowers (ρ a₀) = ⊥ ∧
      (((closure {r₁, r₂, r₃}).map ρ : Subgroup T) : Set T) * (zpowers (ρ a₀) : Set T) =
        ((closure {r₁, r₂, r₃}).map ρ ⊔ zpowers (ρ a₀) : Subgroup T) ∧
      Nat.card ((closure {r₁, r₂, r₃}).map ρ ⊔ zpowers (ρ a₀) : Subgroup T) = 12 ∧
      Set.InjOn ρ (closure {r₁, r₂, r₃} ⊔ zpowers a₀ : Subgroup S) := by
  obtain ⟨hinj, h', hV, hbc, hb2'⟩ := h.quotient_witness hb hb2 ρ hρ
  obtain ⟨hK, ha3, hN, hdisj, hmul, hcard⟩ := h'.quotient_facts hV
  exact ⟨hK, hV, h'.ne_one, h'.two_ne_one, h'.three_ne_one, h'.one_ne_two, h'.one_ne_three,
    h'.two_ne_three, ha3, h'.conj_one, h'.conj_two, h'.conj_three, hb2', hbc, hN, hdisj, hmul,
    hcard, hinj⟩

end CycledFourGroup

section Odd

variable (F : Type) [Field F]

@[expose] def oddDiag₁ : GL (Fin 3) F :=
  ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]⟩

@[expose] def oddDiag₂ : GL (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]⟩

@[expose] def oddDiag₃ : GL (Fin 3) F :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]⟩

@[expose] def oddA₀ : GL (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]⟩

@[expose] def oddB₀ : GL (Fin 3) F :=
  ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, -1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]⟩

theorem oddCycled (hF : ringChar F ≠ 2) :
    CycledFourGroup (oddDiag₁ F) (oddDiag₂ F) (oddDiag₃ F) (oddA₀ F) where
  ne_one h := by
    have h11 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 1 1) h
    simp only [oddDiag₁, Units.val_one, one_apply_eq] at h11
    exact Ring.neg_one_ne_one_of_char_ne_two hF h11
  sq_eq_one := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [oddDiag₁, sq, mul_apply, Fin.sum_univ_three, one_apply])
  mul_eq := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [oddDiag₁, oddDiag₂, oddDiag₃, mul_apply, Fin.sum_univ_three])
  conj_one := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [oddDiag₁, oddDiag₂, oddA₀, mul_apply, Fin.sum_univ_three])
  conj_two := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [oddDiag₂, oddDiag₃, oddA₀, mul_apply, Fin.sum_univ_three])
  cube := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [oddA₀, pow_three, mul_apply, Fin.sum_univ_three, one_apply])

theorem oddB₀_conj : (oddB₀ F)⁻¹ * oddA₀ F * oddB₀ F = (oddA₀ F)⁻¹ :=
  Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [oddA₀, oddB₀, mul_apply, Fin.sum_univ_three])

theorem oddB₀_sq : oddB₀ F ^ 2 = 1 :=
  Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [oddB₀, sq, mul_apply, Fin.sum_univ_three, one_apply])

theorem det_oddDiag₁ : (oddDiag₁ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [oddDiag₁, det_fin_three]

theorem det_oddDiag₂ : (oddDiag₂ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [oddDiag₂, det_fin_three]

theorem det_oddDiag₃ : (oddDiag₃ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [oddDiag₃, det_fin_three]

theorem det_oddA₀ : (oddA₀ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [oddA₀, det_fin_three]

theorem det_oddB₀ : (oddB₀ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [oddB₀, det_fin_three]

section Unitary

variable {F} {q : ℕ} (hq : Odd q)
include hq

theorem unitary_oddDiag₁ : ((oddDiag₁ F : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
    (oddDiag₁ F : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddDiag₁, mul_apply, Fin.sum_univ_three, one_apply, hq.neg_one_pow, zero_pow hq0]

theorem unitary_oddDiag₂ : ((oddDiag₂ F : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
    (oddDiag₂ F : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddDiag₂, mul_apply, Fin.sum_univ_three, one_apply, hq.neg_one_pow, zero_pow hq0]

theorem unitary_oddDiag₃ : ((oddDiag₃ F : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
    (oddDiag₃ F : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddDiag₃, mul_apply, Fin.sum_univ_three, one_apply, hq.neg_one_pow, zero_pow hq0]

theorem unitary_oddA₀ : ((oddA₀ F : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
    (oddA₀ F : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddA₀, mul_apply, Fin.sum_univ_three, one_apply, zero_pow hq0]

theorem unitary_oddB₀ : ((oddB₀ F : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ *
    (oddB₀ F : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddB₀, mul_apply, Fin.sum_univ_three, one_apply, hq.neg_one_pow, zero_pow hq0]

end Unitary

end Odd

section Even

variable (F : Type) [Field F] [CharP F 2]

@[expose] def evenU₁ : GL (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero]⟩

@[expose] def evenU₂ : GL (Fin 3) F :=
  ⟨!![1, 1, 1; 0, 1, 0; 0, 0, 1], !![1, 1, 1; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero]⟩

@[expose] def evenU₃ : GL (Fin 3) F :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero]⟩

@[expose] def evenA₀ : GL (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], !![1, 0, 0; 0, 1, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero],
    by ext i j; fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero]⟩

@[expose] def evenB₀ : GL (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]⟩

theorem evenCycled : CycledFourGroup (evenU₁ F) (evenU₂ F) (evenU₃ F) (evenA₀ F) where
  ne_one h := by
    have h01 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 1) h
    simp [evenU₁] at h01
  sq_eq_one := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [evenU₁, sq, mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero])
  mul_eq := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [evenU₁, evenU₂, evenU₃, mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  conj_one := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [evenU₁, evenU₂, evenA₀, mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  conj_two := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [evenU₂, evenU₃, evenA₀, mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero])
  cube := Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [evenA₀, pow_three, mul_apply, Fin.sum_univ_three, one_apply, CharTwo.add_self_eq_zero])

theorem evenB₀_conj : (evenB₀ F)⁻¹ * evenA₀ F * evenB₀ F = (evenA₀ F)⁻¹ :=
  Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;> simp [evenA₀, evenB₀, mul_apply, Fin.sum_univ_three])

omit [CharP F 2] in
theorem evenB₀_sq : evenB₀ F ^ 2 = 1 :=
  Units.ext (by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [evenB₀, sq, mul_apply, Fin.sum_univ_three, one_apply])

theorem det_evenU₁ : (evenU₁ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [evenU₁, det_fin_three]

theorem det_evenU₂ : (evenU₂ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [evenU₂, det_fin_three]

theorem det_evenU₃ : (evenU₃ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [evenU₃, det_fin_three]

theorem det_evenA₀ : (evenA₀ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [evenA₀, det_fin_three, CharTwo.neg_eq]

theorem det_evenB₀ : (evenB₀ F : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [evenB₀, det_fin_three, CharTwo.neg_eq]

end Even

section Elements

variable (F : Type) [Field F]

@[expose] def slOdd₁ : StatedSL 3 F := ⟨oddDiag₁ F, subset_closure (det_oddDiag₁ F)⟩
@[expose] def slOdd₂ : StatedSL 3 F := ⟨oddDiag₂ F, subset_closure (det_oddDiag₂ F)⟩
@[expose] def slOdd₃ : StatedSL 3 F := ⟨oddDiag₃ F, subset_closure (det_oddDiag₃ F)⟩
@[expose] def slOddA₀ : StatedSL 3 F := ⟨oddA₀ F, subset_closure (det_oddA₀ F)⟩
@[expose] def slOddB₀ : StatedSL 3 F := ⟨oddB₀ F, subset_closure (det_oddB₀ F)⟩

variable {q : ℕ} (hq : Odd q)

@[expose] def suOdd₁ : StatedSU 3 q F :=
  ⟨oddDiag₁ F, subset_closure ⟨det_oddDiag₁ F, unitary_oddDiag₁ hq⟩⟩
@[expose] def suOdd₂ : StatedSU 3 q F :=
  ⟨oddDiag₂ F, subset_closure ⟨det_oddDiag₂ F, unitary_oddDiag₂ hq⟩⟩
@[expose] def suOdd₃ : StatedSU 3 q F :=
  ⟨oddDiag₃ F, subset_closure ⟨det_oddDiag₃ F, unitary_oddDiag₃ hq⟩⟩
@[expose] def suOddA₀ : StatedSU 3 q F :=
  ⟨oddA₀ F, subset_closure ⟨det_oddA₀ F, unitary_oddA₀ hq⟩⟩
@[expose] def suOddB₀ : StatedSU 3 q F :=
  ⟨oddB₀ F, subset_closure ⟨det_oddB₀ F, unitary_oddB₀ hq⟩⟩

variable [CharP F 2]

@[expose] def slEven₁ : StatedSL 3 F := ⟨evenU₁ F, subset_closure (det_evenU₁ F)⟩
@[expose] def slEven₂ : StatedSL 3 F := ⟨evenU₂ F, subset_closure (det_evenU₂ F)⟩
@[expose] def slEven₃ : StatedSL 3 F := ⟨evenU₃ F, subset_closure (det_evenU₃ F)⟩
@[expose] def slEvenA₀ : StatedSL 3 F := ⟨evenA₀ F, subset_closure (det_evenA₀ F)⟩
@[expose] def slEvenB₀ : StatedSL 3 F := ⟨evenB₀ F, subset_closure (det_evenB₀ F)⟩

end Elements

section Relations

variable {F : Type} [Field F]

theorem slOddCycled (hF : ringChar F ≠ 2) :
    CycledFourGroup (slOdd₁ F) (slOdd₂ F) (slOdd₃ F) (slOddA₀ F) :=
  CycledFourGroup.of_injective (f := (StatedSL 3 F).subtype) (StatedSL 3 F).subtype_injective
    (oddCycled F hF)

theorem slOddB₀_conj : (slOddB₀ F)⁻¹ * slOddA₀ F * slOddB₀ F = (slOddA₀ F)⁻¹ :=
  Subtype.ext (oddB₀_conj F)

theorem slOddB₀_sq : slOddB₀ F ^ 2 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact oddB₀_sq F)

variable {q : ℕ}

theorem suOddCycled (hF : ringChar F ≠ 2) (hq : Odd q) :
    CycledFourGroup (suOdd₁ F hq) (suOdd₂ F hq) (suOdd₃ F hq) (suOddA₀ F hq) :=
  CycledFourGroup.of_injective (f := (StatedSU 3 q F).subtype) (StatedSU 3 q F).subtype_injective
    (oddCycled F hF)

theorem suOddB₀_conj (hq : Odd q) :
    (suOddB₀ F hq)⁻¹ * suOddA₀ F hq * suOddB₀ F hq = (suOddA₀ F hq)⁻¹ :=
  Subtype.ext (oddB₀_conj F)

theorem suOddB₀_sq (hq : Odd q) : suOddB₀ F hq ^ 2 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact oddB₀_sq F)

variable [CharP F 2]

theorem slEvenCycled : CycledFourGroup (slEven₁ F) (slEven₂ F) (slEven₃ F) (slEvenA₀ F) :=
  CycledFourGroup.of_injective (f := (StatedSL 3 F).subtype) (StatedSL 3 F).subtype_injective
    (evenCycled F)

theorem slEvenB₀_conj : (slEvenB₀ F)⁻¹ * slEvenA₀ F * slEvenB₀ F = (slEvenA₀ F)⁻¹ :=
  Subtype.ext (evenB₀_conj F)

theorem slEvenB₀_sq : slEvenB₀ F ^ 2 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact evenB₀_sq F)

end Relations

theorem ringChar_ne_two_of_card_eq_sq {F : Type} [Field F] [Finite F] {q : ℕ} (hq : Odd q)
    (hF : Nat.card F = q ^ 2) : ringChar F ≠ 2 := by
  have : Fintype F := Fintype.ofFinite F
  intro h2
  have h := FiniteField.even_card_iff_char_two.1 h2
  rw [← Nat.card_eq_fintype_card, hF] at h
  have h1 := Nat.odd_iff.1 (hq.pow (n := 2))
  omega

section LinearOdd

variable {F : Type} [Field F]

theorem linear_and_odd_unitary_three_central_cover_four_group_witness_linear_odd_quotient
    [Finite F] (hF : ringChar F ≠ 2) :
    let ρ := statedProjMk (StatedSL 3 F)
    let R : Subgroup (StatedSL 3 F) := closure {slOdd₁ F, slOdd₂ F, slOdd₃ F}
    let V := R.map ρ
    let a := ρ (slOddA₀ F)
    let b := ρ (slOddB₀ F)
    (fun g : StatedSL 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ''
        (R : Set (StatedSL 3 F)) =
      {1, !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1]} ∧
    ((slOddA₀ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] ∧
    ((slOddB₀ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, -1, 0; -1, 0, 0; 0, 0, -1] ∧
    IsKleinFour V ∧
    (V : Set (StatedProj (StatedSL 3 F))) = {1, ρ (slOdd₁ F), ρ (slOdd₂ F), ρ (slOdd₃ F)} ∧
    ρ (slOdd₁ F) ≠ 1 ∧ ρ (slOdd₂ F) ≠ 1 ∧ ρ (slOdd₃ F) ≠ 1 ∧ ρ (slOdd₁ F) ≠ ρ (slOdd₂ F) ∧
    ρ (slOdd₁ F) ≠ ρ (slOdd₃ F) ∧ ρ (slOdd₂ F) ≠ ρ (slOdd₃ F) ∧
    orderOf a = 3 ∧ a * ρ (slOdd₁ F) * a⁻¹ = ρ (slOdd₂ F) ∧
    a * ρ (slOdd₂ F) * a⁻¹ = ρ (slOdd₃ F) ∧ a * ρ (slOdd₃ F) * a⁻¹ = ρ (slOdd₁ F) ∧
    orderOf b = 2 ∧ b⁻¹ * a * b = a⁻¹ ∧
    a ∈ normalizer (V : Set (StatedProj (StatedSL 3 F))) ∧ V ⊓ zpowers a = ⊥ ∧
    (V : Set (StatedProj (StatedSL 3 F))) * (zpowers a : Set (StatedProj (StatedSL 3 F))) =
      (V ⊔ zpowers a : Subgroup (StatedProj (StatedSL 3 F))) ∧
    Nat.card (V ⊔ zpowers a : Subgroup (StatedProj (StatedSL 3 F))) = 12 ∧
    Set.InjOn ρ (R ⊔ zpowers (slOddA₀ F) : Subgroup (StatedSL 3 F)) := by
  intro ρ R V a b
  have hR : (R : Set (StatedSL 3 F)) = {1, slOdd₁ F, slOdd₂ F, slOdd₃ F} :=
    (slOddCycled hF).coe_closure
  refine ⟨?_, rfl, rfl, (slOddCycled hF).quotient_package slOddB₀_conj slOddB₀_sq ρ
    (ker_statedProjMk_le_center _)⟩
  rw [hR, Set.image_insert_eq, Set.image_insert_eq, Set.image_pair]
  rfl

theorem linear_and_odd_unitary_three_central_cover_four_group_witness_linear_odd_cover
    [Finite F] (hF : ringChar F ≠ 2) {K : Type*} [Group K] [Finite K]
    (π : K →* StatedProj (StatedSL 3 F)) (hπ : Function.Surjective π) (hZ : π.ker ≤ center K)
    (hZ3 : IsPGroup 3 π.ker) :
    let ρ := statedProjMk (StatedSL 3 F)
    let V := (Subgroup.closure {slOdd₁ F, slOdd₂ F, slOdd₃ F}).map ρ
    let a := ρ (slOddA₀ F)
    (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
    ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
      π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
      ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
        (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
          u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
          x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
        x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
        (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
        (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧ Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
        π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧ π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  intro ρ V a
  obtain ⟨-, h', hV, hbc, -⟩ := (slOddCycled hF).quotient_witness slOddB₀_conj slOddB₀_sq ρ
    (ker_statedProjMk_le_center _)
  exact h'.cover hbc hV π hπ hZ hZ3

end LinearOdd

section LinearEven

variable {F : Type} [Field F]

theorem linear_and_odd_unitary_three_central_cover_four_group_witness_linear_even_quotient
    [Finite F] [CharP F 2] :
    let ρ := statedProjMk (StatedSL 3 F)
    let R : Subgroup (StatedSL 3 F) := closure {slEven₁ F, slEven₂ F, slEven₃ F}
    let V := R.map ρ
    let a := ρ (slEvenA₀ F)
    let b := ρ (slEvenB₀ F)
    (fun g : StatedSL 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ''
        (R : Set (StatedSL 3 F)) =
      {M | ∃ s t : F, (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) ∧ M = !![1, s, t; 0, 1, 0; 0, 0, 1]} ∧
    ((slEvenA₀ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 1] ∧
    ((slEvenB₀ F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] ∧
    IsKleinFour V ∧
    (V : Set (StatedProj (StatedSL 3 F))) = {1, ρ (slEven₁ F), ρ (slEven₂ F), ρ (slEven₃ F)} ∧
    ρ (slEven₁ F) ≠ 1 ∧ ρ (slEven₂ F) ≠ 1 ∧ ρ (slEven₃ F) ≠ 1 ∧ ρ (slEven₁ F) ≠ ρ (slEven₂ F) ∧
    ρ (slEven₁ F) ≠ ρ (slEven₃ F) ∧ ρ (slEven₂ F) ≠ ρ (slEven₃ F) ∧
    orderOf a = 3 ∧ a * ρ (slEven₁ F) * a⁻¹ = ρ (slEven₂ F) ∧
    a * ρ (slEven₂ F) * a⁻¹ = ρ (slEven₃ F) ∧ a * ρ (slEven₃ F) * a⁻¹ = ρ (slEven₁ F) ∧
    orderOf b = 2 ∧ b⁻¹ * a * b = a⁻¹ ∧
    a ∈ normalizer (V : Set (StatedProj (StatedSL 3 F))) ∧ V ⊓ zpowers a = ⊥ ∧
    (V : Set (StatedProj (StatedSL 3 F))) * (zpowers a : Set (StatedProj (StatedSL 3 F))) =
      (V ⊔ zpowers a : Subgroup (StatedProj (StatedSL 3 F))) ∧
    Nat.card (V ⊔ zpowers a : Subgroup (StatedProj (StatedSL 3 F))) = 12 ∧
    Set.InjOn ρ (R ⊔ zpowers (slEvenA₀ F) : Subgroup (StatedSL 3 F)) := by
  intro ρ R V a b
  have hR : (R : Set (StatedSL 3 F)) = {1, slEven₁ F, slEven₂ F, slEven₃ F} :=
    (slEvenCycled (F := F)).coe_closure
  refine ⟨?_, rfl, rfl, (slEvenCycled (F := F)).quotient_package slEvenB₀_conj slEvenB₀_sq ρ
    (ker_statedProjMk_le_center _)⟩
  rw [hR, Set.image_insert_eq, Set.image_insert_eq, Set.image_pair]
  ext M
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, by simp [one_fin_three]⟩
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, rfl⟩
    · exact ⟨1, 1, Or.inr rfl, Or.inr rfl, rfl⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, rfl⟩
  · rintro ⟨s, t, hs | hs, ht | ht, rfl⟩ <;> subst hs <;> subst ht
    · left
      simp [one_fin_three]
    · right; right; right; rfl
    · right; left; rfl
    · right; right; left; rfl

theorem linear_and_odd_unitary_three_central_cover_four_group_witness_linear_even_cover
    [Finite F] [CharP F 2] {K : Type*} [Group K] [Finite K]
    (π : K →* StatedProj (StatedSL 3 F)) (hπ : Function.Surjective π) (hZ : π.ker ≤ center K)
    (hZ3 : IsPGroup 3 π.ker) :
    let ρ := statedProjMk (StatedSL 3 F)
    let V := (Subgroup.closure {slEven₁ F, slEven₂ F, slEven₃ F}).map ρ
    let a := ρ (slEvenA₀ F)
    (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
    ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
      π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
      ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
        (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
          u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
          x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
        x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
        (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
        (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧ Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
        π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧ π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  intro ρ V a
  obtain ⟨-, h', hV, hbc, -⟩ := (slEvenCycled (F := F)).quotient_witness slEvenB₀_conj
    slEvenB₀_sq ρ (ker_statedProjMk_le_center _)
  exact h'.cover hbc hV π hπ hZ hZ3

end LinearEven

section UnitaryOdd

variable {F : Type} [Field F]

theorem linear_and_odd_unitary_three_central_cover_four_group_witness_unitary_odd_quotient
    [Finite F] {q : ℕ} (_hq : IsPrimePow q) (hqodd : Odd q) (hF : Nat.card F = q ^ 2) :
    let ρ := statedProjMk (StatedSU 3 q F)
    let R : Subgroup (StatedSU 3 q F) := closure {suOdd₁ F hqodd, suOdd₂ F hqodd, suOdd₃ F hqodd}
    let V := R.map ρ
    let a := ρ (suOddA₀ F hqodd)
    let b := ρ (suOddB₀ F hqodd)
    (fun g : StatedSU 3 q F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ''
        (R : Set (StatedSU 3 q F)) =
      {1, !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1],
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1]} ∧
    ((suOddA₀ F hqodd : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] ∧
    ((suOddB₀ F hqodd : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, -1, 0; -1, 0, 0; 0, 0, -1] ∧
    IsKleinFour V ∧
    (V : Set (StatedProj (StatedSU 3 q F))) =
      {1, ρ (suOdd₁ F hqodd), ρ (suOdd₂ F hqodd), ρ (suOdd₃ F hqodd)} ∧
    ρ (suOdd₁ F hqodd) ≠ 1 ∧ ρ (suOdd₂ F hqodd) ≠ 1 ∧ ρ (suOdd₃ F hqodd) ≠ 1 ∧
    ρ (suOdd₁ F hqodd) ≠ ρ (suOdd₂ F hqodd) ∧ ρ (suOdd₁ F hqodd) ≠ ρ (suOdd₃ F hqodd) ∧
    ρ (suOdd₂ F hqodd) ≠ ρ (suOdd₃ F hqodd) ∧
    orderOf a = 3 ∧ a * ρ (suOdd₁ F hqodd) * a⁻¹ = ρ (suOdd₂ F hqodd) ∧
    a * ρ (suOdd₂ F hqodd) * a⁻¹ = ρ (suOdd₃ F hqodd) ∧
    a * ρ (suOdd₃ F hqodd) * a⁻¹ = ρ (suOdd₁ F hqodd) ∧
    orderOf b = 2 ∧ b⁻¹ * a * b = a⁻¹ ∧
    a ∈ normalizer (V : Set (StatedProj (StatedSU 3 q F))) ∧ V ⊓ zpowers a = ⊥ ∧
    (V : Set (StatedProj (StatedSU 3 q F))) * (zpowers a : Set (StatedProj (StatedSU 3 q F))) =
      (V ⊔ zpowers a : Subgroup (StatedProj (StatedSU 3 q F))) ∧
    Nat.card (V ⊔ zpowers a : Subgroup (StatedProj (StatedSU 3 q F))) = 12 ∧
    Set.InjOn ρ (R ⊔ zpowers (suOddA₀ F hqodd) : Subgroup (StatedSU 3 q F)) := by
  intro ρ R V a b
  have hF2 := ringChar_ne_two_of_card_eq_sq hqodd hF
  have hR : (R : Set (StatedSU 3 q F)) = {1, suOdd₁ F hqodd, suOdd₂ F hqodd, suOdd₃ F hqodd} :=
    (suOddCycled hF2 hqodd).coe_closure
  refine ⟨?_, rfl, rfl, (suOddCycled hF2 hqodd).quotient_package (suOddB₀_conj hqodd)
    (suOddB₀_sq hqodd) ρ (ker_statedProjMk_le_center _)⟩
  rw [hR, Set.image_insert_eq, Set.image_insert_eq, Set.image_pair]
  rfl

theorem linear_and_odd_unitary_three_central_cover_four_group_witness_unitary_odd_cover
    [Finite F] {q : ℕ} (_hq : IsPrimePow q) (hqodd : Odd q) (hF : Nat.card F = q ^ 2)
    {K : Type*} [Group K] [Finite K] (π : K →* StatedProj (StatedSU 3 q F))
    (hπ : Function.Surjective π) (hZ : π.ker ≤ center K) (hZ3 : IsPGroup 3 π.ker) :
    let ρ := statedProjMk (StatedSU 3 q F)
    let V := (Subgroup.closure {suOdd₁ F hqodd, suOdd₂ F hqodd, suOdd₃ F hqodd}).map ρ
    let a := ρ (suOddA₀ F hqodd)
    (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
    ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
      π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
      ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
        (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
          u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
          x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
        x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
        (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
        (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧ Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
        π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧ π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  intro ρ V a
  obtain ⟨-, h', hV, hbc, -⟩ := (suOddCycled (ringChar_ne_two_of_card_eq_sq hqodd hF)
    hqodd).quotient_witness (suOddB₀_conj hqodd) (suOddB₀_sq hqodd) ρ
    (ker_statedProjMk_le_center _)
  exact h'.cover hbc hV π hπ hZ hZ3

end UnitaryOdd

end CFSG.RankThree.CentralCover

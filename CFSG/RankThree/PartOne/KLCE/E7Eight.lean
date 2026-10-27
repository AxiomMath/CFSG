module

public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.KLCE.CharTwoRep
public import CFSG.RankThree.PartOne.KLCE.PowConj
public import CFSG.RankThree.PartOne.KLCE.FrobAut
public import CFSG.RankThree.PartOne.KLCE.A1Type
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalDescent
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.RankThree.PartOne.KE.E7EightBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)

open CFSG.RankThree.Classical (conjSL conjSL_one)

open scoped Matrix Polynomial MatrixGroups Pointwise

section Frame


@[expose] def E78Rep (L : Type) [Field L] (n : ModGL .E7 L) : Prop :=
  ∃ hnm : n ∈ monomialSubgroup .E7 L,
    (∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = e7O8W *ᵥ u) ∧
    (∀ A, n * rootSL2 .E7 L e7O8Alpha A * n⁻¹ = rootSL2 .E7 L e7O8Alpha A) ∧
    (∀ A, n * rootSL2 .E7 L e7O8Beta A * n⁻¹ = rootSL2 .E7 L e7O8Gamma A) ∧
    (∀ A, n * rootSL2 .E7 L e7O8Gamma A * n⁻¹ = rootSL2 .E7 L e7O8Beta A)

theorem e78Rep_wordRep (L : Type) [Field L] [CharP L 2] :
    E78Rep L (wordRep .E7 L [0, 1, 2, 3, 4]) := by
  obtain ⟨-, hwα, hwβ, hwγ, -⟩ := E7_three_A1_native_product_scalar_kernel_and_exact_Frobenius_swap
  obtain ⟨hαr, hβr, hγr⟩ := e7A1_isRoot
  refine ⟨wordRep_mem_monomial _, fun u => ?_, fun A => ?_, fun A => ?_, fun A => ?_⟩
  · rw [wordRep_weylImage]
    exact wordProd_smul_eq_wordMat_mulVec .E7 [0, 1, 2, 3, 4] u
  · rw [wordRep_conj_rootSL2 hαr, hwα]
  · rw [wordRep_conj_rootSL2 hβr, hwβ]
  · rw [wordRep_conj_rootSL2 hγr, hwγ]

theorem e7Eight_frame {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp7 : 7 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E7) ∧
      ∃ n₀ : ModGL .E7 L, n₀ ∈ adjointGroup .E7 L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧ E78Rep L n₀ ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma)) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ b : Fin Tag.E7.rank → Lˣ,
            rootDiagUnit .E7 b ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
              (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma) →
            orderOf (rootDiagUnit .E7 b) = p →
            rootCharKernel b ⊆ threeRootSet e7O8Alpha e7O8Beta e7O8Gamma) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K₀
  have : CharP K₀ 2 := ⟨fun x => by
    rw [← (algebraMap K₀ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  have hq2 : 2 ≤ Nat.card K₀ := Finite.one_lt_card
  have : Fintype K₀ := Fintype.ofFinite K₀
  set Fr : L →+* L := iterateFrobenius L 2 f₀ with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K₀ := fun c => by
    rw [hK₀]
    exact iterateFrobenius_def 2 f₀ c
  have hℓq : 2 ∣ Nat.card K₀ := by
    rw [hK₀]
    exact dvd_pow_self _ (by omega)
  have hpf' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨-, hpq, hord8⟩ := CTE6.e6Eight_data hp (by omega) hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E7) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))
  obtain ⟨hk, -, -, -, -⟩ := E7_three_A1_native_product_scalar_kernel_and_exact_Frobenius_swap
  obtain ⟨-, hc12, hc13, hc23, -, -, -, -, -, -⟩ := hk L
  obtain ⟨hαr, hβr, hγr⟩ := e7A1_isRoot
  have hrep := e78Rep_wordRep L
  have hrep2 := hrep
  obtain ⟨hnm, hnW, -, -, -⟩ := hrep2
  set n : ModGL .E7 L := wordRep .E7 L [0, 1, 2, 3, 4] with hndef
  have hnC : n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' hnm
  have hnfix : Units.map (entrywiseHom Fr) n = n := by
    have := wordRep_fixed (τ := .E7) (iterateFrobeniusEquiv L 2 f₀) [0, 1, 2, 3, 4]
    rw [CFSG.LieType.AlgebraicGroups.iterateFrobeniusEquiv_toRingHom] at this
    exact this
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e7O8W Fr).map (rootDiagUnitHom .E7 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusSigma_eq_map_fixedBlockTuples_three hc12 hc13 hc23 hT hαr hβr hγr
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  obtain ⟨hcycB, hcardB⟩ := e7Eight_block_cyclic Fr hFr Nat.prime_two hℓq
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr))
      (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma)) = Nat.card K₀ ^ 4 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    exact hcardB
  have hN : Nat.card K₀ ^ 4 + 1 ≠ 0 := by omega
  have hR : ¬ (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 - 1 :=
    CTTw.not_dvd_pow_sub_one hord8 (by norm_num)
  have hord : p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p =
      p ^ (Nat.card K₀ ^ 4 + 1).factorization p := by
    have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 8 → ¬ 8 ∣ d := by decide
    have h1 : 1 ≤ Nat.card K₀ ^ 8 := Nat.one_le_pow _ _ (by omega)
    refine ordProj_card_adjointGroup_E7 hp (by omega) hpq hord8 (d₀ := 8) (by decide) hrest hN
      (R := (Nat.card K₀ : ℤ) ^ 4 - 1) ?_ hR
    push_cast [Nat.cast_sub h1]
    ring
  refine ⟨hordW, n, hnC, hnfix, hrep, Nat.card K₀ ^ 4 + 1, hN, hZcard, hord, ?_⟩
  intro b hb hbp
  rw [hZeq] at hb
  obtain ⟨b', hb', hbb'⟩ := hb
  have : b' = b := hinj0 hbb'
  subst this
  rw [e7Eight_rootCharKernel Fr hFr hp (by omega) hord8 hb'.1
    (KE.pow_eq_one_of_orderOf_rootDiagUnit hbp) (KE.ne_one_of_orderOf_rootDiagUnit hp hbp)]
  exact Set.Subset.rfl

end Frame

section Family


theorem e7A1Mul_injective_of_charTwo (L : Type) [Field L] [CharP L 2] :
    Function.Injective (e7A1Mul L) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B, C⟩ h
  obtain ⟨l, hl, hA, hB, hC⟩ := (e7A1Mul_eq_one_iff A B C).1 h
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hl1 : l = 1 := by
    have h3 : (l - 1) ^ 2 = 0 := by linear_combination hl + (1 - l) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
  subst hl1
  have h1 : ∀ M : SL2 L, (M : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) (1 : L) → M = 1 :=
    fun M hM => Subtype.ext (by rw [hM, map_one]; rfl)
  exact Prod.ext (h1 A hA) (Prod.ext (h1 B hB) (h1 C hC))

theorem e7Eight_fixed_triple {L : Type} [Field L] [CharP L 2] (Fr : L →+* L) {N : ModGL .E7 L}
    (hn₁ : ∀ A : SL2 L, N * rootSL2 .E7 L e7O8Alpha A * N⁻¹ = rootSL2 .E7 L e7O8Alpha A)
    (hn₂ : ∀ B : SL2 L, N * rootSL2 .E7 L e7O8Beta B * N⁻¹ = rootSL2 .E7 L e7O8Gamma B)
    (hn₃ : ∀ C : SL2 L, N * rootSL2 .E7 L e7O8Gamma C * N⁻¹ = rootSL2 .E7 L e7O8Beta C)
    {q : ModGL .E7 L} (hq : q ∈ rootSpan .E7 L (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma))
    (hqR : N * Units.map (entrywiseHom Fr) q * N⁻¹ = q) :
    ∃ A B C : SL2 L, q = rootSL2 .E7 L e7O8Alpha A * rootSL2 .E7 L e7O8Beta B *
        rootSL2 .E7 L e7O8Gamma C ∧ Matrix.SpecialLinearGroup.map Fr A = A ∧
      Matrix.SpecialLinearGroup.map Fr C = B ∧ Matrix.SpecialLinearGroup.map Fr B = C := by
  obtain ⟨hk, -, -, -, -⟩ := E7_three_A1_native_product_scalar_kernel_and_exact_Frobenius_swap
  obtain ⟨-, hc12, hc13, hc23, -, -, -, -, -, -⟩ := hk L
  obtain ⟨hαr, hβr, hγr⟩ := e7A1_isRoot
  rw [rootSpan_threeRootSet hαr hβr hγr] at hq
  obtain ⟨A, B, C, rfl⟩ := mem_sup_three hc12 hc13 hc23 hq
  have h : N * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7O8Alpha A * rootSL2 .E7 L e7O8Beta B *
      rootSL2 .E7 L e7O8Gamma C) * N⁻¹ =
      rootSL2 .E7 L e7O8Alpha (Matrix.SpecialLinearGroup.map Fr A) *
        rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Fr C) *
          rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Fr B) := by
    rw [map_mul, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field,
      entrywise_rootSL2_of_field]
    calc N * (rootSL2 .E7 L e7O8Alpha (Matrix.SpecialLinearGroup.map Fr A) *
          rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Fr B) *
            rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Fr C)) * N⁻¹
        = (N * rootSL2 .E7 L e7O8Alpha (Matrix.SpecialLinearGroup.map Fr A) * N⁻¹) *
          (N * rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Fr B) * N⁻¹) *
          (N * rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Fr C) * N⁻¹) := by group
      _ = rootSL2 .E7 L e7O8Alpha (Matrix.SpecialLinearGroup.map Fr A) *
          rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Fr B) *
            rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Fr C) := by
          rw [hn₁, hn₂, hn₃]
      _ = _ := by
          rw [mul_assoc, mul_assoc, ((hc23 (Matrix.SpecialLinearGroup.map Fr C)
            (Matrix.SpecialLinearGroup.map Fr B)).symm).eq]
  rw [h] at hqR
  have hinj := e7A1Mul_injective_of_charTwo L
  have h2 : e7A1Mul L (A, B, C) = e7A1Mul L (Matrix.SpecialLinearGroup.map Fr A,
      Matrix.SpecialLinearGroup.map Fr C, Matrix.SpecialLinearGroup.map Fr B) := by
    rw [e7A1Mul_apply, e7A1Mul_apply]
    exact hqR.symm
  have h3 := hinj h2
  simp only [Prod.mk.injEq] at h3
  obtain ⟨hA, hB, hC⟩ := h3
  exact ⟨A, B, C, rfl, hA.symm, hB.symm, hC.symm⟩

theorem e7Eight_family {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {f₀ p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀)) (σ : K ≃+* K) (hσord : orderOf σ = p)
    (hσ : ∀ a, σ a = a ^ 2 ^ f₀) {n₀ : ModGL .E7 L}
    (hRn₀ : E78Rep L n₀) :
    ∃ (ι' : Type) (P : ι' → Subgroup (ModGL .E7 L)), Nonempty ι' ∧
      IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p))
        (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma) P ∧
      rootSpan .E7 L (threeRootSet e7O8Alpha e7O8Beta e7O8Gamma) ⊓
        twistedFixedPoints (n₀ ^ p)
          (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) ≤ ⨆ i, P i ∧
      (∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u) ∧
      ∀ i, LayerDatum p
        (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) (P i) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hp2 : p ≠ 2 := by omega
  obtain ⟨kodd, hkodd⟩ := hp.odd_of_ne_two hp2
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hΦ₀K : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [hΦ₀def, iterateFrobenius_def, ← map_pow, hσ]
  have hΦFr : ∀ c, Fr (Φ₀ c) = Φ₀ (Fr c) := fun c => by
    rw [hFrdef, hΦ₀def, iterateFrobenius_def, iterateFrobenius_def, iterateFrobenius_def,
      iterateFrobenius_def, ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨hk, -, -, -, -⟩ := E7_three_A1_native_product_scalar_kernel_and_exact_Frobenius_swap
  obtain ⟨-, hc12, hc13, hc23, -, -, -, hbg, hbginj, -⟩ := hk L
  obtain ⟨hαr, hβr, hγr⟩ := e7A1_isRoot
  have hinj23 : ∀ B C B' C' : SL2 L,
      rootSL2 .E7 L e7O8Beta B * rootSL2 .E7 L e7O8Gamma C =
        rootSL2 .E7 L e7O8Beta B' * rootSL2 .E7 L e7O8Gamma C' → B = B' ∧ C = C' := by
    intro B C B' C' h
    rw [← hbg, ← hbg] at h
    have := hbginj h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨-, -, hn₁, hn₂, hn₃⟩ := hRn₀
  have hcomm₁ : ∀ A : SL2 L, Commute n₀ (rootSL2 .E7 L e7O8Alpha A) := fun A =>
    mul_inv_eq_iff_eq_mul.1 (hn₁ A)
  have hN₁ : ∀ A : SL2 L, n₀ ^ p * rootSL2 .E7 L e7O8Alpha A * (n₀ ^ p)⁻¹ =
      rootSL2 .E7 L e7O8Alpha A := fun A =>
    mul_inv_eq_iff_eq_mul.2 ((hcomm₁ A).pow_left p).eq
  have hNβ : ∀ B : SL2 L, n₀ ^ p * rootSL2 .E7 L e7O8Beta B * (n₀ ^ p)⁻¹ =
      rootSL2 .E7 L e7O8Gamma B := fun B => by
    rw [hkodd]
    exact pow_odd_conj_swap (hn₂ B) (hn₃ B) kodd
  have hNγ : ∀ B : SL2 L, n₀ ^ p * rootSL2 .E7 L e7O8Gamma B * (n₀ ^ p)⁻¹ =
      rootSL2 .E7 L e7O8Beta B := fun B => by
    rw [hkodd]
    exact pow_odd_conj_swap (hn₃ B) (hn₂ B) kodd
  have hnc : n₀ ^ p ∈ Subgroup.centralizer
      (rootRankOneGroup .E7 L e7O8Alpha : Set (ModGL .E7 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact ((hcomm₁ A).pow_left p).eq.symm
  have hn₀c : n₀ ∈ Subgroup.centralizer
      (rootRankOneGroup .E7 L e7O8Alpha : Set (ModGL .E7 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, rfl⟩
    exact (hcomm₁ A).eq.symm
  have hS₁ : ∀ B : SL2 L, n₀ ^ p * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7O8Alpha B) *
      (n₀ ^ p)⁻¹ = rootSL2 .E7 L e7O8Alpha B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map
          (conjSL (1 : GL (Fin 2) L)) := fun B => a1_typeI_action Fr hFr hnc B
  have hpf₀ : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨k₂, _, _, _, hk₂card⟩ := exists_finite_field_into 2 (2 * (p * f₀)) (by omega) L
  have hk₂ : Nat.card k₂ = Nat.card K ^ 2 := by
    rw [hk₂card, hK, ← pow_mul, mul_comm]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hp.two_le])
  have hk4 : 4 ≤ Nat.card k₂ := by
    rw [hk₂]
    nlinarith
  have : CharP k₂ 2 := ⟨fun x => by
    rw [← (algebraMap k₂ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  let Fr2 : L →+* L := Fr.comp Fr
  have hFr2 : ∀ c, Fr2 c = c ^ Nat.card k₂ := fun c => by
    show Fr (Fr c) = c ^ Nat.card k₂
    rw [hk₂, hFr, hFr, ← pow_mul, sq]
  have hfix2 : ∀ c, Fr2 c = c ↔ c ∈ Set.range (algebraMap k₂ L) := fun c =>
    frobenius_fixed_iff Fr2 hFr2 c
  have hS₂ : ∀ B : SL2 L, B ∈ (Matrix.SpecialLinearGroup.map (algebraMap k₂ L)).range.map
      (conjSL (1 : GL (Fin 2) L)) ↔
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr B) = B := by
    intro B
    have hcomp : Matrix.SpecialLinearGroup.map Fr2 B =
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr B) := by
      ext i j
      simp [Fr2]
    rw [← hcomp, sl2_map_fixed_iff Fr2 hfix2 B]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rwa [conjSL_one]
    · intro hB
      exact ⟨B, hB, conjSL_one B⟩
  obtain ⟨hfin₁, hq₁⟩ := sl2_conj_range_quasisimple (L := L) (K := K) hK4 (1 : GL (Fin 2) L)
  obtain ⟨hfin₂, hq₂⟩ := sl2_conj_range_quasisimple (L := L) (K := k₂) hk4 (1 : GL (Fin 2) L)
  have hz₁ := sl2_conj_range_centralizer (K := K) (L := L) (1 : GL (Fin 2) L)
  have hz₂ := sl2_conj_range_centralizer (K := k₂) (L := L) (1 : GL (Fin 2) L)
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, hPtrue, hPfalse⟩ :=
    three_A1_family hc12 hc13 hc23 hαr hβr hγr hinj23 Fr (n₀ ^ p) hNβ hNγ _ _ hS₁ hS₂ hq₁ hq₂
      hz₁ hz₂
  have hrange₁ : (a1Hom .E7 K L e7O8Alpha).range = P true := by
    rw [hPtrue]
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨_, ⟨_, ⟨c, rfl⟩, conjSL_one _⟩, rfl⟩
    · rintro ⟨B, ⟨C, ⟨c, rfl⟩, rfl⟩, rfl⟩
      exact ⟨c, by rw [a1Hom_apply, conjSL_one]⟩
  refine ⟨Bool, P, ⟨true⟩, ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩, ?_, ?_, ?_⟩
  ·
    intro q hq
    obtain ⟨hqS, hqR⟩ := hq
    obtain ⟨A, B, C, rfl, hA, hCB, hBC⟩ := e7Eight_fixed_triple Fr hN₁ hNβ hNγ hqS hqR
    have hA' : n₀ ^ p * Units.map (entrywiseHom Fr) (rootSL2 .E7 L e7O8Alpha A) * (n₀ ^ p)⁻¹ =
        rootSL2 .E7 L e7O8Alpha A := by
      rw [entrywise_rootSL2_of_field, hN₁, hA]
    have hB : B ∈ (Matrix.SpecialLinearGroup.map (algebraMap k₂ L)).range.map
        (conjSL (1 : GL (Fin 2) L)) := (hS₂ B).2 (by rw [hBC]; exact hCB)
    rw [iSup_bool_eq, mul_assoc]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [hPtrue]
      exact ⟨A, (hS₁ A).1 hA', rfl⟩
    · rw [hPfalse]
      exact ⟨B, hB, by rw [pairHom_apply, hBC]⟩
  ·
    have hcomA : ∀ (A B C : SL2 L), Commute (rootSL2 .E7 L e7O8Alpha A)
        (rootSL2 .E7 L e7O8Beta B * rootSL2 .E7 L e7O8Gamma C) := fun A B C =>
      (hc12 A B).mul_right (hc13 A C)
    intro i j hij u hu v hv
    cases i <;> cases j
    · exact absurd rfl hij
    · rw [hPfalse] at hu
      rw [hPtrue] at hv
      obtain ⟨B, -, rfl⟩ := hu
      obtain ⟨A, -, rfl⟩ := hv
      exact (hcomA A B _).symm.eq
    · rw [hPtrue] at hu
      rw [hPfalse] at hv
      obtain ⟨A, -, rfl⟩ := hu
      obtain ⟨B, -, rfl⟩ := hv
      exact (hcomA A B _).eq
    · exact absurd rfl hij
  ·
    have hσ1 : σ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hσord
      exact hp.one_lt.ne hσord
    intro i
    cases i
    ·
      set ι₂ : k₂ →+* L := algebraMap k₂ L with hι₂
      let σ₂ : k₂ ≃+* k₂ := frobAut k₂ ((p + 1) * f₀)
      have hσ₂x : ∀ x : k₂, σ₂ x = x ^ 2 ^ ((p + 1) * f₀) := fun x => rfl
      have hσ₂ : ∀ x : k₂, ι₂ (σ₂ x) = Φ₀ (Fr (ι₂ x)) := fun x => by
        rw [hσ₂x, map_pow, hΦ₀def, hFrdef, iterateFrobenius_def, iterateFrobenius_def, ← pow_mul,
          ← pow_add, show f₀ * p + f₀ = (p + 1) * f₀ by ring]
      have hσ₂ne : σ₂ ≠ 1 :=
        frobAut_ne_one hk₂card (Nat.mul_pos (Nat.succ_pos p) hf₀) (by nlinarith [hp.two_le])
      let ρ' : Matrix.SpecialLinearGroup (Fin (0 + 2)) k₂ →* ModGL .E7 L :=
        (pairHom hc23 Fr).comp (Matrix.SpecialLinearGroup.map ι₂)
      have hρ'inj : Function.Injective ρ' :=
        (pairHom_injective hc23 hinj23 Fr).comp (map_specialLinear_injective _)
      have hS₂eq : (Matrix.SpecialLinearGroup.map ι₂).range.map (conjSL (1 : GL (Fin 2) L)) =
          (Matrix.SpecialLinearGroup.map ι₂).range := by
        ext B
        constructor
        · rintro ⟨C, hC, rfl⟩
          rwa [conjSL_one]
        · intro hB
          exact ⟨B, hB, conjSL_one B⟩
      have hrange₂ : ρ'.range = P false := by
        rw [hPfalse, hS₂eq]
        ext g
        constructor
        · rintro ⟨d, rfl⟩
          exact ⟨_, ⟨d, rfl⟩, rfl⟩
        · rintro ⟨B, ⟨d, rfl⟩, rfl⟩
          exact ⟨d, rfl⟩
      have hFr2fix : ∀ x : k₂, Fr (Φ₀ (Fr (ι₂ x))) = Φ₀ (ι₂ x) := fun x => by
        rw [hΦFr]
        congr 1
        exact (hfix2 _).2 ⟨x, rfl⟩
      have hF : ∀ d : Matrix.SpecialLinearGroup (Fin (0 + 2)) k₂,
          n₀ * Units.map (entrywiseHom Φ₀) (ρ' d) * n₀⁻¹ =
            ρ' (Matrix.SpecialLinearGroup.map σ₂.toRingHom d) := by
        intro d
        set B' : SL2 L := Matrix.SpecialLinearGroup.map ι₂ d with hB'
        have hi : Matrix.SpecialLinearGroup.map ι₂ (Matrix.SpecialLinearGroup.map σ₂.toRingHom d) =
            Matrix.SpecialLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.map Fr B') := by
          ext a b
          simp [hB', hσ₂]
        have hii : Matrix.SpecialLinearGroup.map Fr
            (Matrix.SpecialLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.map Fr B')) =
              Matrix.SpecialLinearGroup.map Φ₀ B' := by
          ext a b
          simp [hB', hFr2fix]
        have e1 : ρ' d = rootSL2 .E7 L e7O8Beta B' *
            rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Fr B') := rfl
        have e2 : ρ' (Matrix.SpecialLinearGroup.map σ₂.toRingHom d) =
            rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Φ₀
              (Matrix.SpecialLinearGroup.map Fr B')) *
              rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Φ₀ B') := by
          show rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map ι₂
            (Matrix.SpecialLinearGroup.map σ₂.toRingHom d)) *
              rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Fr
                (Matrix.SpecialLinearGroup.map ι₂
                  (Matrix.SpecialLinearGroup.map σ₂.toRingHom d))) = _
          rw [hi, hii]
        rw [e1, e2, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
        calc n₀ * (rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Φ₀ B') *
              rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Φ₀
                (Matrix.SpecialLinearGroup.map Fr B'))) * n₀⁻¹
            = (n₀ * rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Φ₀ B') * n₀⁻¹) *
              (n₀ * rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Φ₀
                (Matrix.SpecialLinearGroup.map Fr B')) * n₀⁻¹) := by group
          _ = rootSL2 .E7 L e7O8Gamma (Matrix.SpecialLinearGroup.map Φ₀ B') *
              rootSL2 .E7 L e7O8Beta (Matrix.SpecialLinearGroup.map Φ₀
                (Matrix.SpecialLinearGroup.map Fr B')) := by rw [hn₂, hn₃]
          _ = _ := ((hc23 _ _).symm).eq
      have hK₂ : Nat.card k₂ = 2 ^ (p * (2 * f₀)) := by
        rw [hk₂card]
        congr 1
        ring
      exact layerDatum_of_sl (m := 0) hp (by omega) (by omega) (by omega) _ _ hK₂ hσ₂ne ρ' hρ'inj
        hrange₂ hF
    · exact layerDatum_of_sl (m := 0) hp (by omega) (by omega) hf₀ _ _ hK hσ1
        (a1Hom .E7 K L e7O8Alpha) (a1Hom_injective _) hrange₁
        (fun d => a1_F0_compat hn₀c hΦ₀K d)

theorem threeRootSet_isRoot_e7 :
    ∀ r ∈ threeRootSet e7O8Alpha e7O8Beta e7O8Gamma, IsRoot .E7 r := by
  obtain ⟨hαr, hβr, hγr⟩ := e7A1_isRoot
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hαr, IsRoot.neg hαr, hβr, IsRoot.neg hβr, hγr, IsRoot.neg hγr]

theorem frobSector_E7_8 : FrobSector .E7 8 :=
  frobSector_of_family (τ := .E7) (d := 2) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (e := 8) (p₀ := 7)
    (S := threeRootSet e7O8Alpha e7O8Beta e7O8Gamma) threeRootSet_isRoot_e7
    (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threeRootSet])
    (fun L _ n => E78Rep L n)
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1 := by simpa [exhaustionPhi] using hΦ
      exact (CTE6.e6Eight_data hp (by omega) hpf').1)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf => e7Eight_frame hf₀ hK₀ hp hp0 hpf)
    (by
      intro K₀ K L _ _ _ _ _ _ _ _ _ _ _ _ _ f₀ p hp hp0 hf₀ hK hK₀ hΦ hΦ₀ σ hσord hσ n₀ hn₀C
        hn₀fix hR
      exact e7Eight_family hp hp0 hf₀ hK σ hσord hσ hR)

theorem layerSector_E7_8 : KLC.LayerSector .E7 8 := layerSector_of_frob frobSector_E7_8

end Family


end CFSG.RankThree.PartOne.KLCE

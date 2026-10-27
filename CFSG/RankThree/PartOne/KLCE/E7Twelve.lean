module

public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.KLCE.CharTwoRep
public import CFSG.RankThree.PartOne.KLCE.PowConj
public import CFSG.RankThree.PartOne.KLCE.FrobAut
public import CFSG.RankThree.PartOne.KLCE.A1Type
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerRationalDescent
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.PartOne.KE.E7TwelveBlock
public import CFSG.RankThree.PartOne.KE.E7TwelveFamily
public import CFSG.RankThree.PartOne.KE.E7TwelveNative

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)

open CFSG.RankThree.Classical (conjSL conjSL_one)

open scoped Matrix Polynomial MatrixGroups Pointwise

section Frame


@[expose] def E712Rep (L : Type) [Field L] (n : ModGL .E7 L) : Prop :=
  ∃ hnm : n ∈ monomialSubgroup .E7 L,
    (∀ u, weylQuotientHom .E7 L ⟨n, hnm⟩ • u = e7T12W *ᵥ u) ∧
    (∀ A, n * rootSL2 .E7 L e7T12Alpha A * n⁻¹ = rootSL2 .E7 L e7T12Beta A) ∧
    (∀ A, n * rootSL2 .E7 L e7T12Beta A * n⁻¹ = rootSL2 .E7 L e7T12Gamma A) ∧
    (∀ A, n * rootSL2 .E7 L e7T12Gamma A * n⁻¹ = rootSL2 .E7 L e7T12Alpha A)

theorem e712Rep_wordRep (L : Type) [Field L] [CharP L 2] :
    E712Rep L (wordRep .E7 L [0, 1, 2, 3, 4, 5]) := by
  obtain ⟨hαr, hβr, hγr⟩ := e7T12_isRoot
  obtain ⟨h1, h2, h3⟩ := e7T12Word_smul
  have h1' : (coxeterSystem .E7).wordProd [0, 1, 2, 3, 4, 5] • e7T12Alpha = e7T12Beta := h1
  have h2' : (coxeterSystem .E7).wordProd [0, 1, 2, 3, 4, 5] • e7T12Beta = e7T12Gamma := h2
  have h3' : (coxeterSystem .E7).wordProd [0, 1, 2, 3, 4, 5] • e7T12Gamma = e7T12Alpha := h3
  refine ⟨wordRep_mem_monomial _, fun u => ?_, fun A => ?_, fun A => ?_, fun A => ?_⟩
  · rw [wordRep_weylImage]
    exact wordProd_smul_eq_wordMat_mulVec .E7 [0, 1, 2, 3, 4, 5] u
  · rw [wordRep_conj_rootSL2 hαr, h1']
  · rw [wordRep_conj_rootSL2 hβr, h2']
  · rw [wordRep_conj_rootSL2 hγr, h3']

theorem e7Twelve_frame {K₀ L : Type} [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
    [IsAlgClosure K₀ L] [CharP L 2] {f₀ p : ℕ} (hf₀ : 1 ≤ f₀) (hK₀ : Nat.card K₀ = 2 ^ f₀)
    (hp : p.Prime) (hp7 : 7 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K₀ : ℤ)) :
    ¬ p ∣ Nat.card (WeylGroup .E7) ∧
      ∃ n₀ : ModGL .E7 L, n₀ ∈ adjointGroup .E7 L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧ E712Rep L n₀ ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧
          Nat.card (subtorusSigma n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
            (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma)) = N₀ ∧
          p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ b : Fin Tag.E7.rank → Lˣ,
            rootDiagUnit .E7 b ∈ subtorusSigma n₀
              (Units.map (entrywiseHom (iterateFrobenius L 2 f₀)))
              (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma) →
            orderOf (rootDiagUnit .E7 b) = p →
            rootCharKernel b ⊆ threeRootSet e7T12Alpha e7T12Beta e7T12Gamma) := by
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
  have hpf' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 - (Nat.card K₀ : ℤ) ^ 2 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨-, hpq, hord12⟩ := CTE6.e6Twelve_data hp (by omega) hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E7) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inl rfl))
  obtain ⟨hαr, hβr, hγr⟩ := e7T12_isRoot
  have hrep := e712Rep_wordRep L
  have hrep2 := hrep
  obtain ⟨hnm, hnW, -, -, -⟩ := hrep2
  set n : ModGL .E7 L := wordRep .E7 L [0, 1, 2, 3, 4, 5] with hndef
  have hnC : n ∈ adjointGroup .E7 L := monomialSubgroup_le_adjointGroup' hnm
  have hnfix : Units.map (entrywiseHom Fr) n = n := by
    have := wordRep_fixed (τ := .E7) (iterateFrobeniusEquiv L 2 f₀) [0, 1, 2, 3, 4, 5]
    rw [CFSG.LieType.AlgebraicGroups.iterateFrobeniusEquiv_toRingHom] at this
    exact this
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e7T12W Fr).map (rootDiagUnitHom .E7 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusSigma_eq_map_fixedBlockTuples_three e7T12_commute_alpha_beta
    e7T12_commute_alpha_gamma e7T12_commute_beta_gamma hT hαr hβr hγr
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  obtain ⟨hcycB, hcardB⟩ := e7Twelve_block_cyclic Fr hFr Nat.prime_two hℓq
  have h24 : Nat.card K₀ ^ 2 ≤ Nat.card K₀ ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hN : Nat.card K₀ ^ 4 - Nat.card K₀ ^ 2 + 1 ≠ 0 := by omega
  have hZcard : Nat.card (subtorusSigma n (Units.map (entrywiseHom Fr))
      (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma)) =
        Nat.card K₀ ^ 4 - Nat.card K₀ ^ 2 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    exact hcardB
  have hord : p ^ (Nat.card (adjointGroup .E7 K₀)).factorization p =
      p ^ (Nat.card K₀ ^ 4 - Nat.card K₀ ^ 2 + 1).factorization p := by
    have hrest : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), d ≠ 12 → ¬ 12 ∣ d := by decide
    obtain ⟨hg, -, hR⟩ := CTE6.e6Twelve_factors hp hord12
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : 1 ≤ Nat.card K₀ ^ 12 := Nat.one_le_pow _ _ (by omega)
    refine ordProj_card_adjointGroup_E7 hp (by omega) hpq hord12 (d₀ := 12) (by decide) hrest hN
      (R := ((Nat.card K₀ : ℤ) - 1) * ((Nat.card K₀ : ℤ) ^ 3 + 1) * ((Nat.card K₀ : ℤ) ^ 2 + 1) *
        ((Nat.card K₀ : ℤ) ^ 2 + (Nat.card K₀ : ℤ) + 1)) ?_ ?_
    · push_cast [Nat.cast_sub h1, Nat.cast_sub h24]
      ring
    · intro hdvd
      rcases hpz.dvd_or_dvd hdvd with h | h
      · exact hR h
      · exact hg h
  refine ⟨hordW, n, hnC, hnfix, hrep, Nat.card K₀ ^ 4 - Nat.card K₀ ^ 2 + 1, hN, hZcard, hord, ?_⟩
  intro b hb hbp
  rw [hZeq] at hb
  obtain ⟨b', hb', hbb'⟩ := hb
  have : b' = b := hinj0 hbb'
  subst this
  rw [e7Twelve_rootCharKernel Fr hFr hp (by omega) hord12 hb'.1
    (KE.pow_eq_one_of_orderOf_rootDiagUnit hbp) (KE.ne_one_of_orderOf_rootDiagUnit hp hbp)]
  exact Set.Subset.rfl

end Frame

section Family


theorem e7T12Mul_injective_of_charTwo (L : Type) [Field L] [CharP L 2] :
    Function.Injective (e7T12Mul L) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, B, C⟩ h
  obtain ⟨l, hl, hA, hB, hC⟩ := (e7T12Mul_eq_one_iff A B C).1 h
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hl1 : l = 1 := by
    have h3 : (l - 1) ^ 2 = 0 := by linear_combination hl + (1 - l) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)
  subst hl1
  have h1 : ∀ M : SL2 L, (M : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) (1 : L) → M = 1 :=
    fun M hM => Subtype.ext (by rw [hM, map_one]; rfl)
  exact Prod.ext (h1 A hA) (Prod.ext (h1 B hB) (h1 C hC))

theorem e7Twelve_fixed_triple {L : Type} [Field L] [CharP L 2] (Fr : L →+* L) {N : ModGL .E7 L}
    (hα : ∀ A : SL2 L, N * rootSL2 .E7 L e7T12Alpha A * N⁻¹ = rootSL2 .E7 L e7T12Beta A)
    (hβ : ∀ A : SL2 L, N * rootSL2 .E7 L e7T12Beta A * N⁻¹ = rootSL2 .E7 L e7T12Gamma A)
    (hγ : ∀ A : SL2 L, N * rootSL2 .E7 L e7T12Gamma A * N⁻¹ = rootSL2 .E7 L e7T12Alpha A)
    {q : ModGL .E7 L} (hq : q ∈ rootSpan .E7 L (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma))
    (hqR : N * Units.map (entrywiseHom Fr) q * N⁻¹ = q) :
    ∃ A B C : SL2 L, q = e7T12Mul L (A, B, C) ∧ Matrix.SpecialLinearGroup.map Fr C = A ∧
      Matrix.SpecialLinearGroup.map Fr A = B ∧ Matrix.SpecialLinearGroup.map Fr B = C := by
  obtain ⟨hαr, hβr, hγr⟩ := e7T12_isRoot
  rw [rootSpan_threeRootSet hαr hβr hγr] at hq
  obtain ⟨A, B, C, rfl⟩ := mem_sup_three e7T12_commute_alpha_beta e7T12_commute_alpha_gamma
    e7T12_commute_beta_gamma hq
  rw [← e7T12Mul_apply, e7T12_conj_entrywise hα hβ hγ Fr A B C] at hqR
  have h3 := e7T12Mul_injective_of_charTwo L hqR
  simp only [Prod.mk.injEq] at h3
  obtain ⟨h1, h2, h3⟩ := h3
  exact ⟨A, B, C, (e7T12Mul_apply A B C).symm, h1, h2, h3⟩

theorem e7Twelve_family {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {f₀ p : ℕ} (hp : p.Prime) (hp7 : 7 < p) (hp3 : p % 3 = 1)
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀)) {n₀ : ModGL .E7 L} (hRn₀ : E712Rep L n₀) :
    ∃ (ι' : Type) (P : ι' → Subgroup (ModGL .E7 L)), Nonempty ι' ∧
      IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p))
        (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma) P ∧
      rootSpan .E7 L (threeRootSet e7T12Alpha e7T12Beta e7T12Gamma) ⊓
        twistedFixedPoints (n₀ ^ p)
          (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) ≤ ⨆ i, P i ∧
      (∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u) ∧
      ∀ i, LayerDatum p
        (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) (P i) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨kk, hkk⟩ : ∃ k, p = 3 * k + 1 := ⟨p / 3, by omega⟩
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hΦFr : ∀ c, Fr (Φ₀ c) = Φ₀ (Fr c) := fun c => by
    rw [hFrdef, hΦ₀def, iterateFrobenius_def, iterateFrobenius_def, iterateFrobenius_def,
      iterateFrobenius_def, ← pow_mul, ← pow_mul, mul_comm]
  obtain ⟨hαr, hβr, hγr⟩ := e7T12_isRoot
  obtain ⟨-, -, hn₁, hn₂, hn₃⟩ := hRn₀
  have hNα : ∀ A : SL2 L, n₀ ^ p * rootSL2 .E7 L e7T12Alpha A * (n₀ ^ p)⁻¹ =
      rootSL2 .E7 L e7T12Beta A := fun A => by
    rw [hkk]
    exact pow_three_succ_conj (hn₁ A) (hn₂ A) (hn₃ A) kk
  have hNβ : ∀ A : SL2 L, n₀ ^ p * rootSL2 .E7 L e7T12Beta A * (n₀ ^ p)⁻¹ =
      rootSL2 .E7 L e7T12Gamma A := fun A => by
    rw [hkk]
    exact pow_three_succ_conj (hn₂ A) (hn₃ A) (hn₁ A) kk
  have hNγ : ∀ A : SL2 L, n₀ ^ p * rootSL2 .E7 L e7T12Gamma A * (n₀ ^ p)⁻¹ =
      rootSL2 .E7 L e7T12Alpha A := fun A => by
    rw [hkk]
    exact pow_three_succ_conj (hn₃ A) (hn₁ A) (hn₂ A) kk
  have hpf₀ : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  obtain ⟨k₃, _, _, _, hk₃card⟩ := exists_finite_field_into 2 (3 * (p * f₀)) (by omega) L
  have hk₃ : Nat.card k₃ = Nat.card K ^ 3 := by
    rw [hk₃card, hK, ← pow_mul, mul_comm]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hp.two_le])
  have hk4 : 4 ≤ Nat.card k₃ := by
    rw [hk₃]
    nlinarith [Nat.pow_le_pow_left hK4 3]
  have : CharP k₃ 2 := ⟨fun x => by
    rw [← (algebraMap k₃ L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L 2 x⟩
  let Fr3 : L →+* L := Fr.comp (Fr.comp Fr)
  have hFr3 : ∀ c, Fr3 c = c ^ Nat.card k₃ := fun c => by
    show Fr (Fr (Fr c)) = c ^ Nat.card k₃
    rw [hk₃, hFr, hFr, hFr, ← pow_mul, ← pow_mul]
    ring_nf
  have hfix3 : ∀ c, Fr3 c = c ↔ c ∈ Set.range (algebraMap k₃ L) := fun c =>
    frobenius_fixed_iff Fr3 hFr3 c
  have hS₃ : ∀ B : SL2 L, B ∈ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)).range.map
      (conjSL (1 : GL (Fin 2) L)) ↔
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr
          (Matrix.SpecialLinearGroup.map Fr B)) = B := by
    intro B
    have hcomp : Matrix.SpecialLinearGroup.map Fr3 B =
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr
          (Matrix.SpecialLinearGroup.map Fr B)) := by
      ext i j
      simp [Fr3]
    rw [← hcomp, sl2_map_fixed_iff Fr3 hfix3 B]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rwa [conjSL_one]
    · intro hB
      exact ⟨B, hB, conjSL_one B⟩
  obtain ⟨hfin₃, hq₃⟩ := sl2_conj_range_quasisimple (L := L) (K := k₃) hk4 (1 : GL (Fin 2) L)
  have hz₃ := sl2_conj_range_centralizer (K := k₃) (L := L) (1 : GL (Fin 2) L)
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, hPmem⟩ := three_A1_cyclic_family
    e7T12_commute_alpha_beta e7T12_commute_alpha_gamma e7T12_commute_beta_gamma hαr hβr hγr
    (e7T12Mul L) e7T12Mul_apply (fun A B C h => (e7T12Mul_eq_one_iff A B C).1 h) Fr (n₀ ^ p)
    (fun A B C => e7T12_conj_entrywise hNα hNβ hNγ Fr A B C) _ hS₃ hq₃ hz₃
  refine ⟨Unit, fun _ => P, ⟨()⟩, ⟨fun _ => hPfin, fun _ => hPq, fun _ => hPQ, fun _ => hPR,
    fun _ => hPadj, fun _ => hPnorm, fun y hy hyR hc => hPcent y hy hyR (hc ())⟩, ?_,
    fun i j hij => absurd (Subsingleton.elim i j) hij, ?_⟩
  ·
    intro q hq
    obtain ⟨hqS, hqR⟩ := hq
    obtain ⟨A, B, C, rfl, hCA, hAB, hBC⟩ := e7Twelve_fixed_triple Fr hNα hNβ hNγ hqS hqR
    have hA3 : A ∈ (Matrix.SpecialLinearGroup.map (algebraMap k₃ L)).range.map
        (conjSL (1 : GL (Fin 2) L)) := (hS₃ A).2 (by rw [hAB, hBC, hCA])
    refine le_iSup (fun _ : Unit => P) () ((hPmem _).2 ⟨A, hA3, ?_⟩)
    rw [hAB, hBC]
  ·
    intro _
    set ι₃ : k₃ →+* L := algebraMap k₃ L with hι₃
    let σ₃ : k₃ ≃+* k₃ := frobAut k₃ ((2 * p + 1) * f₀)
    have hσ₃x : ∀ x : k₃, σ₃ x = x ^ 2 ^ ((2 * p + 1) * f₀) := fun x => rfl
    have hΦ3 : ∀ c : L, Φ₀ (Fr (Fr c)) = c ^ 2 ^ ((2 * p + 1) * f₀) := fun c => by
      rw [hΦ₀def, hFrdef, iterateFrobenius_def, iterateFrobenius_def, iterateFrobenius_def,
        ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 2
      ring
    have hσ₃ : ∀ x : k₃, ι₃ (σ₃ x) = Φ₀ (Fr (Fr (ι₃ x))) := fun x => by
      rw [hσ₃x, map_pow, hΦ3]
    have hFr3fix : ∀ x : k₃, Fr (Fr (Fr (ι₃ x))) = ι₃ x := fun x => (hfix3 _).2 ⟨x, rfl⟩
    let ν : SL2 L →* ModGL .E7 L :=
      (e7T12Mul L).comp ((MonoidHom.id (SL2 L)).prod ((Matrix.SpecialLinearGroup.map Fr).prod
        ((Matrix.SpecialLinearGroup.map Fr).comp (Matrix.SpecialLinearGroup.map Fr))))
    have hν : ∀ X, ν X = e7T12Mul L (X, Matrix.SpecialLinearGroup.map Fr X,
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr X)) := fun X => rfl
    have hνinj : Function.Injective ν := fun X Y h => by
      rw [hν, hν] at h
      have := e7T12Mul_injective_of_charTwo L h
      simp only [Prod.mk.injEq] at this
      exact this.1
    let ρ' : Matrix.SpecialLinearGroup (Fin (0 + 2)) k₃ →* ModGL .E7 L :=
      ν.comp (Matrix.SpecialLinearGroup.map ι₃)
    have hρ'inj : Function.Injective ρ' := hνinj.comp (map_specialLinear_injective _)
    have hrange : ρ'.range = P := by
      ext g
      rw [hPmem]
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨Matrix.SpecialLinearGroup.map ι₃ d, ⟨_, ⟨d, rfl⟩, conjSL_one _⟩, rfl⟩
      · rintro ⟨X, ⟨C, ⟨d, rfl⟩, rfl⟩, rfl⟩
        exact ⟨d, by simp only [ρ', MonoidHom.comp_apply, conjSL_one]; rfl⟩
    have hF₀ : ∀ d : Matrix.SpecialLinearGroup (Fin (0 + 2)) k₃,
        n₀ * Units.map (entrywiseHom Φ₀) (ρ' d) * n₀⁻¹ =
          ρ' (Matrix.SpecialLinearGroup.map σ₃.toRingHom d) := by
      intro d
      set X' : SL2 L := Matrix.SpecialLinearGroup.map ι₃ d with hX'
      have e0 : ρ' d = e7T12Mul L (X', Matrix.SpecialLinearGroup.map Fr X',
          Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr X')) := rfl
      have hE1 : Matrix.SpecialLinearGroup.map ι₃ (Matrix.SpecialLinearGroup.map σ₃.toRingHom d) =
          Matrix.SpecialLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.map Fr
            (Matrix.SpecialLinearGroup.map Fr X')) := by
        ext a b
        simp [hX', hσ₃]
      have hE2 : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Φ₀
          (Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr X'))) =
            Matrix.SpecialLinearGroup.map Φ₀ X' := by
        ext a b
        simp [hX', hΦFr, hFr3fix]
      have hE3 : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Φ₀ X') =
          Matrix.SpecialLinearGroup.map Φ₀ (Matrix.SpecialLinearGroup.map Fr X') := by
        ext a b
        simp [hΦFr]
      rw [e0, e7T12_conj_entrywise hn₁ hn₂ hn₃ Φ₀]
      show _ = e7T12Mul L (Matrix.SpecialLinearGroup.map ι₃
        (Matrix.SpecialLinearGroup.map σ₃.toRingHom d), Matrix.SpecialLinearGroup.map Fr
          (Matrix.SpecialLinearGroup.map ι₃ (Matrix.SpecialLinearGroup.map σ₃.toRingHom d)),
            Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr
              (Matrix.SpecialLinearGroup.map ι₃ (Matrix.SpecialLinearGroup.map σ₃.toRingHom d))))
      rw [hE1, hE2, hE3]
    have hσ₃ne : σ₃ ≠ 1 :=
      frobAut_ne_one hk₃card (by positivity) (by nlinarith [hp.two_le])
    have hK₃ : Nat.card k₃ = 2 ^ (p * (3 * f₀)) := by
      rw [hk₃card]
      congr 1
      ring
    exact layerDatum_of_sl (m := 0) hp (by omega) (by omega) (by omega) _ _ hK₃ hσ₃ne ρ' hρ'inj
      hrange hF₀

end Family

section Sector


theorem mod_three_eq_one_of_dvd_phi_twelve {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 2 + 1) : p % 3 = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hpq, hord⟩ := CTE6.e6Twelve_data hp hp3 h
  have hq0 : (q : ZMod p) ≠ 0 := fun h0 => hpq ((ZMod.natCast_eq_zero_iff q p).1 h0)
  have hdvd := ZMod.orderOf_dvd_card_sub_one hq0
  rw [hord] at hdvd
  obtain ⟨t, ht⟩ := hdvd
  omega

theorem threeRootSet_isRoot_e7T12 :
    ∀ r ∈ threeRootSet e7T12Alpha e7T12Beta e7T12Gamma, IsRoot .E7 r := by
  obtain ⟨hαr, hβr, hγr⟩ := e7T12_isRoot
  intro r hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [hαr, IsRoot.neg hαr, hβr, IsRoot.neg hβr, hγr, IsRoot.neg hγr]

theorem frobSector_E7_12 : FrobSector .E7 12 :=
  frobSector_of_family (τ := .E7) (d := 2) (Or.inr (Or.inl ⟨rfl, rfl⟩)) (e := 12) (p₀ := 7)
    (S := threeRootSet e7T12Alpha e7T12Beta e7T12Gamma) threeRootSet_isRoot_e7T12
    (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [threeRootSet])
    (fun L _ n => E712Rep L n)
    (fun K _ _ p f₀ hp hp5 hf₀ hK hΦ hpr => by
      have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 - (Nat.card K : ℤ) ^ 2 + 1 := by
        simpa [exhaustionPhi] using hΦ
      exact (CTE6.e6Twelve_data hp (by omega) hpf').1)
    (fun K₀ L _ _ _ _ _ _ f₀ p hf₀ hK₀ hp hp0 hpf => e7Twelve_frame hf₀ hK₀ hp hp0 hpf)
    (by
      intro K₀ K L _ _ _ _ _ _ _ _ _ _ _ _ _ f₀ p hp hp0 hf₀ hK hK₀ hΦ hΦ₀ σ hσord hσ n₀ hn₀C
        hn₀fix hR
      have hpf' : (p : ℤ) ∣ (Nat.card K₀ : ℤ) ^ 4 - (Nat.card K₀ : ℤ) ^ 2 + 1 := by
        simpa [exhaustionPhi] using hΦ₀
      exact e7Twelve_family hp hp0 (mod_three_eq_one_of_dvd_phi_twelve hp (by omega) hpf') hf₀ hK
        hR)

theorem layerSector_E7_12 : KLC.LayerSector .E7 12 := layerSector_of_frob frobSector_E7_12

end Sector

end CFSG.RankThree.PartOne.KLCE

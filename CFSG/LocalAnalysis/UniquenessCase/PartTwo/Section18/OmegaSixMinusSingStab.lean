module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137Opp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusFixTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesLevi
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONorm
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

section OddIsometries

open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite
  coe_quadMinus)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small)

theorem odd_isometry_mem_omega_four {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {g : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) F}
    (hg : ∀ v, StatedQuadMinus 2 F b c
      (g.val *ᵥ v)
        = StatedQuadMinus 2 F b c v)
    (hodd : Odd (orderOf g)) : g ∈ StatedOmega (StatedQuadMinus 2 F b c) := by
  obtain ⟨-, -, -, -, hoddO, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction (quadMinus 2 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 2 F hirr)
      (Or.inl (finrank_minusSpace_small (n := 2) (by norm_num)))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U
        (by rw [hU, finrank_minusSpace_small (n := 2) (by norm_num)]))
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (coe_quadMinus 2 F b c),
    Subgroup.mem_comap]
  refine hoddO _ ?_ ?_
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [MulEquiv.coe_toMonoidHom, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply,
      coe_quadMinus 2 F b c]
    exact hg x
  · rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]

end OddIsometries

section SingularStabilizer

open Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.RankThreeUC
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus)
open CFSG.SeitzReduction.F4Pilot (coordEmbedGL coordEmbedMat IsCoordSplit coe_coordEmbedGL
  coordEmbedMat_apply_image coordEmbedMat_mulVec_comp coordEmbedMat_mulVec_of_not_mem
  sum_eq_sum_comp_of_vanish isometry_of_mem_statedOmega)
open CFSG.SeitzReduction.SymplecticPilot (kOmMLongEmb kOmMLongEmb_injective
  kOmM_isCoordSplit_long kOmM_exists_of_not_mem_range_longEmb)

variable {F : Type} [Field F] {b c : F}

@[expose] def sixMinusLongEmb :
    Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 :=
  kOmMLongEmb 2 1

theorem sixMinusLongEmb_injective : Function.Injective sixMinusLongEmb :=
  kOmMLongEmb_injective (r := 2) 1

theorem sixMinusLongEmb_ne_inl (a : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) :
    sixMinusLongEmb a ≠ Sum.inl 0 := by
  rcases a with a | a | a <;> simp [sixMinusLongEmb, kOmMLongEmb]

theorem sixMinusLongEmb_ne_inr_inl (a : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) :
    sixMinusLongEmb a ≠ Sum.inr (Sum.inl 0) := by
  rcases a with a | a | a <;> simp [sixMinusLongEmb, kOmMLongEmb]

theorem eq_of_not_mem_range_sixMinusLongEmb {a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2}
    (ha : a ∉ Set.range sixMinusLongEmb) : a = Sum.inl 0 ∨ a = Sum.inr (Sum.inl 0) := by
  obtain ⟨l', hl', h⟩ := kOmM_exists_of_not_mem_range_longEmb (r := 2) (l := 1) ha
  have h0 : ∀ l' : Fin 2, l' ≠ 1 → l' = 0 := by decide
  rw [h0 l' hl'] at h
  exact h

theorem statedQuadMinus_three_split (v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    StatedQuadMinus 3 F b c v =
      v (Sum.inl 0) * v (Sum.inr (Sum.inl 0)) + StatedQuadMinus 2 F b c (v ∘ sixMinusLongEmb) := by
  simp only [StatedQuadMinus, Function.comp_apply, sixMinusLongEmb, kOmMLongEmb, Sum.map_inl,
    Sum.map_inr, id]
  rw [Fin.sum_univ_two, Fin.sum_univ_one]
  ring

theorem statedQuadMinus_three_add_single (y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    StatedQuadMinus 3 F b c (y + Pi.single (Sum.inl 0) 1) =
      StatedQuadMinus 3 F b c y + y (Sum.inr (Sum.inl 0)) := by
  have hl : (y + Pi.single (Sum.inl 0) 1) ∘ sixMinusLongEmb = y ∘ sixMinusLongEmb := by
    funext a
    simp [Pi.single_apply, sixMinusLongEmb_ne_inl a]
  have h1 : (y + Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (Sum.inl 0) =
      y (Sum.inl 0) + 1 := by simp
  have h2 : (y + Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)
      (Sum.inr (Sum.inl 0)) = y (Sum.inr (Sum.inl 0)) := by simp
  rw [statedQuadMinus_three_split, statedQuadMinus_three_split y, hl, h1, h2]
  ring

section Mat

variable {M : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}

theorem apply_inl_zero_of_mulVec_single
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) :
    M a (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) a := by
  have := congrFun he a
  rwa [Matrix.mulVec_single_one] at this

theorem mulVec_inr_inl_zero_of_isometry
    (hQ : ∀ v, StatedQuadMinus 3 F b c (M *ᵥ v) = StatedQuadMinus 3 F b c v)
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :
    (M *ᵥ x) (Sum.inr (Sum.inl 0)) = x (Sum.inr (Sum.inl 0)) := by
  have h := hQ (x + Pi.single (Sum.inl 0) 1)
  rw [Matrix.mulVec_add, he, statedQuadMinus_three_add_single,
    statedQuadMinus_three_add_single, hQ x] at h
  exact add_left_cancel h

theorem apply_inr_inl_zero_of_isometry
    (hQ : ∀ v, StatedQuadMinus 3 F b c (M *ᵥ v) = StatedQuadMinus 3 F b c v)
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (a : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) :
    M (Sum.inr (Sum.inl 0)) a =
      (Pi.single a 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (Sum.inr (Sum.inl 0)) := by
  have := mulVec_inr_inl_zero_of_isometry hQ he (Pi.single a 1)
  rwa [Matrix.mulVec_single_one] at this

theorem apply_sixMinusLongEmb_inl_zero
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (a : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) : M (sixMinusLongEmb a) (Sum.inl 0) = 0 := by
  rw [apply_inl_zero_of_mulVec_single he, Pi.single_apply, if_neg (sixMinusLongEmb_ne_inl a)]

theorem apply_inr_inl_zero_sixMinusLongEmb
    (hQ : ∀ v, StatedQuadMinus 3 F b c (M *ᵥ v) = StatedQuadMinus 3 F b c v)
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (a : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) : M (Sum.inr (Sum.inl 0)) (sixMinusLongEmb a) = 0 := by
  rw [apply_inr_inl_zero_of_isometry hQ he, Pi.single_apply,
    if_neg (sixMinusLongEmb_ne_inr_inl a).symm]

theorem submatrix_sixMinusLongEmb_mul
    {N : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hM : ∀ a, M (sixMinusLongEmb a) (Sum.inl 0) = 0)
    (hN : ∀ a, N (Sum.inr (Sum.inl 0)) (sixMinusLongEmb a) = 0) :
    (M * N).submatrix sixMinusLongEmb sixMinusLongEmb =
      M.submatrix sixMinusLongEmb sixMinusLongEmb *
        N.submatrix sixMinusLongEmb sixMinusLongEmb := by
  ext a a'
  have hv : ∀ c', c' ∉ Set.range sixMinusLongEmb →
      M (sixMinusLongEmb a) c' * N c' (sixMinusLongEmb a') = 0 := fun c' hc => by
    rcases eq_of_not_mem_range_sixMinusLongEmb hc with rfl | rfl
    · rw [hM, zero_mul]
    · rw [hN, mul_zero]
  rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
    sum_eq_sum_comp_of_vanish sixMinusLongEmb_injective _ hv]
  rfl

theorem isometry_submatrix_sixMinusLongEmb
    (hQ : ∀ v, StatedQuadMinus 3 F b c (M *ᵥ v) = StatedQuadMinus 3 F b c v)
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) :
    StatedQuadMinus 2 F b c (M.submatrix sixMinusLongEmb sixMinusLongEmb *ᵥ x) =
      StatedQuadMinus 2 F b c x := by
  obtain ⟨X, hXl, hXo⟩ : ∃ X : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F,
      (∀ z, X (sixMinusLongEmb z) = x z) ∧ ∀ c', c' ∉ Set.range sixMinusLongEmb → X c' = 0 :=
    ⟨Function.extend sixMinusLongEmb x (0 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      fun z => sixMinusLongEmb_injective.extend_apply x _ z,
      fun c' hc => Function.extend_apply' x _ c' hc⟩
  have hf0 : X (Sum.inr (Sum.inl 0)) = 0 :=
    hXo _ fun ⟨z, hz⟩ => sixMinusLongEmb_ne_inr_inl z hz
  have hXl' : X ∘ sixMinusLongEmb = x := funext hXl
  have hMl : (M *ᵥ X) ∘ sixMinusLongEmb = M.submatrix sixMinusLongEmb sixMinusLongEmb *ᵥ x := by
    funext a
    have hv : ∀ c', c' ∉ Set.range sixMinusLongEmb → M (sixMinusLongEmb a) c' * X c' = 0 :=
      fun c' hc => by rw [hXo c' hc, mul_zero]
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct]
    rw [sum_eq_sum_comp_of_vanish sixMinusLongEmb_injective _ hv]
    exact Finset.sum_congr rfl fun z _ => by rw [hXl]; rfl
  have hf : (M *ᵥ X) (Sum.inr (Sum.inl 0)) = 0 := by
    rw [mulVec_inr_inl_zero_of_isometry hQ he X, hf0]
  have h := hQ X
  rw [statedQuadMinus_three_split, statedQuadMinus_three_split X, hMl, hf, hXl', hf0, mul_zero,
    mul_zero, zero_add, zero_add] at h
  exact h

theorem pow_four_eq_one_of_submatrix_eq_one [CharP F 2]
    (hQ : ∀ v, StatedQuadMinus 3 F b c (M *ᵥ v) = StatedQuadMinus 3 F b c v)
    (he : M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (h1 : M.submatrix sixMinusLongEmb sixMinusLongEmb = 1) : M ^ 4 = 1 := by
  have hcol := apply_inl_zero_of_mulVec_single he
  have hrow := mulVec_inr_inl_zero_of_isometry hQ he
  have hA : ∀ y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F, y (Sum.inr (Sum.inl 0)) = 0 →
      ∀ a, (M *ᵥ y) (sixMinusLongEmb a) = y (sixMinusLongEmb a) := by
    intro y hy a
    have hv : ∀ c', c' ∉ Set.range sixMinusLongEmb → M (sixMinusLongEmb a) c' * y c' = 0 :=
      fun c' hc => by
        rcases eq_of_not_mem_range_sixMinusLongEmb hc with rfl | rfl
        · rw [hcol, Pi.single_apply, if_neg (sixMinusLongEmb_ne_inl a), zero_mul]
        · rw [hy, mul_zero]
    have h1' : ∀ z, M (sixMinusLongEmb a) (sixMinusLongEmb z) =
        (1 : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) F) a z :=
      fun z => congrFun (congrFun h1 a) z
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_eq_sum_comp_of_vanish sixMinusLongEmb_injective _ hv]
    simp [h1', Matrix.one_apply]
  have hB : ∀ y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F, y (Sum.inr (Sum.inl 0)) = 0 →
      (∀ a, y (sixMinusLongEmb a) = 0) → M *ᵥ y = y := by
    intro y hy hyl
    have hy0 : ∀ c', c' ≠ Sum.inl 0 → y c' = 0 := fun c' hc => by
      by_cases hr : c' ∈ Set.range sixMinusLongEmb
      · obtain ⟨z, rfl⟩ := hr
        exact hyl z
      · rcases eq_of_not_mem_range_sixMinusLongEmb hr with h | h
        · exact absurd h hc
        · rw [h]
          exact hy
    funext a
    have hsum : ∑ c', M a c' * y c' = M a (Sum.inl 0) * y (Sum.inl 0) :=
      Finset.sum_eq_single _ (fun c' _ hc => by rw [hy0 c' hc, mul_zero])
        (fun h => absurd (Finset.mem_univ _) h)
    simp only [Matrix.mulVec, dotProduct]
    rw [hsum, hcol]
    by_cases ha : a = Sum.inl 0
    · subst ha
      simp
    · simp [Pi.single_apply, ha, hy0 a ha]
  have hN : ∀ v, (M - 1) *ᵥ v = M *ᵥ v - v := fun v => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have h3 : ∀ v, (M - 1) ^ 3 *ᵥ v = 0 := by
    intro v
    rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hz₁ : ((M - 1) *ᵥ v) (Sum.inr (Sum.inl 0)) = 0 := by
      rw [hN, Pi.sub_apply, hrow, sub_self]
    have hz₂f : ((M - 1) *ᵥ ((M - 1) *ᵥ v)) (Sum.inr (Sum.inl 0)) = 0 := by
      rw [hN, Pi.sub_apply, hrow, sub_self]
    have hz₂l : ∀ a, ((M - 1) *ᵥ ((M - 1) *ᵥ v)) (sixMinusLongEmb a) = 0 := fun a => by
      rw [hN, Pi.sub_apply, hA _ hz₁, sub_self]
    rw [hN, hB _ hz₂f hz₂l, sub_self]
  have h3' : (M - 1) ^ 3 = 0 := by
    ext i j
    have := congrFun (h3 (Pi.single j 1)) i
    rwa [Matrix.mulVec_single_one] at this
  have h4 : (M - 1) ^ 2 ^ 2 = M ^ 2 ^ 2 - 1 ^ 2 ^ 2 :=
    sub_pow_char_pow_of_commute (p := 2) (n := 2) (Commute.one_right M)
  rw [show (2 : ℕ) ^ 2 = 3 + 1 by norm_num, pow_succ, h3', zero_mul, one_pow] at h4
  exact sub_eq_zero.mp h4.symm

end Mat

variable (b c) in
@[expose] noncomputable def sixMinusResMat :
    ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) →*
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) F where
  toFun g := ((((g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)).submatrix
        sixMinusLongEmb sixMinusLongEmb
  map_one' := by
    change ((1 : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).submatrix
        sixMinusLongEmb sixMinusLongEmb = 1
    rw [Units.val_one]
    exact Matrix.submatrix_one _ sixMinusLongEmb_injective
  map_mul' g h := by
    change ((((g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *
      (((h : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)).submatrix
        sixMinusLongEmb sixMinusLongEmb = _
    exact submatrix_sixMinusLongEmb_mul
      (apply_sixMinusLongEmb_inl_zero (M := (((g : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)) g.2)
      (apply_inr_inl_zero_sixMinusLongEmb (M := (((h : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F))
        (isometry_of_mem_statedOmega h.1.2) h.2)

variable (b c) in
@[expose] noncomputable def sixMinusRes :
    ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype
      (Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) →*
      GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) F :=
  (sixMinusResMat b c).toHomUnits

theorem sixMinusRes_spec [Finite F] [CharP F 2] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (∀ g, sixMinusRes b c g = 1 → g ^ 4 = 1) ∧
      StatedOmega (StatedQuadMinus 2 F b c) ≤ (sixMinusRes b c).range ∧
      ∀ g, Odd (orderOf (sixMinusRes b c g)) →
        sixMinusRes b c g ∈ StatedOmega (StatedQuadMinus 2 F b c) := by
  refine ⟨fun g hg => ?_, fun A hA => ?_, fun g hodd => ?_⟩
  · have hM : sixMinusResMat b c g = 1 := by
      have := congrArg Units.val hg
      simpa [sixMinusRes] using this
    have h4 := pow_four_eq_one_of_submatrix_eq_one (isometry_of_mem_statedOmega g.1.2) g.2 hM
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simpa using h4
  · have hsplit : IsCoordSplit (StatedQuadMinus 3 F b c) (StatedQuadMinus 2 F b c)
        sixMinusLongEmb := kOmM_isCoordSplit_long b c 1
    have hGΩ : coordEmbedGL sixMinusLongEmb sixMinusLongEmb_injective A ∈
        StatedOmega (StatedQuadMinus 3 F b c) :=
      hsplit.map_statedOmega_le sixMinusLongEmb_injective ⟨A, hA, rfl⟩
    have h0 : (Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ∘
        sixMinusLongEmb = 0 := funext fun z => by simp [Pi.single_apply, sixMinusLongEmb_ne_inl z]
    have hfix : ((coordEmbedGL sixMinusLongEmb sixMinusLongEmb_injective A :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
      rw [coe_coordEmbedGL]
      funext a
      by_cases ha : a ∈ Set.range sixMinusLongEmb
      · obtain ⟨z, rfl⟩ := ha
        have := congrFun (coordEmbedMat_mulVec_comp sixMinusLongEmb_injective
          (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) F)
          (Pi.single (Sum.inl 0) 1)) z
        rw [h0, Matrix.mulVec_zero] at this
        simp only [Function.comp_apply, Pi.zero_apply] at this
        rw [this]
        simp [Pi.single_apply, sixMinusLongEmb_ne_inl z]
      · exact coordEmbedMat_mulVec_of_not_mem _ _ ha
    refine ⟨⟨⟨_, hGΩ⟩, hfix⟩, Units.ext ?_⟩
    ext x y
    exact coordEmbedMat_apply_image sixMinusLongEmb_injective _ x y
  · exact odd_isometry_mem_omega_four hirr
      (fun v => isometry_submatrix_sixMinusLongEmb (isometry_of_mem_statedOmega g.1.2) g.2 v) hodd

theorem nonempty_vecStab_omegaSixMinus_equiv [Finite F] [CharP F 2]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {w₀ w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F}
    (hw₀ : w₀ ≠ 0) (hw : w ≠ 0) (hQ : StatedQuadMinus 3 F b c w = StatedQuadMinus 3 F b c w₀) :
    Nonempty (↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype w) ≃*
      ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype w₀)) := by
  obtain ⟨h, hh, hhe⟩ := exists_isometry_apply_eq hirr hw₀ hw hQ
  obtain ⟨G₀, rfl⟩ : ∃ G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
      toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G₀ = h :=
    ⟨(toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm h, MulEquiv.apply_symm_apply _ _⟩
  have hG₀i : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G₀⁻¹ ∈
      orthogonalGroup (quadMinus 3 F b c) := by
    rw [map_inv]
    exact inv_mem hh
  have hG₀e : (G₀ : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w₀ = w := by
    rw [← toLinEquiv_apply]
    exact hhe
  let φ : ↥(StatedOmega (StatedQuadMinus 3 F b c)) ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)) :=
    { toFun := fun g => ⟨G₀⁻¹ * g * G₀, by
        have := conj_mem_statedOmega hirr hG₀i g.2
        rwa [inv_inv] at this⟩
      invFun := fun g => ⟨G₀ * g * G₀⁻¹, conj_mem_statedOmega hirr hh g.2⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun g => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun g g' => Subtype.ext (by simp [mul_assoc]) }
  have hG₀w : ((G₀⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w = w₀ := by
    rw [← hG₀e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  refine ⟨vecStabEquivOfIff φ w w₀ fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · have h1 := conj_mulVec_fix hG₀w hg
    rwa [inv_inv] at h1
  · have h1 : ((G₀ * (G₀⁻¹ * (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * G₀) * G₀⁻¹ :
        GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w = w :=
      conj_mulVec_fix hG₀e hg
    rwa [show G₀ * (G₀⁻¹ * (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) * G₀) * G₀⁻¹ =
      (g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) by group] at h1

theorem exists_vecStab_OmegaMinus6_sing_hom {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F} (hw0 : w ≠ 0)
    (hw : StatedQuadMinus 3 F b c w = 0) :
    ∃ σ : ↥(KTabC.vecStab (StatedOmega (StatedQuadMinus 3 F b c)).subtype w) →*
        GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) F,
      IsPGroup 2 σ.ker ∧ StatedOmega (StatedQuadMinus 2 F b c) ≤ σ.range ∧
        ∀ g, Odd (orderOf (σ g)) → σ g ∈ StatedOmega (StatedQuadMinus 2 F b c) := by
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  obtain ⟨hker₀, hrange₀, hodd₀⟩ := sixMinusRes_spec (b := b) (c := c) hirr
  have he₀ : (Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ≠ 0 := fun h => by
    simpa using congrFun h (Sum.inl 0)
  have hQe₀ : StatedQuadMinus 3 F b c (Pi.single (Sum.inl 0) 1) = 0 := by
    have h0 : (Pi.single (Sum.inl 0) 1 : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ∘
        sixMinusLongEmb = 0 := funext fun z => by simp [Pi.single_apply, sixMinusLongEmb_ne_inl z]
    rw [statedQuadMinus_three_split, h0]
    simp [StatedQuadMinus]
  obtain ⟨ψ⟩ := nonempty_vecStab_omegaSixMinus_equiv hirr he₀ hw0 (by rw [hw, hQe₀])
  refine ⟨(sixMinusRes b c).comp ψ.toMonoidHom, fun ⟨g, hg⟩ => ⟨2, Subtype.ext ?_⟩,
    fun A hA => ?_, fun g hodd => hodd₀ (ψ g) hodd⟩
  · have h4 := hker₀ (ψ g) hg
    have h4' : g ^ 4 = 1 := ψ.injective (by rw [map_pow, h4, map_one])
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h4'
  · obtain ⟨g₀, hg₀⟩ := hrange₀ hA
    exact ⟨ψ.symm g₀, by simp [hg₀]⟩

end SingularStabilizer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

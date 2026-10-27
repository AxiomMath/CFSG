module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenDefs
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDict
import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaIsoOneLinear
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDvd
import CFSG.Adapters.RankTwoModelTransports
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
import CFSG.LocalAnalysis.StandardType.GGTBJSpBlockAux
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLieA
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowOmMinusSplitAux1
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2UniSquare
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.LocalAnalysis.StandardType.GGResQTwoLinearJ
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCoord
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagOmegaQuasisimple
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenComp
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256q
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHFixed
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.ClassicalGroups.Orthogonal.EichlerCentralizerScalar
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHShell

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Multiplicative
open CFSG.SeitzReduction.SymplecticPilot CFSG.StandardType.ClassicalBlocks
open CFSG.StandardType.ClassicalPosition

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m p f : ℕ} {b c : K} {ζ : Kˣ}

section Aux

open CFSG.SeitzReduction.SymplecticPilot
open CFSG.StandardType.ClassicalPosition
open Classical

private def omMinusSwap (m : ℕ) : Equiv.Perm (Fin m ⊕ Fin m ⊕ Fin 2) where
  toFun
    | Sum.inl i => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr 0) => Sum.inr (Sum.inr 1)
    | Sum.inr (Sum.inr 1) => Sum.inr (Sum.inr 0)
  invFun
    | Sum.inl i => Sum.inr (Sum.inl i)
    | Sum.inr (Sum.inl i) => Sum.inl i
    | Sum.inr (Sum.inr 0) => Sum.inr (Sum.inr 1)
    | Sum.inr (Sum.inr 1) => Sum.inr (Sum.inr 0)
  left_inv := by
    intro x
    rcases x with i | (i | j)
    · rfl
    · rfl
    · fin_cases j <;> rfl
  right_inv := by
    intro x
    rcases x with i | (i | j)
    · rfl
    · rfl
    · fin_cases j <;> rfl

@[simp] private theorem omMinusSwap_inl (m : ℕ) (i : Fin m) :
    omMinusSwap m (Sum.inl i) = Sum.inr (Sum.inl i) := rfl

@[simp] private theorem omMinusSwap_inr_inl (m : ℕ) (i : Fin m) :
    omMinusSwap m (Sum.inr (Sum.inl i)) = Sum.inl i := rfl

@[simp] private theorem omMinusSwap_inr_inr_zero (m : ℕ) :
    omMinusSwap m (Sum.inr (Sum.inr 0)) = Sum.inr (Sum.inr 1) := rfl

@[simp] private theorem omMinusSwap_inr_inr_one (m : ℕ) :
    omMinusSwap m (Sum.inr (Sum.inr 1)) = Sum.inr (Sum.inr 0) := rfl

private theorem omMinusSwap_apply_self (m : ℕ) (a : Fin m ⊕ Fin m ⊕ Fin 2) :
    omMinusSwap m (omMinusSwap m a) = a := by
  rcases a with i | (i | j)
  · rfl
  · rfl
  · fin_cases j <;> rfl

private theorem kOmMWeight_omMinusSwap (t : Fin m → Kˣ) (a : Fin m ⊕ Fin m ⊕ Fin 2) :
    kOmMWeight K m t (omMinusSwap m a) = (kOmMWeight K m t a)⁻¹ := by
  rcases a with i | (i | j)
  · simp [kOmMWeight]
  · simp [kOmMWeight]
  · fin_cases j <;> simp [kOmMWeight]

private theorem kOmMWeight_ne_zero (t : Fin m → Kˣ) (a : Fin m ⊕ Fin m ⊕ Fin 2) :
    kOmMWeight K m t a ≠ 0 := by
  rcases a with i | (i | j)
  · simp [kOmMWeight]
  · simp [kOmMWeight]
  · fin_cases j <;> simp [kOmMWeight]

private theorem aeval_diagonal_eq {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → K)
    (g : Polynomial K) :
    Polynomial.aeval (Matrix.diagonal w) g = Matrix.diagonal (fun a => g.eval (w a)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom K) w) g = _
  rw [Polynomial.aeval_algHom_apply, Matrix.diagonalAlgHom_apply]
  ext a b
  by_cases h : a = b <;> simp [h, Polynomial.aeval_fn_apply]

private lemma eq_diagonal_of_mem_adjoin_omMinus (t : Fin m → Kˣ)
    {y : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K}
    (hy : y ∈ Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) :
    ∃ g : Polynomial K, y = Matrix.diagonal (fun a => g.eval (kOmMWeight K m t a)) := by
  rw [Set.image_singleton] at hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨g, hg⟩ := hy
  refine ⟨g, hg.symm.trans ?_⟩
  rw [kOmMDiag_coe]
  exact aeval_diagonal_eq (kOmMWeight K m t) g

private theorem polarGram_quadMinus_apply (a b' : Fin m ⊕ Fin m ⊕ Fin 2) :
    LinearMap.toMatrix₂' K
        (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) a b' =
      QuadraticMap.polar (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
        (Pi.single a 1) (Pi.single b' 1) := by
  rw [LinearMap.toMatrix₂'_apply, QuadraticMap.polarBilin_apply_apply]

private theorem polarGram_statedQuadMinus_apply_eq_zero (a b' : Fin m ⊕ Fin m ⊕ Fin 2)
    (h : b' ≠ omMinusSwap m a) :
    LinearMap.toMatrix₂' K
        (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))
        a b' = 0 := by
  rw [polarGram_quadMinus_apply]
  rcases a with i | (i | j)
  · rw [QuadraticMap.polar_comm,
      CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl (n := m + 1)]
    exact Pi.single_eq_of_ne (M := fun _ => K) (by simpa using (Ne.symm h)) (1 : K)
  · rw [QuadraticMap.polar_comm,
      CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl (n := m + 1)]
    exact Pi.single_eq_of_ne (M := fun _ => K) (by simpa using (Ne.symm h)) (1 : K)
  · fin_cases j
    · have h' : b' ≠ Sum.inr (Sum.inr (1 : Fin 2)) := fun e => h (by simpa using e)
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [QuadraticMap.polar_comm]
      change QuadraticMap.polar (⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))
        (Pi.single b' 1) (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1) = 0
      rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero (n := m + 1)]
      rw [h2]
      simp only [zero_mul, mul_zero, zero_add, add_zero]
      rw [Pi.single_eq_of_ne (M := fun _ => K) (by simpa using (Ne.symm h')) (1 : K), mul_zero]
    · have h' : b' ≠ Sum.inr (Sum.inr (0 : Fin 2)) := fun e => h (by simpa using e)
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      rw [QuadraticMap.polar_comm]
      change QuadraticMap.polar (⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))
        (Pi.single b' 1) (Pi.single (Sum.inr (Sum.inr (1 : Fin 2))) 1) = 0
      rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one (n := m + 1)]
      rw [h2]
      simp only [zero_mul, mul_zero, zero_add, add_zero]
      rw [Pi.single_eq_of_ne (M := fun _ => K) (by simpa using (Ne.symm h')) (1 : K), mul_zero]

private theorem formAdj_quadMinus_diagonal
    (hnd : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).Nondegenerate)
    (hb : b ≠ 0) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K
        (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Matrix.diagonal v) = Matrix.diagonal (v ∘ omMinusSwap m) := by
  classical
  let G : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K :=
    LinearMap.toMatrix₂' K
      (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det _ hnd
  have hleft : G * formAdj (RingHom.id K) G (Matrix.diagonal v) = Matrix.diagonal v * G := by
    rw [CFSG.StandardType.ClassicalBlocks.ggOmegaBlk_formAdj_id, Matrix.diagonal_transpose]
    rw [← Matrix.mul_assoc G (G⁻¹ * Matrix.diagonal v) G,
      ← Matrix.mul_assoc G G⁻¹ (Matrix.diagonal v), Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  have hright : G * Matrix.diagonal (v ∘ omMinusSwap m) = Matrix.diagonal v * G := by
    ext a b'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : G a b' = 0
    · rw [h, zero_mul, mul_zero]
    · have hb' : b' = omMinusSwap m a := by
        by_contra hne
        exact h (polarGram_statedQuadMinus_apply_eq_zero a b' hne)
      rw [hb', Function.comp_apply, omMinusSwap_apply_self]
      exact mul_comm _ _
  calc formAdj (RingHom.id K) G (Matrix.diagonal v)
      = 1 * formAdj (RingHom.id K) G (Matrix.diagonal v) := (one_mul _).symm
    _ = (G⁻¹ * G) * formAdj (RingHom.id K) G (Matrix.diagonal v) := by
        rw [Matrix.nonsing_inv_mul G hG]
    _ = G⁻¹ * (G * formAdj (RingHom.id K) G (Matrix.diagonal v)) := by rw [Matrix.mul_assoc]
    _ = G⁻¹ * (G * Matrix.diagonal (v ∘ omMinusSwap m)) := by rw [hleft, ← hright]
    _ = (G⁻¹ * G) * Matrix.diagonal (v ∘ omMinusSwap m) := by rw [Matrix.mul_assoc]
    _ = Matrix.diagonal (v ∘ omMinusSwap m) := by rw [Matrix.nonsing_inv_mul G hG, Matrix.one_mul]

private lemma diagonal_pair_mem_adjoin_omMinus (t : Fin m → Kˣ) {lam : K} (hlam : lam ≠ 0) :
    Matrix.diagonal (fun a => if kOmMWeight K m t a = lam ∨ kOmMWeight K m t a = lam⁻¹
        then 1 else 0) ∈
      Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))) := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  have hqF : 0 < Fintype.card K - 1 := by
    have h1 : 1 < @Fintype.card K F := @Fintype.one_lt_card K F _
    omega
  let P : Polynomial K := 1 - ((Polynomial.X - Polynomial.C lam) *
    (Polynomial.X - Polynomial.C lam⁻¹)) ^ (Fintype.card K - 1)
  have hP : ∀ a, P.eval (kOmMWeight K m t a) =
      if kOmMWeight K m t a = lam ∨ kOmMWeight K m t a = lam⁻¹ then 1 else 0 := by
    intro a
    by_cases h : kOmMWeight K m t a = lam ∨ kOmMWeight K m t a = lam⁻¹
    · have hzero : (kOmMWeight K m t a - lam) * (kOmMWeight K m t a - lam⁻¹) = 0 := by
        rcases h with h | h
        · rw [h, sub_self, zero_mul]
        · rw [h, sub_self, mul_zero]
      simp [P, h, hzero, hqF.ne']
    · have h1 : kOmMWeight K m t a - lam ≠ 0 := fun h0 => h (Or.inl (sub_eq_zero.mp h0))
      have h2 : kOmMWeight K m t a - lam⁻¹ ≠ 0 := fun h0 => h (Or.inr (sub_eq_zero.mp h0))
      have hprod : (kOmMWeight K m t a - lam) * (kOmMWeight K m t a - lam⁻¹) ≠ 0 :=
        mul_ne_zero h1 h2
      have hpow : ((kOmMWeight K m t a - lam) *
          (kOmMWeight K m t a - lam⁻¹)) ^ (Fintype.card K - 1) = 1 :=
        @FiniteField.pow_card_sub_one_eq_one K _ F _ hprod
      simp [P, h, hpow]
  have hmem : Polynomial.aeval (Units.val (kOmMDiag K m t)) P ∈ Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))) := by
    rw [Set.image_singleton]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  rw [kOmMDiag_coe, aeval_diagonal_eq] at hmem
  rw [show (fun a => if kOmMWeight K m t a = lam ∨ kOmMWeight K m t a = lam⁻¹ then 1 else 0) =
    (fun a => P.eval (kOmMWeight K m t a)) from funext (fun a => (hP a).symm)]
  exact hmem

private theorem exists_diagonal_of_isPrimAdjIdemIn_omMinus
    (t : Fin m → Kˣ)
    (hnd : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).Nondegenerate)
    (hb : b ≠ 0) {ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K
        (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε) :
    ∃ v : Fin m ⊕ Fin m ⊕ Fin 2 → K, ε = Matrix.diagonal v ∧
      (∀ a, v a = 0 ∨ v a = 1) ∧
      (∀ a a', kOmMWeight K m t a = kOmMWeight K m t a' → v a = v a') ∧
      (∀ a, v a = v (omMinusSwap m a)) ∧
      ∃ lam : K, lam ≠ 0 ∧ ∀ a, v a = 1 →
        kOmMWeight K m t a = lam ∨ kOmMWeight K m t a = lam⁻¹ := by
  classical
  let A : Subalgebra K (Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) :=
    Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))
  obtain ⟨g, hg⟩ := eq_diagonal_of_mem_adjoin_omMinus t hε.1
  let v : Fin m ⊕ Fin m ⊕ Fin 2 → K := fun a => g.eval (kOmMWeight K m t a)
  have hεv : ε = Matrix.diagonal v := hg
  have hidem : IsIdempotentElem ε := hε.2.1
  have hne : ε ≠ 0 := hε.2.2.1
  have hfix : formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K
        (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))) ε = ε :=
    hε.2.2.2.1
  have hv : ∀ a, v a = 0 ∨ v a = 1 := by
    intro a
    have hsq : v a * v a = v a := by
      have h := congrArg (fun M : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K =>
        M a a)
        (show Matrix.diagonal (fun a => v a * v a) = Matrix.diagonal v from by
          rw [← Matrix.diagonal_mul_diagonal, ← hεv, hidem.eq, hεv])
      simpa [Matrix.diagonal_apply] using h
    have h3 : v a * (v a - 1) = 0 := by rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hconst : ∀ a a', kOmMWeight K m t a = kOmMWeight K m t a' → v a = v a' := by
    intro a a' h
    change g.eval (kOmMWeight K m t a) = g.eval (kOmMWeight K m t a')
    rw [h]
  have hpar : ∀ a, v a = v (omMinusSwap m a) := by
    intro a
    have hfix' : Matrix.diagonal (v ∘ omMinusSwap m) = Matrix.diagonal v := by
      rw [← formAdj_quadMinus_diagonal hnd hb v, ← hεv]
      exact hfix
    have h := congrArg (fun M : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K =>
      M a a) hfix'
    simpa using h.symm
  have hsuppne : ∃ a, v a = 1 := by
    by_contra h
    apply hne
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  obtain ⟨a₀, ha₀⟩ := hsuppne
  refine ⟨v, hεv, hv, hconst, hpar, kOmMWeight K m t a₀, kOmMWeight_ne_zero t a₀, ?_⟩
  let p : Fin m ⊕ Fin m ⊕ Fin 2 → K :=
    fun a => if kOmMWeight K m t a = kOmMWeight K m t a₀ ∨
      kOmMWeight K m t a = (kOmMWeight K m t a₀)⁻¹ then 1 else 0
  have hp : ∀ a, p a = 0 ∨ p a = 1 := by
    intro a
    unfold p
    split <;> simp
  have hppar : ∀ a, p (omMinusSwap m a) = p a := by
    intro a
    have hinv : kOmMWeight K m t (omMinusSwap m a) = (kOmMWeight K m t a)⁻¹ :=
      kOmMWeight_omMinusSwap t a
    unfold p
    by_cases h : kOmMWeight K m t a = kOmMWeight K m t a₀ ∨
        kOmMWeight K m t a = (kOmMWeight K m t a₀)⁻¹
    · have h' : kOmMWeight K m t (omMinusSwap m a) = kOmMWeight K m t a₀ ∨
          kOmMWeight K m t (omMinusSwap m a) = (kOmMWeight K m t a₀)⁻¹ := by
        rw [hinv]
        rcases h with h | h
        · right; rw [h]
        · left; rw [h, inv_inv]
      rw [if_pos h', if_pos h]
    · have h' : ¬ (kOmMWeight K m t (omMinusSwap m a) = kOmMWeight K m t a₀ ∨
          kOmMWeight K m t (omMinusSwap m a) = (kOmMWeight K m t a₀)⁻¹) := by
        rw [hinv]
        rintro (h' | h')
        · exact h (Or.inr (by have := congrArg (fun x : K => x⁻¹) h'; simpa using this))
        · exact h (Or.inl (by have := congrArg (fun x : K => x⁻¹) h'; simpa using this))
      rw [if_neg h', if_neg h]
  have hπA : Matrix.diagonal p ∈ A :=
    diagonal_pair_mem_adjoin_omMinus t (kOmMWeight_ne_zero t a₀)
  let e : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K := ε * Matrix.diagonal p
  have he_eq : e = Matrix.diagonal (fun a => v a * p a) := by
    rw [show e = Matrix.diagonal v * Matrix.diagonal p from by
      rw [show e = ε * Matrix.diagonal p from rfl, hεv], Matrix.diagonal_mul_diagonal]
  have heA : e ∈ A := Subalgebra.mul_mem _ hε.1 hπA
  have he_idem : IsIdempotentElem e := by
    rw [he_eq, isIdempotentElem_iff, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    rcases hv a with h | h <;> rcases hp a with k | k <;> rw [h, k] <;> ring
  have he_adj : formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K
        (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))) e = e := by
    rw [he_eq, formAdj_quadMinus_diagonal hnd hb]
    congr 1
    funext a
    rw [Function.comp_apply, hppar a, hpar a]
  have he_e : e * ε = e := by
    rw [he_eq, hεv, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    rcases hv a with h | h <;> rcases hp a with k | k <;> rw [h, k] <;> ring
  have he_ne : e ≠ 0 := by
    have h1 : e a₀ a₀ = 1 := by
      rw [he_eq, Matrix.diagonal_apply, if_pos rfl]
      have hp1 : p a₀ = 1 := by
        unfold p
        rw [if_pos (Or.inl rfl)]
      simp [ha₀, hp1]
    intro h0
    rw [h0, Matrix.zero_apply] at h1
    exact zero_ne_one h1
  rcases hε.2.2.2.2 e heA he_idem he_adj he_e with h0 | he
  · exact absurd h0 he_ne
  intro a ha
  by_contra h
  have h1 : p a = 0 := by
    unfold p
    rw [if_neg h]
  have hcc := congrArg (fun M : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K =>
    M a a) he
  rw [he_eq, hεv, Matrix.diagonal_apply, if_pos rfl, Matrix.diagonal_apply, if_pos rfl,
    h1, mul_zero, ha] at hcc
  exact zero_ne_one hcc

end Aux

private theorem omMinus_split_exists_idempotent
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({omMinusTorus (p := p) b c hζ t} : Set
        (StatedOmega (StatedQuadMinus (m + 1) K b c))))) :
    ∃ ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K,
      IsPrimAdjIdemIn (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
          (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
        (Algebra.adjoin K (Units.val ''
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε ∧
      CFSG.Assembly.IsComponentOf J
        ((glBlockCentralizer
            (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
            ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
              GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
              Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
          (MulEquiv.subgroupCongr (by
            rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype K := Fintype.ofFinite K
  let Φ : QuadraticForm K (Fin m ⊕ Fin m ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c
  have hnd : (QuadraticMap.polarBilin Φ).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr
  let u : Fin m → Kˣ := omMinusTorusParam m hζ t
  let b₀ : GL (Fin m ⊕ Fin m ⊕ Fin 2) K := kOmMDiag K m u
  have hQ : ⇑Φ = StatedQuadMinus (m + 1) K b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) K b c
  have hb₀ : b₀ ∈ StatedOmega ⇑Φ := by
    rw [hQ]
    exact kOmMDiag_mem b c u
  have hu_pow : u ^ p = 1 := by
    funext i
    show (TableBSymp.zmodPowHom hζ (t i)) ^ p = 1
    rw [← map_pow]
    have h1 : t i ^ p = 1 := by
      rw [← ofAdd_toAdd (t i), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
        ofAdd_zero]
    rw [h1, map_one]
  have hb₀_pow : b₀ ^ p = 1 := by
    rw [show b₀ = kOmMDiag K m u from rfl, ← map_pow, hu_pow, map_one]
  have hodd : Odd (orderOf b₀) :=
    Odd.of_dvd_nat hpodd (orderOf_dvd_of_pow_eq_one hb₀_pow)
  have h8 : 8 ≤ Fintype.card (Fin m ⊕ Fin m ⊕ Fin 2) := by
    have hc : Fintype.card (Fin m ⊕ Fin m ⊕ Fin 2) = 2 * m + 2 := by
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      ring
    omega
  have hΩ : StatedOmega ⇑Φ = StatedOmega (StatedQuadMinus (m + 1) K b c) := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
  let eΩ : ↥(StatedOmega ⇑Φ) ≃* ↥(StatedOmega (StatedQuadMinus (m + 1) K b c)) :=
    MulEquiv.subgroupCongr hΩ
  have hcent : (omegaCentralizerSubgroup Φ b₀).map eΩ.toMonoidHom =
      Subgroup.centralizer
        ({omMinusTorus (p := p) b c hζ t} :
          Set (StatedOmega (StatedQuadMinus (m + 1) K b c))) := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      show ((eΩ x : ↥(StatedOmega (StatedQuadMinus (m + 1) K b c))) :
          GL (Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2) K) *
          ((omMinusTorus (p := p) b c hζ t :
            ↥(StatedOmega (StatedQuadMinus (m + 1) K b c))) :
            GL (Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2) K) =
        ((omMinusTorus (p := p) b c hζ t :
            ↥(StatedOmega (StatedQuadMinus (m + 1) K b c))) :
            GL (Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2) K) *
          ((eΩ x : ↥(StatedOmega (StatedQuadMinus (m + 1) K b c))) :
            GL (Fin ((m + 1) - 1) ⊕ Fin ((m + 1) - 1) ⊕ Fin 2) K)
      have hx' : ((x : ↥(StatedOmega ⇑Φ)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) K) * b₀ =
          b₀ * ((x : ↥(StatedOmega ⇑Φ)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) K) := by
        have h1 : x ∈ (Subgroup.centralizer
            ({b₀} : Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))).comap
            (StatedOmega ⇑Φ).subtype := by
          simpa [omegaCentralizerSubgroup] using hx
        rwa [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at h1
      dsimp only [eΩ]
      rw [MulEquiv.subgroupCongr_apply]
      rw [coe_omMinusTorus, omMinusTorusGL_apply]
      exact hx'
    · intro hg
      refine Subgroup.mem_map.mpr ⟨eΩ.symm g, ?_, ?_⟩
      · have h2 : eΩ.symm g ∈ (Subgroup.centralizer
            ({b₀} : Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))).comap
            (StatedOmega ⇑Φ).subtype := by
          rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
          have hg'' := hg
          rw [Subgroup.mem_centralizer_singleton_iff] at hg''
          have hb : eΩ ⟨b₀, hb₀⟩ = omMinusTorus (p := p) b c hζ t := by
            apply Subtype.ext
            dsimp only [eΩ]
            rw [MulEquiv.subgroupCongr_apply, coe_omMinusTorus, omMinusTorusGL_apply]
          have hb' : eΩ.symm (omMinusTorus (p := p) b c hζ t) = ⟨b₀, hb₀⟩ := by
            rw [← hb, eΩ.symm_apply_apply]
          have h3 : eΩ.symm g * (⟨b₀, hb₀⟩ : ↥(StatedOmega ⇑Φ)) =
              (⟨b₀, hb₀⟩ : ↥(StatedOmega ⇑Φ)) * eΩ.symm g := by
            have := congrArg eΩ.symm hg''
            simpa [map_mul, hb', eΩ.symm_apply_apply] using this
          simpa using congrArg Subtype.val h3
        simpa [omegaCentralizerSubgroup] using h2
      · exact eΩ.apply_symm_apply g
  let J' : Subgroup (StatedOmega ⇑Φ) := J.map eΩ.symm.toMonoidHom
  have hJ' : CFSG.Assembly.IsComponentOf J' (omegaCentralizerSubgroup Φ b₀) := by
    have h1 : CFSG.Assembly.IsComponentOf
        (J.map eΩ.symm.toMonoidHom)
        ((Subgroup.centralizer
          ({omMinusTorus (p := p) b c hζ t} :
            Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))).map eΩ.symm.toMonoidHom) :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ eΩ.symm.toMonoidHom
        eΩ.symm.injective
    have h2 : (Subgroup.centralizer
          ({omMinusTorus (p := p) b c hζ t} :
            Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))).map eΩ.symm.toMonoidHom =
        omegaCentralizerSubgroup Φ b₀ := by
      have h3 := congrArg (fun H : Subgroup
          (StatedOmega (StatedQuadMinus (m + 1) K b c)) =>
        H.map eΩ.symm.toMonoidHom) hcent
      rw [Subgroup.map_map] at h3
      have hcomp : eΩ.symm.toMonoidHom.comp eΩ.toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext (fun y => eΩ.symm_apply_apply y)
      rw [hcomp, Subgroup.map_id] at h3
      exact h3.symm
    rwa [h2] at h1
  obtain ⟨ε, hε, hJε⟩ :=
    exists_isPrimAdjIdemIn_isComponentOf_glBlockCentralizer Φ hnd h8 b₀ hb₀ hodd J' hJ'
  refine ⟨ε, hε, ?_⟩
  have hmap : J'.map eΩ.toMonoidHom = J := by
    change (J.map eΩ.symm.toMonoidHom).map eΩ.toMonoidHom = J
    rw [Subgroup.map_map]
    have hcomp : eΩ.toMonoidHom.comp eΩ.symm.toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext (fun y => eΩ.apply_symm_apply y)
    rw [hcomp, Subgroup.map_id]
  have hJmap : CFSG.Assembly.IsComponentOf (J'.map eΩ.toMonoidHom)
      ((omegaBlockSubgroup Φ b₀ ε).map eΩ.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJε eΩ.toMonoidHom
        eΩ.injective
  rwa [hmap] at hJmap


private lemma omMinusWeight_inl_eq_one_iff
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    kOmMWeight K m (omMinusTorusParam m hζ t) (Sum.inl i) = 1 ↔ t i = 1 := by
  haveI : NeZero p := ⟨by rw [← hζo]; exact (orderOf_pos ζ).ne'⟩
  rw [kOmMWeight_inl, omMinusTorusParam_apply]
  constructor
  · exact fun h => (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp (Units.ext h)
  · intro h; rw [h, map_one]; rfl

private lemma omMinusWeight_inr_inl_eq_one_iff
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p)) (i : Fin m) :
    kOmMWeight K m (omMinusTorusParam m hζ t) (Sum.inr (Sum.inl i)) = 1 ↔ t i = 1 := by
  haveI : NeZero p := ⟨by rw [← hζo]; exact (orderOf_pos ζ).ne'⟩
  rw [kOmMWeight_inr_inl, Units.val_inv_eq_inv_val]
  constructor
  · intro h
    have h1 : ((omMinusTorusParam m hζ t i)⁻¹ : Kˣ) = 1 := Units.ext (by simpa using h)
    have h2 : omMinusTorusParam m hζ t i = 1 := inv_eq_one.mp h1
    exact (TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp (by
      simpa [omMinusTorusParam_apply] using h2)
  · intro h
    rw [omMinusTorusParam_apply, h, map_one]
    simp

private lemma omMinusWeight_eq_one_iff
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p)) (a : Fin m ⊕ Fin m ⊕ Fin 2) :
    kOmMWeight K m (omMinusTorusParam m hζ t) a = 1 ↔
      (∃ i : Fin m, a = Sum.inl i ∧ t i = 1) ∨
      (∃ i : Fin m, a = Sum.inr (Sum.inl i) ∧ t i = 1) ∨
      (∃ j : Fin 2, a = Sum.inr (Sum.inr j)) := by
  rcases a with i | (i | j)
  · rw [omMinusWeight_inl_eq_one_iff (p := p) hζ hζo (t := t) (i := i)]
    exact ⟨fun h => Or.inl ⟨i, rfl, h⟩, by
      rintro (⟨i', hi', h⟩ | ⟨i', hi', _⟩ | ⟨j', hj'⟩)
      · simpa [Sum.inl_injective hi'] using h
      · exact absurd hi' (by simp)
      · exact absurd hj' (by simp)⟩
  · rw [omMinusWeight_inr_inl_eq_one_iff (p := p) hζ hζo (t := t) (i := i)]
    exact ⟨fun h => Or.inr (Or.inl ⟨i, rfl, h⟩), by
      rintro (⟨i', hi', _⟩ | ⟨i', hi', h⟩ | ⟨j', hj'⟩)
      · exact absurd hi' (by simp)
      · simpa [Sum.inl_injective (Sum.inr_injective hi')] using h
      · exact absurd hj' (by simp)⟩
  · rw [kOmMWeight_inr_inr]
    exact ⟨fun _ => Or.inr (Or.inr ⟨j, rfl⟩), by
      rintro (⟨i', hi', _⟩ | ⟨i', hi', _⟩ | ⟨j', -⟩)
      · exact absurd hi' (by simp)
      · exact absurd hi' (by simp)
      · rfl⟩

private lemma kOmMDiag_ggJSo2_ML_apply (u : Fin m → Kˣ)
    (w : Fin m ⊕ Fin m ⊕ Fin 2 → K) :
    ggJSo2_ML (kOmMDiag K m u) w = fun a => kOmMWeight K m u a * w a := by
  ext a
  simp only [ggJSo2_ML, MulEquiv.trans_apply,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.mulVecLin_apply, kOmMDiag_coe]
  rw [Matrix.mulVec_diagonal]

private lemma omMinus_fixed_coord_zero (u : Fin m → Kˣ)
    {w : Fin m ⊕ Fin m ⊕ Fin 2 → K}
    (hw : w ∈ CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML (kOmMDiag K m u)))
    {a : Fin m ⊕ Fin m ⊕ Fin 2} (ha : kOmMWeight K m u a ≠ 1) : w a = 0 := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace,
    kOmMDiag_ggJSo2_ML_apply] at hw
  have h := congrFun hw a
  change kOmMWeight K m u a * w a = w a at h
  have h0 : (kOmMWeight K m u a - 1) * w a = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ha)

private lemma omMinus_fixed_single_mem (u : Fin m → Kˣ)
    {a : Fin m ⊕ Fin m ⊕ Fin 2} (ha : kOmMWeight K m u a = 1) :
    (Pi.single a 1 : Fin m ⊕ Fin m ⊕ Fin 2 → K) ∈
      CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML (kOmMDiag K m u)) := by
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_fixedSpace, kOmMDiag_ggJSo2_ML_apply]
  funext c
  by_cases hc : c = a
  · subst hc; simp [ha]
  · simp [Pi.single_eq_of_ne hc, hc]

private lemma omMinus_fixed_isometry
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (n1 : ℕ) (e : {i : Fin m // t i = 1} ≃ Fin n1) :
    Nonempty (((CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c).comp
      (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace
        (ggJSo2_ML (kOmMDiag K m (omMinusTorusParam m hζ t)))).subtype).IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadMinus (n1 + 1) K b c)) := by
  classical
  let u : Fin m → Kˣ := omMinusTorusParam m hζ t
  let b0 : GL (Fin m ⊕ Fin m ⊕ Fin 2) K := kOmMDiag K m u
  let V := Fin m ⊕ Fin m ⊕ Fin 2 → K
  let W : Submodule K V := CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b0)
  let σ : (Fin n1 ⊕ Fin n1 ⊕ Fin 2) → (Fin m ⊕ Fin m ⊕ Fin 2) := fun x =>
    match x with
    | Sum.inl k => Sum.inl (e.symm k)
    | Sum.inr (Sum.inl k) => Sum.inr (Sum.inl (e.symm k))
    | Sum.inr (Sum.inr j) => Sum.inr (Sum.inr j)
  have hσw : ∀ x, kOmMWeight K m u (σ x) = 1 := by
    intro x
    rcases x with k | (k | j)
    · exact (omMinusWeight_inl_eq_one_iff (p := p) hζ hζo (t := t) (i := e.symm k)).mpr
        (e.symm k).2
    · exact (omMinusWeight_inr_inl_eq_one_iff (p := p) hζ hζo (t := t) (i := e.symm k)).mpr
        (e.symm k).2
    · exact kOmMWeight_inr_inr u j
  have hσrange : ∀ a, kOmMWeight K m u a = 1 → ∃ x, σ x = a := by
    intro a ha
    rcases a with i | (i | j)
    · have hi : t i = 1 :=
        (omMinusWeight_inl_eq_one_iff (p := p) hζ hζo (t := t) (i := i)).mp ha
      exact ⟨Sum.inl (e ⟨i, hi⟩), by simp [σ]⟩
    · have hi : t i = 1 :=
        (omMinusWeight_inr_inl_eq_one_iff (p := p) hζ hζo (t := t) (i := i)).mp ha
      exact ⟨Sum.inr (Sum.inl (e ⟨i, hi⟩)), by simp [σ]⟩
    · exact ⟨Sum.inr (Sum.inr j), rfl⟩
  have hσinj : Function.Injective σ := by
    intro x y h
    rcases x with k | (k | j) <;> rcases y with l | (l | i) <;> simp only [σ] at h
    · rw [Sum.inl.injEq] at h
      rw [e.symm.injective (Subtype.ext h)]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rw [Sum.inr.injEq, Sum.inl.injEq] at h
      rw [e.symm.injective (Subtype.ext h)]
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rw [Sum.inr.injEq, Sum.inr.injEq] at h
      rw [h]
  have hgen : ∀ x, (Pi.single (σ x) 1 : V) ∈ W := by
    intro x
    simpa [W, b0] using omMinus_fixed_single_mem u (hσw x)
  let gen : (Fin n1 ⊕ Fin n1 ⊕ Fin 2) → W := fun x => ⟨Pi.single (σ x) 1, hgen x⟩
  have hgen_coe (x : Fin n1 ⊕ Fin n1 ⊕ Fin 2) : ((gen x : W) : V) = Pi.single (σ x) 1 :=
    rfl
  let lin : (Fin n1 ⊕ Fin n1 ⊕ Fin 2 → K) →ₗ[K] W :=
    { toFun := fun f => ∑ x, f x • gen x
      map_add' := by
        intro f g
        apply Subtype.ext
        funext a
        simp only [Submodule.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        apply Subtype.ext
        funext a
        simp only [Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, Finset.smul_sum,
          smul_assoc, RingHom.id_apply] }
  let ev : W →ₗ[K] (Fin n1 ⊕ Fin n1 ⊕ Fin 2 → K) :=
    { toFun := fun w x => (w : V) (σ x)
      map_add' := by intro w w'; ext x; rfl
      map_smul' := by intro c w; ext x; rfl }
  have hev_lin : ∀ f, ev (lin f) = f := by
    intro f
    ext y
    change ((lin f : W) : V) (σ y) = f y
    have hcoe : ((lin f : W) : V) = ∑ x, f x • (Pi.single (σ x) 1 : V) := by
      change ((∑ x, f x • gen x : W) : V) = ∑ x, f x • (Pi.single (σ x) 1 : V)
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Submodule.coe_smul, hgen_coe]
    have hsum : ((lin f : W) : V) (σ y) =
        ∑ x, f x * (Pi.single (σ x) 1 : V) (σ y) := by
      rw [hcoe, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single y]
    · simp
    · intro x _ hxy
      have hne : σ x ≠ σ y := fun hσ => hxy (hσinj hσ)
      have hsingle : (Pi.single (σ x) 1 : V) (σ y) = 0 := Pi.single_eq_of_ne hne.symm 1
      rw [hsingle, mul_zero]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  have hev_inj : Function.Injective ev := by
    intro w w' h
    have h' : ev (w - w') = 0 := by rw [map_sub, h, sub_self]
    have hzero : (w - w' : W) = 0 := by
      apply Subtype.ext
      funext a
      by_cases ha : kOmMWeight K m u a = 1
      · obtain ⟨x, rfl⟩ := hσrange a ha
        have hx := congrFun h' x
        change ((w - w' : W) : V) (σ x) = 0 at hx
        rw [Submodule.coe_sub, Pi.sub_apply] at hx
        change (w : V) (σ x) - (w' : V) (σ x) = 0
        exact hx
      · have hw := omMinus_fixed_coord_zero u (by simpa [W, b0] using w.2) ha
        have hw' := omMinus_fixed_coord_zero u (by simpa [W, b0] using w'.2) ha
        change (w : V) a - (w' : V) a = 0
        rw [hw, hw', sub_self]
    exact sub_eq_zero.mp hzero
  have hev_surj : Function.Surjective ev := fun f => ⟨lin f, hev_lin f⟩
  let eW : W ≃ₗ[K] (Fin n1 ⊕ Fin n1 ⊕ Fin 2 → K) :=
    LinearEquiv.ofBijective ev ⟨hev_inj, hev_surj⟩
  refine ⟨{ toLinearEquiv := eW, map_app' := ?_ }⟩
  intro w
  let wv : Fin m ⊕ Fin m ⊕ Fin 2 → K := w.1
  have hsum : (∑ i : Fin m, wv (Sum.inl i) * wv (Sum.inr (Sum.inl i))) =
      ∑ k : Fin n1, wv (σ (Sum.inl k)) * wv (σ (Sum.inr (Sum.inl k))) := by
    let F : Fin m → K := fun i => wv (Sum.inl i) * wv (Sum.inr (Sum.inl i))
    have h1 : (∑ i : Fin m, F i) = ∑ i ∈ Finset.univ.filter (fun i => t i = 1), F i := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro i _ hi
      have hti : t i ≠ 1 := by simpa using hi
      have h1 : wv (Sum.inl i) = 0 := by
        refine omMinus_fixed_coord_zero u (by simpa [W, b0, wv] using w.2) ?_
        exact fun h => hti ((omMinusWeight_inl_eq_one_iff (p := p) hζ hζo (t := t)
          (i := i)).mp h)
      have h2 : wv (Sum.inr (Sum.inl i)) = 0 := by
        refine omMinus_fixed_coord_zero u (by simpa [W, b0, wv] using w.2) ?_
        exact fun h => hti ((omMinusWeight_inr_inl_eq_one_iff (p := p) hζ hζo (t := t)
          (i := i)).mp h)
      simp [F, h1, h2]
    let Fsub : {i : Fin m // t i = 1} → K := fun i => F i
    rw [h1, Finset.sum_subtype (p := fun i => t i = 1)
      (Finset.univ.filter (fun i => t i = 1)) (by simp) F]
    exact Fintype.sum_equiv e Fsub
      (fun k => wv (σ (Sum.inl k)) * wv (σ (Sum.inr (Sum.inl k))))
      (fun i => by simp [Fsub, F, σ])
  have heW : (eW w) = fun x => wv (σ x) := by
    ext x
    rfl
  change (CFSG.LieType.Universal.Spin.quadMinus (n1 + 1) K b c) (eW w) =
    (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) w.1
  rw [heW, CFSG.LieType.Universal.Spin.quadMinus_apply,
    CFSG.LieType.Universal.Spin.quadMinus_apply]
  change (∑ k : Fin n1, wv (σ (Sum.inl k)) * wv (σ (Sum.inr (Sum.inl k))) +
      wv (Sum.inr (Sum.inr 0)) ^ 2 +
      b * wv (Sum.inr (Sum.inr 0)) * wv (Sum.inr (Sum.inr 1)) +
      c * wv (Sum.inr (Sum.inr 1)) ^ 2) =
    (∑ i : Fin m, wv (Sum.inl i) * wv (Sum.inr (Sum.inl i)) +
      wv (Sum.inr (Sum.inr 0)) ^ 2 +
      b * wv (Sum.inr (Sum.inr 0)) * wv (Sum.inr (Sum.inr 1)) +
      c * wv (Sum.inr (Sum.inr 1)) ^ 2)
  rw [hsum]

private lemma omMinus_p_dvd_card_sub_one (hζo : orderOf ζ = p) :
    p ∣ Nat.card K - 1 := by
  rw [← hζo, ← Nat.card_units]
  exact orderOf_dvd_natCard ζ

private lemma omMinusTorusGL_pow_prime (hζ : ζ ^ p = 1)
    (t : Fin m → Multiplicative (ZMod p)) :
    omMinusTorusGL (K := K) (m := m) hζ t ^ p = 1 := by
  have ht : t ^ p = 1 := by
    funext i
    change (t i) ^ p = 1
    rw [← ofAdd_toAdd (t i), ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      ofAdd_zero]
  rw [← map_pow, ht, map_one]

private lemma omMinus_odd_orderOf_kOmMDiag (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p)) :
    Odd (orderOf (kOmMDiag K m (omMinusTorusParam m hζ t))) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpow : (kOmMDiag K m (omMinusTorusParam m hζ t)) ^ p = 1 := by
    rw [← omMinusTorusGL_apply]
    exact omMinusTorusGL_pow_prime hζ t
  exact Odd.of_dvd_nat hpodd (orderOf_dvd_of_pow_eq_one hpow)

open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb in
private lemma omMinus_statedOmega_quasisimple (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {n : ℕ} (hn : 2 ≤ n) :
    CFSG.Assembly.IsQuasisimple ↥(StatedOmega (StatedQuadMinus n K b c)) := by
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
  · exact OmegaMinus.isQuasisimple_statedOmega_quadMinus_two hirr
  · exact OmegaMinus.isQuasisimple_statedOmega_quadMinus_three hirr
  · exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadMinus (by omega) hirr)

private lemma omMinus_v_eq_one_of_weight_one
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p))
    {ε : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin
        2) K}
    {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hεne : ε ≠ 0) (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a', kOmMWeight K m (omMinusTorusParam m hζ t) a =
      kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hfix : ∀ a, v a = 1 → kOmMWeight K m (omMinusTorusParam m hζ t) a = 1) :
    ∀ a, kOmMWeight K m (omMinusTorusParam m hζ t) a = 1 → v a = 1 := by
  have hvne : ∃ a, v a = 1 := by
    by_contra h
    apply hεne
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  obtain ⟨a0, ha0⟩ := hvne
  have hw0 : kOmMWeight K m (omMinusTorusParam m hζ t) a0 = 1 := hfix a0 ha0
  intro a ha
  rw [hconst a a0 (ha.trans hw0.symm)]
  exact ha0

private lemma omMinus_weight_mul_one (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t g : Fin m → Multiplicative (ZMod p))
    (hg : ∀ i, t i = 1 → g i = 1) {a : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2}
    (ha : kOmMWeight K m (omMinusTorusParam m hζ t) a = 1) :
    kOmMWeight K m (omMinusTorusParam m hζ g) a = 1 := by
  rcases (omMinusWeight_eq_one_iff (p := p) hζ hζo t a).mp ha with
    ⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩ | ⟨j, rfl⟩
  · rw [kOmMWeight_inl, omMinusTorusParam_apply, hg i hi, map_one]
    simp
  · rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, hg i hi, map_one]
    simp
  · rw [kOmMWeight_inr_inr]

private lemma omMinus_longBlock_mem_fixedBlock
    (hp : p.Prime) (hp2 : p ≠ 2) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    {ε : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin
        2) K}
    {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hεne : ε ≠ 0) (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a', kOmMWeight K m (omMinusTorusParam m hζ t) a =
      kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hfix : ∀ a, v a = 1 → kOmMWeight K m (omMinusTorusParam m hζ t) a = 1)
    {l : Fin m} (hl : t l = 1) {w : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K}
    (hw : w ∈ omMinusLongBlock K b c l)
    (hwconj : ∀ f : Fin m → Multiplicative (ZMod p),
      w * omMinusTorusGL hζ f * w⁻¹ = omMinusTorusGL hζ (SpCoord.sgnAut l f)) :
    (⟨w, omMinusLongBlock_le hirr l hw⟩ : StatedOmega (StatedQuadMinus (m + 1) K b c)) ∈
      glBlockCentralizer
        (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} :
          Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) ε := by
  classical
  have hv1 : ∀ a, kOmMWeight K m (omMinusTorusParam m hζ t) a = 1 → v a = 1 :=
    omMinus_v_eq_one_of_weight_one hζ t hεne hεv hv hconst hfix
  have hsgn : SpCoord.sgnAut l t = t := by
    funext i
    by_cases hi : i = l
    · subst hi
      simp [SpCoord.sgnAut_apply, hl]
    · simp [SpCoord.sgnAut_apply, hi]
  refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := hwconj t
    rw [hsgn] at h
    have hb0 : (kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) = omMinusTorusGL hζ t := by
      rw [omMinusTorusGL_apply]
    rw [hb0]
    calc w * omMinusTorusGL hζ t
        = (w * omMinusTorusGL hζ t * w⁻¹) * w := by group
      _ = omMinusTorusGL hζ t * w := by rw [h]
  · show (w : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1)
      ⊕ Fin 2) K) *
      (1 - ε) = 1 - ε
    have h1m : (1 - ε : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m
        + 1 - 1) ⊕ Fin 2) K) =
        Matrix.diagonal (fun a => 1 - v a) := by
      rw [hεv]
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.diagonal_apply, hab]
    rw [h1m]
    rw [omMinusLongBlock] at hw
    obtain ⟨g, -, hg⟩ := Subgroup.mem_map.mp hw
    rw [← hg, CFSG.SeitzReduction.F4Pilot.coe_coordEmbedGL]
    ext a b
    rw [Matrix.mul_diagonal]
    by_cases hb : b ∈ Set.range (kOmMLongEmb m l)
    · have hvb : v b = 1 := by
        refine hv1 b ?_
        obtain ⟨x, rfl⟩ := hb
        rcases x with x | (x | j)
        · have hx : x = 0 := Fin.ext (by omega)
          subst hx
          rw [kOmMLongEmb, Sum.map_inl, kOmMWeight_inl, omMinusTorusParam_apply, hl, map_one]
          simp
        · have hx : x = 0 := Fin.ext (by omega)
          subst hx
          rw [kOmMLongEmb, Sum.map_inr, Sum.map_inl, kOmMWeight_inr_inl,
            omMinusTorusParam_apply, hl, map_one]
          simp
        · rw [kOmMLongEmb, Sum.map_inr, Sum.map_inr, kOmMWeight_inr_inr]
      rw [hvb, sub_self, mul_zero]
      by_cases hab : a = b
      · subst hab; simp [hvb]
      · simp [Matrix.diagonal_apply, hab]
    · rw [CFSG.SeitzReduction.F4Pilot.coordEmbedMat_apply_of_not_mem (F := K)
        (g := (g : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) (a := a) (b := b)
        (fun hmem => hb hmem.2)]
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.one_apply_ne hab, Matrix.diagonal_apply, hab]

private lemma omMinus_eq_one_of_sgnAut_eq_self (hp : p.Prime) (hp2 : p ≠ 2)
    {i : Fin m} {f : Fin m → Multiplicative (ZMod p)}
    (h : SpCoord.sgnAut i f = f) : f i = 1 := by
  have hinv : (f i)⁻¹ = f i := by
    simpa [SpCoord.sgnAut_apply] using congrFun h i
  have h2 : (f i) * (f i) = 1 := by
    nth_rewrite 2 [← hinv]
    exact mul_inv_cancel (f i)
  have hd2 : orderOf (f i) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hdp : orderOf (f i) ∣ p := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rcases (Nat.dvd_prime hp).mp hdp with h1 | hp'
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [hp'] at hd2
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hd2) hp.two_le)

private theorem omMinus_split_fixed_block_data
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hfix : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a = 1)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    (1 ≤ Nat.card {i : Fin m // t i = 1} ∧
      Nonempty (↥J ≃*
        StatedOmega (StatedQuadMinus (Nat.card {i : Fin m // t i = 1} + 1) K b c))) ∧
      J = (glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hpqK : p ∣ Nat.card K - 1 := omMinus_p_dvd_card_sub_one hζo
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hK4 : 4 ≤ Nat.card K := by
    have hq2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card (α := K))
    by_contra h
    have hq3 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
    rcases hq3 with h2 | h3
    · rw [h2] at hpqK
      have := Nat.le_of_dvd (by norm_num) hpqK
      omega
    · rw [h3] at hpqK
      have := Nat.le_of_dvd (by norm_num) hpqK
      omega
  let u : Fin m → Kˣ := omMinusTorusParam m hζ t
  let b0 : GL (Fin m ⊕ Fin m ⊕ Fin 2) K := kOmMDiag K m u
  let Φ := CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c
  let W : Submodule K (Fin m ⊕ Fin m ⊕ Fin 2 → K) :=
    CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace (ggJSo2_ML b0)
  have hnd : (QuadraticMap.polarBilin Φ).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr
  have hS : StatedOmega ⇑Φ = StatedOmega (StatedQuadMinus (m + 1) K b c) := by
    rw [show ⇑Φ = StatedQuadMinus (m + 1) K b c from
      CFSG.LieType.Universal.Spin.coe_quadMinus (m + 1) K b c]
  have hb0 : b0 ∈ StatedOmega ⇑Φ := by
    rw [hS]
    simpa [b0, u] using kOmMDiag_mem b c u
  have hodd : Odd (orderOf b0) := by
    simpa [b0, u] using omMinus_odd_orderOf_kOmMDiag hp hp2 hζ t
  have hvne : ∃ a, v a = 1 := by
    by_contra h
    apply hε.2.2.1
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  have hbε : (b0 : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) * ε = ε := by
    have hbm : (b0 : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
        Matrix.diagonal (kOmMWeight K m u) := by
      rw [show b0 = kOmMDiag K m u from rfl, kOmMDiag_coe]
    rw [hεv, hbm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    by_cases ha : v a = 1
    · rw [show kOmMWeight K m u a = 1 by simpa [u] using hfix a ha, one_mul, ha]
    · rcases hv a with h0 | h1
      · rw [h0, mul_zero]
      · exact absurd h1 ha
  have hnot : ¬ (Nat.card K = 2 ∧ Module.finrank K W = 4) := by
    rintro ⟨hK2, -⟩
    omega
  have hD : CFSG.RankThree.PartOne.DicksonDerived (Φ.comp W.subtype)
      (ggJSo2_oddOrderIsometry Φ hnd b0 hb0 hodd).polarBilin_fixed_nondegenerate :=
    ggJSo2_dicksonDerived_generic Φ hnd b0 hb0 hodd hnot
  let n1 : ℕ := Nat.card {i : Fin m // t i = 1}
  have hcard : Fintype.card {i : Fin m // t i = 1} = n1 := Nat.card_eq_fintype_card.symm
  let e : {i : Fin m // t i = 1} ≃ Fin n1 := Fintype.equivFinOfCardEq hcard
  obtain ⟨eW⟩ := omMinus_fixed_isometry (b := b) (c := c) hζ hζo t n1 e
  let Gε : Subgroup (StatedOmega ⇑Φ) :=
    glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b0} : Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε
  let Gq : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c)) :=
    Gε.map (MulEquiv.subgroupCongr hS).toMonoidHom
  have hJq : CFSG.Assembly.IsComponentOf J Gq := by
    simpa [Gq, Gε, b0, u, hS] using hJε
  let eFixed : ↥Gε ≃* ↥(CFSG.RankThree.Classical2.orthDerived (Φ.comp W.subtype)) :=
    glBlockCentralizerEquivFixedDerived Φ hnd b0 hb0 hodd hε hbε hD
  let eGG : ↥Gε ≃* ↥Gq :=
    Subgroup.equivMapOfInjective Gε (MulEquiv.subgroupCongr hS).toMonoidHom
      (MulEquiv.subgroupCongr hS).injective
  let eOrth : ↥(CFSG.RankThree.Classical2.orthDerived (Φ.comp W.subtype)) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived
        (CFSG.LieType.Universal.Spin.quadMinus (n1 + 1) K b c)) :=
    CFSG.RankThree.PartOne.orthDerivedEquiv eW
  let eGq1 : ↥Gq ≃* ↥(CFSG.RankThree.Classical2.orthDerived
      (CFSG.LieType.Universal.Spin.quadMinus (Nat.card {i : Fin m // t i = 1} + 1) K b c)) := by
    simpa only [n1] using eGG.symm.trans (eFixed.trans eOrth)
  let eStd : ↥(CFSG.RankThree.Classical2.orthDerived
        (CFSG.LieType.Universal.Spin.quadMinus (n1 + 1) K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus (n1 + 1) K b c)) :=
    (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
      (Q := CFSG.LieType.Universal.Spin.quadMinus (n1 + 1) K b c) rfl).symm.trans
      (MulEquiv.subgroupCongr (by
        rw [CFSG.LieType.Universal.Spin.coe_quadMinus]))
  let eGq : ↥Gq ≃* ↥(StatedOmega (StatedQuadMinus (n1 + 1) K b c)) :=
    eGq1.trans eStd

  have hn1pos : 1 ≤ n1 := by
    rcases Nat.eq_zero_or_pos n1 with hn1 | hn1
    · exfalso
      have hcard0 : Nat.card {i : Fin m // t i = 1} = 0 := by
        rw [← show n1 = Nat.card {i : Fin m // t i = 1} from rfl]
        exact hn1
      have hdim1 : Module.finrank K (Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K) = 2 := by
        simpa using CFSG.GroupTheory.WeirSylow.finrank_quadMinus_space (K := K) (m := 1)
          (by norm_num)
      have hnd1 : (QuadraticMap.polarBilin
          (CFSG.LieType.Universal.Spin.quadMinus 1 K b c)).Nondegenerate :=
        CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 1 K hirr
      have hnd1' : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus
          (Nat.card {i : Fin m // t i = 1} + 1) K b c)).Nondegenerate :=
        CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
          (Nat.card {i : Fin m // t i = 1} + 1) K hirr
      have hdim1' : Module.finrank K
          (Fin (Nat.card {i : Fin m // t i = 1} + 1 - 1) ⊕
            Fin (Nat.card {i : Fin m // t i = 1} + 1 - 1) ⊕ Fin 2 → K) ≤ 2 := by
        rw [hcard0]
        rw [Module.finrank_fintype_fun_eq_card]
        simp
      have hcommR : ∀ x y : ↥(CFSG.RankThree.Classical2.orthDerived
          (CFSG.LieType.Universal.Spin.quadMinus (Nat.card {i : Fin m // t i = 1} + 1)
            K b c)), x * y = y * x := by
        intro x y
        exact Subtype.ext
          (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6orth_commute_orthDerived_of_finrank_le_two
            (R := CFSG.LieType.Universal.Spin.quadMinus
              (Nat.card {i : Fin m // t i = 1} + 1) K b c) hnd1' hdim1' x.2 y.2)
      have hcommG : ∀ a b : ↥Gq, a * b = b * a := by
        intro a b
        exact eGq1.injective (by
          rw [map_mul, map_mul]
          exact hcommR (eGq1 a) (eGq1 b))
      refine CFSG.StandardType.LinSemisimple.false_of_isQuasisimple_of_commute hJq.2.2 ?_
      intro x hx y hy
      exact congrArg Subtype.val (hcommG ⟨x, hJq.1 hx⟩ ⟨y, hJq.1 hy⟩)
    · omega
  have hJG : J = Gq := by
    have hn2 : 2 ≤ n1 + 1 := by omega
    have hqR : CFSG.Assembly.IsQuasisimple ↥(StatedOmega (StatedQuadMinus (n1 + 1) K b c)) :=
      omMinus_statedOmega_quasisimple hirr hn2
    have hqG : CFSG.Assembly.IsQuasisimple ↥Gq :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv eGq hqR
    exact CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hqG hJq
  refine ⟨⟨?_, ?_⟩, hJG⟩
  · simpa [n1] using hn1pos
  · exact ⟨(MulEquiv.subgroupCongr hJG).trans eGq⟩

private theorem omMinus_split_fixed_block
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hfix : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a = 1)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    1 ≤ Nat.card {i : Fin m // t i = 1} ∧
      Nonempty (↥J ≃*
        StatedOmega (StatedQuadMinus (Nat.card {i : Fin m // t i = 1} + 1) K b c)) := by
  exact (omMinus_split_fixed_block_data hp hp2 hm hirr hζ hζo t ε v hε hεv hv
    hconst hsym hfix hJε).1

section FibreProjections

open Classical

private lemma diagonal_single_weight_mem_adjoin_omMinus (t : Fin m → Kˣ) {lam : K} :
    Matrix.diagonal (fun a => if kOmMWeight K m t a = lam then (1 : K) else 0) ∈
      Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))) := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  have hqF : 0 < Fintype.card K - 1 := by
    have h1 : 1 < @Fintype.card K F := @Fintype.one_lt_card K F _
    omega
  let P : Polynomial K := 1 - (Polynomial.X - Polynomial.C lam) ^ (Fintype.card K - 1)
  have hP : ∀ a, P.eval (kOmMWeight K m t a) =
      if kOmMWeight K m t a = lam then (1 : K) else 0 := by
    intro a
    by_cases h : kOmMWeight K m t a = lam
    · have hzero : kOmMWeight K m t a - lam = 0 := sub_eq_zero.mpr h
      simp [P, h, hzero, hqF.ne']
    · have h1 : kOmMWeight K m t a - lam ≠ 0 := fun h0 => h (sub_eq_zero.mp h0)
      have hpow : (kOmMWeight K m t a - lam) ^ (Fintype.card K - 1) = 1 :=
        @FiniteField.pow_card_sub_one_eq_one K _ F _ h1
      simp [P, h, hpow]
  have hmem : Polynomial.aeval (Units.val (kOmMDiag K m t)) P ∈ Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))) := by
    rw [Set.image_singleton]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  rw [kOmMDiag_coe, aeval_diagonal_eq] at hmem
  rw [show (fun a => if kOmMWeight K m t a = lam then (1 : K) else 0) =
    (fun a => P.eval (kOmMWeight K m t a)) from funext (fun a => (hP a).symm)]
  exact hmem

private lemma isPrimIdemIn_diagonal_single_weight (t : Fin m → Kˣ) {lam : K}
    (hfib : ∃ a, kOmMWeight K m t a = lam) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m t : GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K))))
      (Matrix.diagonal (fun a => if kOmMWeight K m t a = lam then (1 : K) else 0)) := by
  classical
  refine ⟨diagonal_single_weight_mem_adjoin_omMinus t, ?_, ?_, ?_⟩
  · rw [isIdempotentElem_iff, Matrix.diagonal_mul_diagonal, Matrix.diagonal_injective.eq_iff]
    funext a
    by_cases h : kOmMWeight K m t a = lam <;> simp [h]
  · intro hf
    rw [Matrix.diagonal_eq_zero] at hf
    obtain ⟨a, ha⟩ := hfib
    have h := congrFun hf a
    simp [ha] at h
  · intro e' he'A he'idem he'e
    obtain ⟨g, hg⟩ := eq_diagonal_of_mem_adjoin_omMinus t he'A
    have hout : ∀ a, kOmMWeight K m t a ≠ lam → g.eval (kOmMWeight K m t a) = 0 := by
      intro a ha
      have h := he'e
      rw [hg, Matrix.diagonal_mul_diagonal, Matrix.diagonal_injective.eq_iff] at h
      have h2 := congrFun h a
      simp only [Pi.mul_apply, Pi.zero_apply, ha, if_false, mul_zero] at h2
      exact h2.symm
    have hidem : ∀ a, g.eval (kOmMWeight K m t a) * g.eval (kOmMWeight K m t a) =
        g.eval (kOmMWeight K m t a) := by
      intro a
      have h := he'idem.eq
      rw [hg, Matrix.diagonal_mul_diagonal, Matrix.diagonal_injective.eq_iff] at h
      have h2 := congrFun h a
      simpa [Pi.mul_apply] using h2
    obtain ⟨a₀, ha₀⟩ := hfib
    have hc : g.eval lam * g.eval lam = g.eval lam := by
      have := hidem a₀
      rwa [ha₀] at this
    have hroot : g.eval lam * (g.eval lam - 1) = 0 := by
      rw [mul_sub, mul_one, hc, sub_self]
    rcases mul_eq_zero.mp hroot with h0 | h1
    · left
      rw [hg, Matrix.diagonal_eq_zero]
      funext a
      by_cases h : kOmMWeight K m t a = lam
      · rw [h]; exact h0
      · exact hout a h
    · right
      rw [hg, Matrix.diagonal_injective.eq_iff]
      funext a
      by_cases h : kOmMWeight K m t a = lam
      · rw [h]
        simp only [if_pos rfl]
        exact sub_eq_zero.mp h1
      · rw [hout a h, if_neg h]

private lemma zmodPowHom_ne_inv (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) {lam : Multiplicative (ZMod p)} (hlam : lam ≠ 1) :
    TableBSymp.zmodPowHom hζ lam ≠ (TableBSymp.zmodPowHom hζ lam)⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  intro h
  apply hlam
  have hlinv : lam = lam⁻¹ := (ReflSp.zmodPowHom_injective (K := K) hζ hζo)
    (h.trans (map_inv (TableBSymp.zmodPowHom hζ) lam).symm)
  have h2 : lam * lam = 1 := by
    nth_rewrite 2 [hlinv]
    exact mul_inv_cancel lam
  have hp1 : lam ^ p = 1 := by
    rw [← ofAdd_toAdd lam, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      ofAdd_zero]
  have hdvd2 : orderOf lam ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hdvdp : orderOf lam ∣ p := orderOf_dvd_of_pow_eq_one hp1
  have hcop : Nat.Coprime 2 p := hpodd.coprime_two_left
  have hone : orderOf lam = 1 := by
    refine Nat.dvd_one.mp ?_
    have hh := Nat.dvd_gcd hdvd2 hdvdp
    rwa [hcop] at hh
  exact orderOf_eq_one_iff.mp hone

private lemma finrank_diagonal_omMinus_eq_card (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hv : ∀ a, v a = 0 ∨ v a = 1) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (Matrix.diagonal v))) =
      Fintype.card {a // v a = 1} := by
  have hlin : (Matrix.toLin (Pi.basisFun K (Fin m ⊕ Fin m ⊕ Fin 2))
      (Pi.basisFun K (Fin m ⊕ Fin m ⊕ Fin 2))) (Matrix.diagonal v) =
      Matrix.toLin' (Matrix.diagonal v) := by
    rw [Matrix.toLin_eq_toLin']
  rw [← hlin, ← Matrix.rank_eq_finrank_range_toLin (Matrix.diagonal v)
    (Pi.basisFun K (Fin m ⊕ Fin m ⊕ Fin 2)) (Pi.basisFun K (Fin m ⊕ Fin m ⊕ Fin 2)),
    Matrix.rank_diagonal]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_)
  intro a
  simp only [Equiv.refl_apply]
  constructor
  · intro h
    rcases hv a with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h
    rw [h]
    exact one_ne_zero

private lemma omMinus_split_linear_support
    (hζ : ζ ^ p = 1) (lam : Multiplicative (ZMod p))
    (u : Fin m → Kˣ) (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hconst : ∀ a a', kOmMWeight K m u a = kOmMWeight K m u a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 → kOmMWeight K m u a = (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m u a = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹)
    (hne : ∃ a, v a = 1) :
    ∀ a, (kOmMWeight K m u a = (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m u a = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) → v a = 1 := by
  obtain ⟨a₀, ha₀⟩ := hne
  have h0 := hsupp a₀ ha₀
  intro a ha
  rcases h0 with h0 | h0
  · rcases ha with ha | ha
    · exact (hconst a a₀ (ha.trans h0.symm)).trans ha₀
    · rw [hsym a]
      refine (hconst _ _ ?_).trans ha₀
      rw [kOmMWeight_omMinusSwap, ha, inv_inv]
      exact h0.symm
  · rcases ha with ha | ha
    · rw [hsym a]
      refine (hconst _ _ ?_).trans ha₀
      rw [kOmMWeight_omMinusSwap, ha]
      exact h0.symm
    · exact (hconst a a₀ (ha.trans h0.symm)).trans ha₀

private lemma omMinus_split_linear_finrank
    (hp : p.Prime) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p)) (lam : Multiplicative (ZMod p)) (hlam : lam ≠ 1)
    (u : Fin m → Kˣ) (hu : ∀ i, u i = TableBSymp.zmodPowHom hζ (t i))
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hsupp : ∀ a, v a = 1 → kOmMWeight K m u a = (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m u a = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹)
    (hsupp1 : ∀ a, (kOmMWeight K m u a = (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m u a = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) → v a = 1) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (Matrix.diagonal v))) =
      2 * Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hinj := ReflSp.zmodPowHom_injective (K := K) hζ hζo
  have hwinl : ∀ i : Fin m, kOmMWeight K m u (Sum.inl i) =
      (TableBSymp.zmodPowHom hζ (t i) : K) := by
    intro i
    rw [kOmMWeight_inl, hu i]
  have hwinr : ∀ i : Fin m, kOmMWeight K m u (Sum.inr (Sum.inl i)) =
      ((TableBSymp.zmodPowHom hζ (t i) : K))⁻¹ := by
    intro i
    rw [kOmMWeight_inr_inl, hu i, Units.val_inv_eq_inv_val]
  have hclass_inl : ∀ i : Fin m,
      (kOmMWeight K m u (Sum.inl i) = (TableBSymp.zmodPowHom hζ lam : K) ∨
        kOmMWeight K m u (Sum.inl i) = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) ↔
        (t i = lam ∨ t i = lam⁻¹) := by
    intro i
    rw [hwinl i]
    constructor
    · rintro (h | h)
      · exact Or.inl (hinj (Units.ext h))
      · refine Or.inr (hinj (Units.ext ?_))
        rw [map_inv, Units.val_inv_eq_inv_val]
        exact h
    · rintro (h | h)
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h, map_inv, Units.val_inv_eq_inv_val])
  have hclass_inr : ∀ i : Fin m,
      (kOmMWeight K m u (Sum.inr (Sum.inl i)) = (TableBSymp.zmodPowHom hζ lam : K) ∨
        kOmMWeight K m u (Sum.inr (Sum.inl i)) = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) ↔
        (t i = lam ∨ t i = lam⁻¹) := by
    intro i
    rw [hwinr i]
    constructor
    · rintro (h | h)
      · refine Or.inr (hinj (Units.ext ?_))
        rw [map_inv, Units.val_inv_eq_inv_val]
        exact inv_eq_iff_eq_inv.mp h
      · refine Or.inl (hinj (Units.ext ?_))
        exact inv_inj.mp h
    · rintro (h | h)
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, map_inv, Units.val_inv_eq_inv_val, inv_inv])
  have hv1 : ∀ a, v a = 1 ↔ (kOmMWeight K m u a = (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m u a = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) :=
    fun a => ⟨hsupp a, hsupp1 a⟩
  have htail : ∀ j : Fin 2, ¬ (kOmMWeight K m u (Sum.inr (Sum.inr j)) =
      (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m u (Sum.inr (Sum.inr j)) = ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) := by
    intro j h
    have h1 : (TableBSymp.zmodPowHom hζ lam : K) = 1 := by
      rw [kOmMWeight_inr_inr] at h
      rcases h with h | h
      · exact h.symm
      · exact inv_eq_one.mp h.symm
    exact hlam ((TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp (Units.ext h1))
  have hcard : Fintype.card {a : Fin m ⊕ Fin m ⊕ Fin 2 // v a = 1} =
      2 * Fintype.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
    let fwd : {a : Fin m ⊕ Fin m ⊕ Fin 2 // v a = 1} →
        {i : Fin m // t i = lam ∨ t i = lam⁻¹} × Bool := fun a => by
      rcases a with ⟨a, ha⟩
      rcases a with i | i | j
      · exact (⟨i, (hclass_inl i).mp ((hv1 (Sum.inl i)).mp ha)⟩, true)
      · exact (⟨i, (hclass_inr i).mp ((hv1 (Sum.inr (Sum.inl i))).mp ha)⟩, false)
      · exact absurd ((hv1 (Sum.inr (Sum.inr j))).mp ha) (htail j)
    let bwd : {i : Fin m // t i = lam ∨ t i = lam⁻¹} × Bool →
        {a : Fin m ⊕ Fin m ⊕ Fin 2 // v a = 1} := fun q => by
      rcases q with ⟨⟨i, hi⟩, b⟩
      cases b
      · exact ⟨Sum.inr (Sum.inl i), (hv1 (Sum.inr (Sum.inl i))).mpr ((hclass_inr i).mpr hi)⟩
      · exact ⟨Sum.inl i, (hv1 (Sum.inl i)).mpr ((hclass_inl i).mpr hi)⟩
    have hleft : Function.LeftInverse bwd fwd := by
      rintro ⟨a, ha⟩
      rcases a with i | i | j
      · exact Subtype.ext rfl
      · exact Subtype.ext rfl
      · exact absurd ((hv1 (Sum.inr (Sum.inr j))).mp ha) (htail j)
    have hright : Function.RightInverse bwd fwd := by
      rintro ⟨⟨i, hi⟩, b⟩
      cases b <;> exact Prod.ext (Subtype.ext rfl) rfl
    have hbij : Function.Bijective fwd := ⟨hleft.injective, hright.surjective⟩
    have h1 : Fintype.card {a : Fin m ⊕ Fin m ⊕ Fin 2 // v a = 1} =
        Fintype.card ({i : Fin m // t i = lam ∨ t i = lam⁻¹} × Bool) :=
      Fintype.card_congr (Equiv.ofBijective fwd hbij)
    rw [h1, Fintype.card_prod, Fintype.card_bool]
    simp [Nat.mul_comm]
  rw [finrank_diagonal_omMinus_eq_card v hv, hcard, Nat.card_eq_fintype_card]

end FibreProjections

private theorem omMinus_split_linear_block_data
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (lam : Multiplicative (ZMod p)) (hlam : lam ≠ 1)
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
          TableBSymp.zmodPowHom hζ lam ∨
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam)⁻¹)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    ∃ mlam : ℕ, 2 ≤ mlam ∧
      mlam = Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} ∧
      Nonempty (↥J ≃* StatedSL mlam K) ∧
      ∀ y ∈ ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom),
        y * y = 1 → y ∈ J := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hpqK : p ∣ Nat.card K - 1 := by
    rw [← hζo, ← Nat.card_units]
    exact orderOf_dvd_natCard ζ
  have hnd : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr
  have h8 : 8 ≤ Fintype.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) := by
    have hc : Fintype.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) = 2 * m + 2 := by
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      omega
    omega
  have hcoe : ((kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) =
      Matrix.diagonal (kOmMWeight K m (omMinusTorusParam m hζ t)) :=
    kOmMDiag_coe _
  have hwinv : (TableBSymp.zmodPowHom hζ lam : K) ≠
      ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    intro h
    exact zmodPowHom_ne_inv hp hp2 hζ hζo hlam (Units.ext h)
  have hsuppK : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a = (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ := by
    intro a ha
    rcases hsupp a ha with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (Units.val_inv_eq_inv_val _))
  have hvne : ∃ a, v a = 1 := by
    by_contra h
    apply hε.2.2.1
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  have hsupp1 : ∀ a, (kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) → v a = 1 :=
    omMinus_split_linear_support (p := p) (m := m) hζ lam (omMinusTorusParam m hζ t) v
      hconst hsym hsuppK hvne
  have hfib1 : ∃ a, kOmMWeight K m (omMinusTorusParam m hζ t) a =
      (TableBSymp.zmodPowHom hζ lam : K) := by
    obtain ⟨a₀, ha₀⟩ := hvne
    rcases hsuppK a₀ ha₀ with h | h
    · exact ⟨a₀, h⟩
    · exact ⟨omMinusSwap m a₀, by simp [kOmMWeight_omMinusSwap, h]⟩
  have hfib2 : ∃ a, kOmMWeight K m (omMinusTorusParam m hζ t) a =
      ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ := by
    obtain ⟨a₀, ha₀⟩ := hvne
    rcases hsuppK a₀ ha₀ with h | h
    · exact ⟨omMinusSwap m a₀, by simp [kOmMWeight_omMinusSwap, h]⟩
    · exact ⟨a₀, h⟩
  let e : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
      (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K :=
    Matrix.diagonal (fun a =>
      if kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) then (1 : K) else 0)
  let e' : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
      (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K :=
    Matrix.diagonal (fun a =>
      if kOmMWeight K m (omMinusTorusParam m hζ t) a =
        ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ then (1 : K) else 0)
  have hedef : e = Matrix.diagonal (fun a =>
      if kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) then (1 : K) else 0) := rfl
  have he'def : e' = Matrix.diagonal (fun a =>
      if kOmMWeight K m (omMinusTorusParam m hζ t) a =
        ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ then (1 : K) else 0) := rfl
  have he : IsPrimIdemIn (Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} :
        Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)))) e :=
    isPrimIdemIn_diagonal_single_weight (omMinusTorusParam m hζ t) hfib1
  have he' : IsPrimIdemIn (Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} :
        Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)))) e' :=
    isPrimIdemIn_diagonal_single_weight (omMinusTorusParam m hζ t) hfib2
  have hene : e ≠ e' := by
    obtain ⟨a₀, ha₀⟩ := hfib1
    intro h
    rw [hedef, he'def, Matrix.diagonal_injective.eq_iff] at h
    have h1 := congrFun h a₀
    rw [ha₀] at h1
    simp only [if_pos rfl, if_neg hwinv] at h1
    exact one_ne_zero h1
  have hεe : ε = e + e' := by
    have hnat : (Matrix.diagonal v : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) = e + e' := by
      rw [hedef, he'def, Matrix.diagonal_add, Matrix.diagonal_injective.eq_iff]
      funext a
      by_cases h1 : kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam : K)
      · have h2 : ¬ (kOmMWeight K m (omMinusTorusParam m hζ t) a =
            ((TableBSymp.zmodPowHom hζ lam : K))⁻¹) := fun h2 => hwinv (h1.symm.trans h2)
        rw [if_pos h1, if_neg h2, hsupp1 a (Or.inl h1)]
        norm_num
      · by_cases h2 : kOmMWeight K m (omMinusTorusParam m hζ t) a =
            ((TableBSymp.zmodPowHom hζ lam : K))⁻¹
        · rw [if_neg h1, if_pos h2, hsupp1 a (Or.inr h2)]
          norm_num
        · have h0 : v a = 0 := by
            rcases hv a with h0 | h0
            · exact h0
            · exact absurd (hsuppK a h0) (fun h => h.elim h1 h2)
          rw [if_neg h1, if_neg h2, h0]
          norm_num
    exact hεv.trans hnat
  have hbpow : ((kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ^ p = 1 := by
    have hupow : ∀ i : Fin m, omMinusTorusParam m hζ t i ^ p = 1 := by
      intro i
      rw [omMinusTorusParam_apply, ← map_pow, ← ofAdd_toAdd (t i), ← ofAdd_nsmul,
        nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero, map_one]
    rw [hcoe, Matrix.diagonal_pow, ← Matrix.diagonal_one,
      Matrix.diagonal_injective.eq_iff]
    funext a
    rcases a with i | i | j
    · rw [Pi.pow_apply, kOmMWeight_inl, ← Units.val_pow_eq_pow_val, hupow i, Units.val_one]
    · rw [Pi.pow_apply, kOmMWeight_inr_inl, ← Units.val_pow_eq_pow_val, inv_pow, hupow i,
        inv_one, Units.val_one]
    · rw [Pi.pow_apply, kOmMWeight_inr_inr, one_pow]
  have hbpowGL : (kOmMDiag K m (omMinusTorusParam m hζ t) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hbpow
  have hodd : Odd (orderOf (kOmMDiag K m (omMinusTorusParam m hζ t) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) :=
    hpodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hbpowGL)
  have hb0 : (kOmMDiag K m (omMinusTorusParam m hζ t) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ∈
      StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) := by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus,
      ← omMinusTorusGL_apply (K := K) (m := m) (p := p) hζ t]
    exact omMinusTorusGL_mem b c hζ t
  obtain ⟨d, mm, E, hEf, hEfi, hd1, hEcard, hrank, hdeg, ⟨eG⟩⟩ :=
    blockGroup_iso_Omega_linear (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)
      hnd h8 (kOmMDiag K m (omMinusTorusParam m hζ t)) hb0 hodd hε he he' hene hεe
  letI : Field E := hEf
  letI : Fintype E := hEfi
  have hpqK' : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpqK
  have hmemS : (kOmMDiag K m (omMinusTorusParam m hζ t) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ∈
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} : Set _) :=
    Set.mem_singleton _
  have hScomm : ∀ s ∈ ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} : Set _),
      ∀ s' ∈ ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} : Set _), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    subst hs
    subst hs'
    exact Commute.refl _
  have hSodd : ∀ s ∈ ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} : Set _), Odd (orderOf s) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hodd
  have hSpow : ∀ s ∈ ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} : Set _),
      ∃ c : K, (s : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
          (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) ^ p =
        Matrix.scalar (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (c ^ p) := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨1, by simp [hbpow]⟩
  have hdeg1 : blockDegree (Algebra.adjoin K (Units.val ''
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} :
        Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)))) e = 1 :=
    CFSG.StandardType.TableCRes.blockDegree_eq_one_of_pow_eq_pow (p := p)
      (ι := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (F := K) hp hpqK' hScomm hSodd
      hSpow he
  have hd : d = 1 := by
    rw [← hdeg]
    exact hdeg1
  have hfinrank : Module.finrank K (LinearMap.range (Matrix.toLin' ε)) =
      2 * Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
    rw [hεv]
    exact omMinus_split_linear_finrank (p := p) (m := m) hp hζ hζo t lam hlam
      (omMinusTorusParam m hζ t) (fun _ => rfl) v hv hsuppK hsupp1
  have hmm : mm = Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
    have h2 : 2 * d * mm = 2 * Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} :=
      hrank.trans hfinrank
    rw [hd] at h2
    omega
  have hEcard1 : Fintype.card E = Fintype.card K := by
    rw [hEcard, hd, pow_one]
  let σ : E ≃+* K := FiniteField.ringEquivOfCardEq hEcard1
  let glc : GL (Fin mm) E ≃* GL (Fin mm) K :=
    CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin mm) σ
  let Fblk : Subgroup (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) :=
    glBlockCentralizer
      (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} :
        Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) ε
  let σg : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) ≃*
      StatedOmega (StatedQuadMinus (m + 1) K b c) :=
    MulEquiv.subgroupCongr (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus])
  have hJε' : CFSG.Assembly.IsComponentOf J (Fblk.map σg.toMonoidHom) := hJε
  have eF : ↥Fblk ≃* GL (Fin mm) K := eG.trans glc
  have eK : ↥(Fblk.map σg.toMonoidHom) ≃* GL (Fin mm) K :=
    (Subgroup.equivMapOfInjective Fblk σg.toMonoidHom σg.injective).symm.trans eF
  have hcompJ : CFSG.Assembly.IsComponentOf (J.subgroupOf (Fblk.map σg.toMonoidHom)) ⊤ := by
    have hC₀ : (J.subgroupOf (Fblk.map σg.toMonoidHom)).map
        (Fblk.map σg.toMonoidHom).subtype = J := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJε'.1]
    have hH : (⊤ : Subgroup ↥(Fblk.map σg.toMonoidHom)).map
        (Fblk.map σg.toMonoidHom).subtype = Fblk.map σg.toMonoidHom := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (Fblk.map σg.toMonoidHom).subtype_injective, hC₀, hH]
    exact hJε'
  have himg : CFSG.Assembly.IsComponentOf
      ((J.subgroupOf (Fblk.map σg.toMonoidHom)).map eK.toMonoidHom) ⊤ := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := eK.toMonoidHom) eK.injective).2 hcompJ
    rwa [Subgroup.map_top_of_surjective _ eK.surjective] at h
  have hSL : (J.subgroupOf (Fblk.map σg.toMonoidHom)).map eK.toMonoidHom = StatedSL mm K :=
    CFSG.StandardType.eq_statedSL_of_isComponentOf_top himg
  have hcompSL : CFSG.Assembly.IsComponentOf (StatedSL mm K) ⊤ := hSL ▸ himg
  have hmm2 : 2 ≤ mm := by
    by_contra hlt
    have hle : mm ≤ 1 := by omega
    haveI : Subsingleton ↥(StatedSL mm K) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_subsingleton_statedSL_of_le_one hle
    have hntriv : Nontrivial ↥(StatedSL mm K) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_nontrivial_of_isQuasisimple hcompSL.2.2
    obtain ⟨x, y, hxy⟩ := hntriv.exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  refine ⟨mm, hmm2, hmm, ?_, ?_⟩
  · exact ⟨componentEquivStatedSLOfMulEquiv eK hJε'⟩
  · intro y hy hy2
    have hsq : eK ⟨y, hy⟩ * eK ⟨y, hy⟩ = 1 := by
      have h1 : (⟨y, hy⟩ : ↥(Fblk.map σg.toMonoidHom)) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
      rw [← map_mul, h1, map_one]
    have hmem : eK ⟨y, hy⟩ ∈ StatedSL mm K := ggTBJSpB_mem_statedSL_of_mul_self hsq
    rw [← hSL] at hmem
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hmem
    have hke' : k = ⟨y, hy⟩ := eK.injective hke
    have hkJ : (k : StatedOmega (StatedQuadMinus (m + 1) K b c)) ∈ J := hk
    rw [hke'] at hkJ
    simpa using hkJ

private theorem omMinus_split_linear_block
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (lam : Multiplicative (ZMod p)) (hlam : lam ≠ 1)
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
          TableBSymp.zmodPowHom hζ lam ∨
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam)⁻¹)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    2 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} ∧
      Nonempty (↥J ≃* Matrix.SpecialLinearGroup
        (Fin (Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹})) K) := by
  obtain ⟨mlam, h2, hmlam, ⟨eiso⟩, -⟩ :=
    omMinus_split_linear_block_data hp hp2 hm hirr hζ hζo t lam hlam ε v hε hεv hv hconst
      hsym hsupp hJε
  refine ⟨?_, ?_⟩
  · rw [← hmlam]
    exact h2
  · rw [← hmlam]
    exact ⟨eiso.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL mlam K).symm⟩

private theorem omMinus_split_linear_inv_mem
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (lam : Multiplicative (ZMod p)) (hlam : lam ≠ 1)
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
          TableBSymp.zmodPowHom hζ lam ∨
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam)⁻¹)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    ∀ y ∈ (glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom,
      y * y = 1 → y ∈ J := by
  obtain ⟨-, -, -, -, hinv⟩ :=
    omMinus_split_linear_block_data hp hp2 hm hirr hζ hζo t lam hlam ε v hε hεv hv hconst
      hsym hsupp hJε
  exact hinv

private lemma glBlockCentralizer_map_subgroupCongr {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (S : Set (GL ι F)) (ε : Matrix ι ι F) {H₁ H₂ : Subgroup (GL ι F)}
    (h : H₁ = H₂) :
    (glBlockCentralizer H₁.subtype S ε).map (MulEquiv.subgroupCongr h).toMonoidHom =
      glBlockCentralizer H₂.subtype S ε := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    show ((MulEquiv.subgroupCongr h y : H₂) : GL ι F) ∈
      Subgroup.centralizer S ⊓ glFixing (1 - ε)
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.mem_comap.mp hy
  · intro x hx
    have hx' : ((x : H₂) : GL ι F) ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp hx
    let y : H₁ := ⟨(x : GL ι F), by rw [h]; exact x.2⟩
    have hy : y ∈ glBlockCentralizer H₁.subtype S ε := Subgroup.mem_comap.mpr hx'
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    exact Subtype.ext (MulEquiv.subgroupCongr_apply h y)

private theorem omMinus_split_criterion_fixed
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hfix : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a = 1)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    ∀ g : Fin m → Multiplicative (ZMod p),
      (∀ j ∈ J,
        omMinusTorus (p := p) b c hζ g * j = j * omMinusTorus (p := p) b c hζ g) ↔
        ∀ i, t i = 1 → g i = 1 := by
  classical
  haveI : NeZero p := ⟨by rw [← hζo]; exact (orderOf_pos ζ).ne'⟩
  have hεne : ε ≠ 0 := hε.2.2.1
  have hGid : (glBlockCentralizer
      (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
      (MulEquiv.subgroupCongr (by
        rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom =
    glBlockCentralizer
      (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε :=
    glBlockCentralizer_map_subgroupCongr _ ε (by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus])
  intro g
  constructor
  · intro hcentral l hl
    obtain ⟨w, hw, hwconj⟩ := exists_sgn_mem_omMinusLongBlock (b := b) (c := c) hirr hζ l
    have hwG : (⟨w, omMinusLongBlock_le hirr l hw⟩ :
        StatedOmega (StatedQuadMinus (m + 1) K b c)) ∈
        glBlockCentralizer
          (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε :=
      omMinus_longBlock_mem_fixedBlock hp hp2 hirr hζ hζo t hεne hεv hv hconst hfix hl hw
        hwconj
    have hJG : J = (glBlockCentralizer
        (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom :=
      (omMinus_split_fixed_block_data hp hp2 hm hirr hζ hζo t ε v hε hεv hv hconst hsym hfix
        hJε).2
    have hwJ : (⟨w, omMinusLongBlock_le hirr l hw⟩ :
        StatedOmega (StatedQuadMinus (m + 1) K b c)) ∈ J := by
      rw [hJG, hGid]
      exact hwG
    have hcommGL : (omMinusTorusGL hζ g) * w = w * (omMinusTorusGL hζ g) := by
      have h := congrArg (fun x : StatedOmega (StatedQuadMinus (m + 1) K b c) =>
        (x : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) (hcentral _ hwJ)
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
      change (omMinusTorusGL hζ g) * w = w * (omMinusTorusGL hζ g) at h
      exact h
    have h2 : w⁻¹ * omMinusTorusGL hζ g * w = omMinusTorusGL hζ g := by
      rw [mul_assoc, hcommGL, ← mul_assoc, inv_mul_cancel, one_mul]
    have hconj : omMinusTorusGL hζ (SpCoord.sgnAut l g) = omMinusTorusGL hζ g := by
      rw [← hwconj g]
      calc w * omMinusTorusGL hζ g * w⁻¹
          = w * (w⁻¹ * omMinusTorusGL hζ g * w) * w⁻¹ := by rw [h2]
        _ = omMinusTorusGL hζ g := by group
    exact omMinus_eq_one_of_sgnAut_eq_self hp hp2 (omMinusTorusGL_injective hζ hζo hconj)
  · intro hg j hj
    have hj' : j ∈ glBlockCentralizer
        (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε := by
      rw [← hGid]
      exact hJε.1 hj
    have hjmem := Subgroup.mem_comap.mp hj'
    have hjcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hjmem).1
    let jm : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K := j
    have hjfix' : (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
        (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v := by
      have h : ((StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype j :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K) ∈ glFixing (1 - ε) :=
        (Subgroup.mem_inf.mp hjmem).2
      rw [hεv] at h
      exact h
    have hjcommM : (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
        (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
        (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
          (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) := by
      have h := congrArg Units.val hjcomm
      change (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
          (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
        (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
          (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) at h
      exact h
    rw [kOmMDiag_coe] at hjcommM
    have hx : ∀ a b, v a = 1 → v b = 1 →
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          kOmMWeight K m (omMinusTorusParam m hζ t) b →
        kOmMWeight K m (omMinusTorusParam m hζ g) a =
          kOmMWeight K m (omMinusTorusParam m hζ g) b := by
      intro a b ha hb _
      rw [omMinus_weight_mul_one hζ hζo t g hg (hfix a ha),
        omMinus_weight_mul_one hζ hζo t g hg (hfix b hb)]
    have hmat := ggTBJSpB_diagonal_mul_eq_mul_of_block v
      (fun a => kOmMWeight K m (omMinusTorusParam m hζ t) a)
      (fun a => kOmMWeight K m (omMinusTorusParam m hζ g) a)
      (Units.val jm) hv hjfix' hjcommM hconst hx
    refine Subtype.ext (Units.ext ?_)
    change (omMinusTorusGL hζ g : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) * (Units.val jm) =
      (Units.val jm) * (omMinusTorusGL hζ g : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)
    rw [omMinusTorusGL_apply, kOmMDiag_coe]
    exact hmat

section OmMinusSplitLinearAux

open CFSG.SeitzReduction.SymplecticPilot CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal QuadraticMap Matrix

private lemma polar_inl (j : Fin (m + 1 - 1)) (v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (m+1) K b c) (Pi.single (Sum.inl j) 1) v = v (Sum.inr (Sum.inl j)) :=
  polar_single_inl_quadMinus (n := m+1) j v

private lemma polar_inr (j : Fin (m + 1 - 1)) (v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (m+1) K b c) (Pi.single (Sum.inr (Sum.inl j)) 1) v = v (Sum.inl j) :=
  polar_single_inr_quadMinus (n := m+1) j v

private lemma add_self_add_char2 {R : Type} [Ring R] [CharP R 2] (a b : R) :
    a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private lemma add_add_self_char2 {R : Type} [Ring R] [CharP R 2] (a b : R) :
    a + (b + a) = b := by
  have h : a + (b + a) = b + (a + a) := by abel
  rw [h, CharTwo.add_self_eq_zero, add_zero]

private lemma planePerm_apply_inl (i k j : Fin (m + 1 - 1)) :
    (Equiv.sumCongr (Equiv.swap i k)
      (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2))))
        (Sum.inl j : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) = Sum.inl (Equiv.swap i k j) := rfl

private lemma planePerm_apply_inr (i k j : Fin (m + 1 - 1)) :
    (Equiv.sumCongr (Equiv.swap i k)
      (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2))))
        (Sum.inr (Sum.inl j) : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) =
      Sum.inr (Sum.inl (Equiv.swap i k j)) := rfl

private lemma planePerm_apply_tail (i k : Fin (m + 1 - 1)) (t : Fin 2) :
    (Equiv.sumCongr (Equiv.swap i k)
      (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2))))
        (Sum.inr (Sum.inr t) : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) = Sum.inr (Sum.inr t) :=
            rfl

private lemma plane_qu (i k : Fin (m + 1 - 1)) :
    quadMinus (m+1) K b c
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2
          → K) = 0 := by
  rw [QuadraticMap.map_add (quadMinus (m+1) K b c),
    quadMinus_single_inl (n := m+1) i, quadMinus_single_inl (n := m+1) k, polar_inl i]
  simp [Pi.single_apply]

private lemma plane_qw (i k : Fin (m + 1 - 1)) :
    quadMinus (m+1) K b c
      (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1 :
        Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) = 0 := by
  rw [QuadraticMap.map_add (quadMinus (m+1) K b c),
    quadMinus_single_inr (n := m+1) i, quadMinus_single_inr (n := m+1) k, polar_inr i]
  simp [Pi.single_apply]

private lemma plane_pol (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    polar (quadMinus (m+1) K b c)
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2
          → K)
      (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1) = 0 := by
  rw [polar_add_left, polar_add_right, polar_add_right,
    polar_inl i (Pi.single (Sum.inr (Sum.inl i)) 1), polar_inl i (Pi.single (Sum.inr (Sum.inl k))
        1),
    polar_inl k (Pi.single (Sum.inr (Sum.inl i)) 1), polar_inl k (Pi.single (Sum.inr (Sum.inl k))
        1)]
  simp [Pi.single_apply, hik, Ne.symm hik]
  linear_combination (1 : K) * CharTwo.two_eq_zero (R := K)




private lemma polar_tail0 (v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (m+1) K b c) (Pi.single (Sum.inr (Sum.inr 0)) 1) v =
      2 * v (Sum.inr (Sum.inr 0)) + b * v (Sum.inr (Sum.inr 1)) := by
  rw [polar_comm, polar_quadMinus_single_inr_inr_zero]

private lemma polar_tail1 (v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus (m+1) K b c) (Pi.single (Sum.inr (Sum.inr 1)) 1) v =
      b * v (Sum.inr (Sum.inr 0)) + 2 * c * v (Sum.inr (Sum.inr 1)) := by
  rw [polar_comm, polar_quadMinus_single_inr_inr_one]

private lemma plane_single_full (i k : Fin (m + 1 - 1)) (hik : i ≠ k)
    (a : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :
    eichler (quadMinus (m+1) K b c)
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2
          → K)
      (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1)
      (Pi.single a 1) =
    Pi.single ((Equiv.sumCongr (Equiv.swap i k)
      (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2)))) a) 1 := by
  rcases a with j | (j | t)
  · by_cases hji : j = i
    · subst j
      rw [eichler_apply (plane_qu i k) (plane_pol i k hik), plane_qw i k,
        polar_inl i (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1),
        polar_inl i (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
        planePerm_apply_inl, Equiv.swap_apply_left]
      funext x
      rcases x with x | (x | t) <;>
        simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
          add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
    · by_cases hjk : j = k
      · subst j
        rw [eichler_apply (plane_qu i k) (plane_pol i k hik), plane_qw i k,
          polar_inl k (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1),
          polar_inl k (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
          planePerm_apply_inl, Equiv.swap_apply_right]
        funext x
        rcases x with x | (x | t) <;> simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
            add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
      · rw [eichler_apply_of_polar_eq_zero, planePerm_apply_inl,
          Equiv.swap_apply_of_ne_of_ne hji hjk]
        · rw [polar_inl j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
        · rw [polar_inl j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
  · by_cases hji : j = i
    · subst j
      rw [eichler_apply (plane_qu i k) (plane_pol i k hik), plane_qw i k,
        polar_inr i (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1),
        polar_inr i (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
        planePerm_apply_inr, Equiv.swap_apply_left]
      funext x
      rcases x with x | (x | t) <;>
        simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
          add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
    · by_cases hjk : j = k
      · subst j
        rw [eichler_apply (plane_qu i k) (plane_pol i k hik), plane_qw i k,
          polar_inr k (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1),
          polar_inr k (Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
          planePerm_apply_inr, Equiv.swap_apply_right]
        funext x
        rcases x with x | (x | t) <;> simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
            add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
      · rw [eichler_apply_of_polar_eq_zero, planePerm_apply_inr,
          Equiv.swap_apply_of_ne_of_ne hji hjk]
        · rw [polar_inr j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
        · rw [polar_inr j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
  · rw [eichler_apply_of_polar_eq_zero, planePerm_apply_tail]
    · fin_cases t
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 0)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail0]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 1)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail1]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]
    · fin_cases t
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 0)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail0]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 1)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail1]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]


private lemma mixed_qu (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    quadMinus (m+1) K b c
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1 :
        Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) = 0 := by
  rw [QuadraticMap.map_add (quadMinus (m+1) K b c),
    quadMinus_single_inl (n := m+1) i, quadMinus_single_inr (n := m+1) k, polar_inl i]
  simp [Pi.single_apply, hik]

private lemma mixed_qw (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    quadMinus (m+1) K b c
      (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1 :
        Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) = 0 := by
  rw [QuadraticMap.map_add (quadMinus (m+1) K b c),
    quadMinus_single_inl (n := m+1) k, quadMinus_single_inr (n := m+1) i, polar_inl k]
  simp [Pi.single_apply, Ne.symm hik]

private lemma mixed_pol (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    polar (quadMinus (m+1) K b c)
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1 :
        Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K)
      (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1) = 0 := by
  rw [polar_add_left, polar_add_right, polar_add_right,
    polar_inl i (Pi.single (Sum.inl k) 1),
    polar_inl i (Pi.single (Sum.inr (Sum.inl i)) 1),
    polar_inr k (Pi.single (Sum.inl k) 1),
    polar_inr k (Pi.single (Sum.inr (Sum.inl i)) 1)]
  simp [Pi.single_apply, hik, Ne.symm hik]
  linear_combination (1 : K) * CharTwo.two_eq_zero (R := K)

private lemma mixedPerm_apply_inl_self (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inl i) =
        Sum.inr (Sum.inl k) := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hik]

private lemma mixedPerm_apply_inl_other (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inl k) =
        Sum.inr (Sum.inl i) := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hik]

private lemma mixedPerm_apply_inr_self (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inr (Sum.inl k)) =
        Sum.inl i := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hik, Ne.symm hik]

private lemma mixedPerm_apply_inr_other (i k : Fin (m + 1 - 1)) (hik : i ≠ k) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inr (Sum.inl i)) =
        Sum.inl k := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hik, Ne.symm hik]

private lemma mixedPerm_apply_inl_of_ne (i k j : Fin (m + 1 - 1)) (hji : j ≠ i) (hjk : j ≠ k) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inl j) =
        Sum.inl j := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hji, hjk]

private lemma mixedPerm_apply_inr_of_ne (i k j : Fin (m + 1 - 1)) (hji : j ≠ i) (hjk : j ≠ k) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inr (Sum.inl j)) =
        Sum.inr (Sum.inl j) := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, hji, hjk]

private lemma mixedPerm_apply_tail (i k : Fin (m + 1 - 1)) (t : Fin 2) :
    ((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k) : Fin
        (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) : Equiv.Perm _) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
          Equiv.Perm _)) (Sum.inr (Sum.inr t)) =
        Sum.inr (Sum.inr t) := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def]

private lemma mixed_single_full (i k : Fin (m + 1 - 1)) (hik : i ≠ k)
    (a : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :
    eichler (quadMinus (m+1) K b c)
      (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1 :
        Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K)
      (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1)
      (Pi.single a 1) =
    Pi.single (((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr
        (Sum.inl k)) :
        Equiv.Perm _) * (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr
            (Sum.inl i)) : Equiv.Perm _)) a) 1 := by
  rcases a with j | (j | t)
  · by_cases hji : j = i
    · subst j
      rw [eichler_apply (mixed_qu i k hik) (mixed_pol i k hik), mixed_qw i k hik,
        polar_inl i (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
        polar_inl i (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1),
        mixedPerm_apply_inl_self i k hik]
      funext x
      rcases x with x | (x | t) <;>
        simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
          add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
    · by_cases hjk : j = k
      · subst j
        rw [eichler_apply (mixed_qu i k hik) (mixed_pol i k hik), mixed_qw i k hik,
          polar_inl k (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
          polar_inl k (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1),
          mixedPerm_apply_inl_other i k hik]
        funext x
        rcases x with x | (x | t) <;>
          simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
            add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
      · rw [eichler_apply_of_polar_eq_zero, mixedPerm_apply_inl_of_ne i k j hji hjk]
        · rw [polar_inl j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
        · rw [polar_inl j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
  · by_cases hji : j = i
    · subst j
      rw [eichler_apply (mixed_qu i k hik) (mixed_pol i k hik), mixed_qw i k hik,
        polar_inr i (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
        polar_inr i (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1),
        mixedPerm_apply_inr_other i k hik]
      funext x
      rcases x with x | (x | t) <;>
        simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
          add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
    · by_cases hjk : j = k
      · subst j
        rw [eichler_apply (mixed_qu i k hik) (mixed_pol i k hik), mixed_qw i k hik,
          polar_inr k (Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1),
          polar_inr k (Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1),
          mixedPerm_apply_inr_self i k hik]
        funext x
        rcases x with x | (x | t) <;>
          simp [hik, Ne.symm hik, Pi.single_apply, CharTwo.neg_eq,
            add_self_add_char2, add_add_self_char2, CharTwo.add_self_eq_zero]
      · rw [eichler_apply_of_polar_eq_zero, mixedPerm_apply_inr_of_ne i k j hji hjk]
        · rw [polar_inr j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
        · rw [polar_inr j]; simp [Pi.add_apply, Pi.single_apply, hji, hjk]
  · rw [eichler_apply_of_polar_eq_zero, mixedPerm_apply_tail]
    · fin_cases t
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 0)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail0]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 1)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail1]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]
    · fin_cases t
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 0)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail0]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]
      · change polar (quadMinus (m+1) K b c)
          (Pi.single (Sum.inr (Sum.inr 1)) 1 : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) _ = 0
        rw [polar_tail1]; simp [Pi.add_apply, Pi.single_apply, CharTwo.two_eq_zero]

private lemma mulVec_single_entry {ι : Type} [Fintype ι] [DecidableEq ι] {E : Matrix ι ι K}
    (a b : ι) :
    (E *ᵥ Pi.single b 1) a = E a b := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

private lemma perm_diag_comm {ι : Type} [Fintype ι] [DecidableEq ι] {E : Matrix ι ι K}
    {σ : Equiv.Perm ι}
    (hE : ∀ b, E *ᵥ Pi.single b 1 = Pi.single (σ b) 1) {w : ι → K}
    (hw : ∀ b, w (σ b) = w b) :
    E * Matrix.diagonal w = Matrix.diagonal w * E := by
  ext a b
  have hEb : E a b = if a = σ b then 1 else 0 := by
    have h := congrFun (hE b) a
    rw [mulVec_single_entry] at h
    simpa [Pi.single_apply, eq_comm] using h
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hEb]
  by_cases h : a = σ b
  · rw [if_pos h, one_mul, mul_one, h, hw b]
  · rw [if_neg h, zero_mul, mul_zero]

private lemma perm_glFixing {ι : Type} [Fintype ι] [DecidableEq ι] {E : Matrix ι ι K}
    {σ : Equiv.Perm ι}
    (hE : ∀ b, E *ᵥ Pi.single b 1 = Pi.single (σ b) 1) {v : ι → K}
    (hv : ∀ b, σ b ≠ b → v b = 1) :
    E * (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v := by
  have hD : (1 - Matrix.diagonal v) = Matrix.diagonal (fun c => 1 - v c) := by
    ext c d
    rw [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hcd : c = d <;> simp [hcd]
  have hEb : ∀ a b, E a b = if a = σ b then 1 else 0 := by
    intro a b
    have h := congrFun (hE b) a
    rw [mulVec_single_entry] at h
    simpa [Pi.single_apply, eq_comm] using h
  rw [hD]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply, hEb]
  by_cases hab : a = b
  · subst hab
    by_cases hσ : a = σ a
    · rw [if_pos hσ, one_mul, if_pos rfl]
    · rw [if_neg hσ, zero_mul, if_pos rfl]
      have hv1 : v a = 1 := hv a (by intro e; exact hσ e.symm)
      rw [hv1, sub_self]
  · rw [if_neg hab]
    by_cases h : a = σ b
    · rw [if_pos h, one_mul]
      have hne : σ b ≠ b := by intro e; exact hab (h.trans e)
      rw [hv b hne, sub_self]
    · rw [if_neg h, zero_mul]

private lemma diag_comm_weight {ι : Type} [Fintype ι] [DecidableEq ι] {E : Matrix ι ι K}
    {σ : Equiv.Perm ι}
    (hE : ∀ b, E *ᵥ Pi.single b 1 = Pi.single (σ b) 1) {w : ι → K}
    (hcomm : E * Matrix.diagonal w = Matrix.diagonal w * E) :
    ∀ b, w (σ b) = w b := by
  intro b
  have hEb : E (σ b) b = 1 := by
    have h := congrFun (hE b) (σ b)
    rw [mulVec_single_entry] at h
    simpa [Pi.single_apply] using h
  have h := congrFun (congrFun hcomm (σ b)) b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hEb] at h
  simpa using h.symm

private lemma support_iff [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p)) {lam : Multiplicative (ZMod p)}
    {ε : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin
        2) K}
    {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hεv : ε = Matrix.diagonal v) (hεne : ε ≠ 0)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a', kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 → kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹) :
    ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹ := by
  classical
  have hex : ∃ a, v a = 1 := by
    by_contra h
    apply hεne
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  obtain ⟨a₀, ha₀⟩ := hex
  have hkey : ∀ b, kOmMWeight K m (omMinusTorusParam m hζ t) b =
      kOmMWeight K m (omMinusTorusParam m hζ t) a₀ → v b = 1 := by
    intro b hb
    rw [hconst b a₀ hb]
    exact ha₀
  intro a
  constructor
  · exact hsupp a
  · intro hw
    rcases hsupp a₀ ha₀ with hz | hz
    · rcases hw with hwa | hwa
      · exact hkey a (hwa.trans hz.symm)
      · have hswap : kOmMWeight K m (omMinusTorusParam m hζ t) (omMinusSwap m a) =
            kOmMWeight K m (omMinusTorusParam m hζ t) a₀ := by
          rw [kOmMWeight_omMinusSwap, hwa, ← hz] <;> simp
        rw [hsym a]
        exact hkey (omMinusSwap m a) hswap
    · rcases hw with hwa | hwa
      · have hswap : kOmMWeight K m (omMinusTorusParam m hζ t) (omMinusSwap m a) =
            kOmMWeight K m (omMinusTorusParam m hζ t) a₀ := by
          rw [kOmMWeight_omMinusSwap, hwa, ← hz] <;> simp
        rw [hsym a]
        exact hkey (omMinusSwap m a) hswap
      · exact hkey a (hwa.trans hz.symm)

private lemma zpow_lam_ne_inv [NeZero p] {lam : Multiplicative (ZMod p)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (hlam : lam ≠ 1) :
    (TableBSymp.zmodPowHom hζ lam : K) ≠
      ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have h' : TableBSymp.zmodPowHom hζ lam = (TableBSymp.zmodPowHom hζ lam)⁻¹ :=
    Units.ext (by simpa using h)
  have hsq : TableBSymp.zmodPowHom hζ lam * TableBSymp.zmodPowHom hζ lam = 1 := by
    nth_rewrite 2 [h']
    exact mul_inv_cancel _
  have hpow : (TableBSymp.zmodPowHom hζ lam) ^ p = 1 := by
    rw [TableBSymp.zmodPowHom_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hone := CFSG.AGLEmbedding.Norton.MON5_7.eq_one_of_sq_eq_one_of_pow_eq_one hp2 hpow hsq
  exact hlam ((TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp hone)

private lemma tail_not_mem [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p)) {lam : Multiplicative (ZMod p)}
    (hlam : lam ≠ 1) {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hsupiff : ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹) (j : Fin 2) :
    v (Sum.inr (Sum.inr j)) ≠ 1 := by
  intro hv
  have hw1 : kOmMWeight K m (omMinusTorusParam m hζ t) (Sum.inr (Sum.inr j)) = 1 :=
    kOmMWeight_inr_inr (omMinusTorusParam m hζ t) j
  have hz1 : (TableBSymp.zmodPowHom hζ lam : K) ≠ 1 := by
    intro e
    exact hlam ((TableBSymp.zmodPowHom_eq_one_iff hζ hζo).mp (Units.ext e))
  have hzi1 : ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ ≠ 1 := by
    intro e
    apply hz1
    rw [← inv_inv (TableBSymp.zmodPowHom hζ lam)] at e
    exact inv_injective (by simpa using e)
  rcases (hsupiff _).mp hv with h | h
  · rw [hw1] at h
    exact hz1 h.symm
  · rw [hw1] at h
    exact hzi1 h.symm

private lemma zpow_eq_iff [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {a b : Multiplicative (ZMod p)} :
    ((TableBSymp.zmodPowHom hζ a : Kˣ) : K) =
      ((TableBSymp.zmodPowHom hζ b : Kˣ) : K) ↔ a = b := by
  constructor
  · intro h
    exact ReflSp.zmodPowHom_injective hζ hζo (Units.ext h)
  · intro h; rw [h]

private lemma zpow_eq_inv_iff [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    {a b : Multiplicative (ZMod p)} :
    ((TableBSymp.zmodPowHom hζ a : Kˣ) : K) =
      (((TableBSymp.zmodPowHom hζ b : Kˣ) : K))⁻¹ ↔ a = b⁻¹ := by
  constructor
  · intro h
    have h1 : ((TableBSymp.zmodPowHom hζ a : Kˣ) : K)⁻¹ =
        ((TableBSymp.zmodPowHom hζ b : Kˣ) : K) := by
      rw [h, inv_inv]
    have h2 : (TableBSymp.zmodPowHom hζ a)⁻¹ = TableBSymp.zmodPowHom hζ b :=
      Units.ext (by simpa using h1)
    have h3 : TableBSymp.zmodPowHom hζ a = (TableBSymp.zmodPowHom hζ b)⁻¹ := by
      rw [← h2, inv_inv]
    rw [← map_inv] at h3
    exact ReflSp.zmodPowHom_injective hζ hζo h3
  · intro h
    rw [h, map_inv, Units.val_inv_eq_inv_val]

private lemma dv_of_support [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t g : Fin m → Multiplicative (ZMod p)) {lam : Multiplicative (ZMod p)}
    (hlam : lam ≠ 1) (d : Multiplicative (ZMod p))
    (hd : ∀ i, (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))
    {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hsupiff : ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹) :
    ∀ a, v a = 1 →
      (kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam : K) →
        kOmMWeight K m (omMinusTorusParam m hζ g) a =
          (TableBSymp.zmodPowHom hζ d : K)) ∧
      (kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam : K)⁻¹ →
        kOmMWeight K m (omMinusTorusParam m hζ g) a =
          ((TableBSymp.zmodPowHom hζ d : Kˣ) : K)⁻¹) := by
  intro a ha
  rcases a with i | (i | j)
  · have hw : kOmMWeight K m (omMinusTorusParam m hζ t) (Sum.inl i) =
        ((TableBSymp.zmodPowHom hζ (t i) : Kˣ) : K) :=
      kOmMWeight_inl (omMinusTorusParam m hζ t) i
    have hg : kOmMWeight K m (omMinusTorusParam m hζ g) (Sum.inl i) =
        ((TableBSymp.zmodPowHom hζ (g i) : Kˣ) : K) :=
      kOmMWeight_inl (omMinusTorusParam m hζ g) i
    constructor
    · intro h
      have hti : t i = lam := zpow_eq_iff hζ hζo |>.mp (by rwa [hw] at h)
      rw [hg, hd i |>.1 hti] <;> simp
    · intro h
      have hti : t i = lam⁻¹ := zpow_eq_inv_iff hζ hζo |>.mp (by rwa [hw] at h)
      rw [hg, hd i |>.2 hti] <;> simp [map_inv]
  · have hw : kOmMWeight K m (omMinusTorusParam m hζ t) (Sum.inr (Sum.inl i)) =
        ((TableBSymp.zmodPowHom hζ (t i) : Kˣ) : K)⁻¹ := by
      rw [kOmMWeight_inr_inl, omMinusTorusParam_apply]
      simp
    have hg : kOmMWeight K m (omMinusTorusParam m hζ g) (Sum.inr (Sum.inl i)) =
        ((TableBSymp.zmodPowHom hζ (g i) : Kˣ) : K)⁻¹ := by
      rw [kOmMWeight_inr_inl, omMinusTorusParam_apply]
      simp
    constructor
    · intro h
      have h' : ((TableBSymp.zmodPowHom hζ (t i) : Kˣ) : K) =
          (((TableBSymp.zmodPowHom hζ lam : Kˣ) : K))⁻¹ := by
        have h1 : ((TableBSymp.zmodPowHom hζ (t i) : Kˣ) : K)⁻¹ =
            ((TableBSymp.zmodPowHom hζ lam : Kˣ) : K) := by
          simpa [hw] using h
        rw [← h1, inv_inv]
      have hti : t i = lam⁻¹ := zpow_eq_inv_iff hζ hζo |>.mp h'
      rw [hg, hd i |>.2 hti] <;> simp [map_inv]
    · intro h
      have h' : ((TableBSymp.zmodPowHom hζ (t i) : Kˣ) : K) =
          ((TableBSymp.zmodPowHom hζ lam : Kˣ) : K) := by
        have h1 : ((TableBSymp.zmodPowHom hζ (t i) : Kˣ) : K)⁻¹ =
            (((TableBSymp.zmodPowHom hζ lam : Kˣ) : K))⁻¹ := by
          simpa [hw] using h
        exact inv_injective h1
      have hti : t i = lam := zpow_eq_iff hζ hζo |>.mp h'
      rw [hg, hd i |>.1 hti] <;> simp
  · exact absurd ha (tail_not_mem hζ hζo t hlam hsupiff j)

private lemma hx_of_coord [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t g : Fin m → Multiplicative (ZMod p)) {lam : Multiplicative (ZMod p)}
    (hlam : lam ≠ 1) (d : Multiplicative (ZMod p))
    (hd : ∀ i, (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))
    {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hsupiff : ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹)
    (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2}
    (hva : v a = 1) (hvb : v b = 1)
    (hw : kOmMWeight K m (omMinusTorusParam m hζ t) a =
      kOmMWeight K m (omMinusTorusParam m hζ t) b) :
    kOmMWeight K m (omMinusTorusParam m hζ g) a =
      kOmMWeight K m (omMinusTorusParam m hζ g) b := by
  have hzne : (TableBSymp.zmodPowHom hζ lam : K) ≠
      ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ :=
    zpow_lam_ne_inv hp hp2 hζ hζo hlam
  have ha := dv_of_support hζ hζo t g hlam d hd hsupiff a hva
  have hb := dv_of_support hζ hζo t g hlam d hd hsupiff b hvb
  rcases (hsupiff a).mp hva with ha1 | ha1
  · have hb1 : kOmMWeight K m (omMinusTorusParam m hζ t) b =
        (TableBSymp.zmodPowHom hζ lam : K) := by rw [← hw, ha1]
    rw [ha.1 ha1, hb.1 hb1]
  · have hb1 : kOmMWeight K m (omMinusTorusParam m hζ t) b =
        ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ := by rw [← hw, ha1]
    rw [ha.2 ha1, hb.2 hb1]

private lemma omMinus_split_mem_block_of_perm
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p))
    (ε : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin
        2) K)
    (v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) (hεv : ε = Matrix.diagonal v)
    {E : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K}
    (hS : E ∈ StatedOmega ⇑(quadMinus (m+1) K b c))
    {σ : Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)}
    (hE : ∀ a, (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1
        - 1) ⊕ Fin 2) K) *ᵥ
      Pi.single a 1 = Pi.single (σ a) 1)
    (hw0 : ∀ a, kOmMWeight K m (omMinusTorusParam m hζ t) (σ a) =
      kOmMWeight K m (omMinusTorusParam m hζ t) a)
    (hv1 : ∀ a, σ a ≠ a → v a = 1) :
    (⟨E, hS⟩ : StatedOmega ⇑(quadMinus (m+1) K b c)) ∈
      glBlockCentralizer (StatedOmega ⇑(quadMinus (m+1) K b c)).subtype
        ({kOmMDiag K m (omMinusTorusParam m hζ t)} :
          Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) ε := by
  rw [glBlockCentralizer, Subgroup.mem_comap]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, kOmMDiag_coe]
    exact perm_diag_comm hE hw0
  · change (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Fin (m + 1 - 1) ⊕ Fin (m + 1 -
      1) ⊕ Fin 2) K) * (1 - ε) =
      1 - ε
    rw [hεv]
    exact perm_glFixing hE hv1

private lemma omMinus_split_plane_weight_invariant
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p)) {i k : Fin m} (ht : t i = t k) :
    ∀ a : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2,
      kOmMWeight K m (omMinusTorusParam m hζ t)
        ((Equiv.sumCongr (Equiv.swap i k)
          (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2)))) a) =
      kOmMWeight K m (omMinusTorusParam m hζ t) a := by
  intro a
  rcases a with j | (j | t)
  · rw [planePerm_apply_inl, kOmMWeight_inl, kOmMWeight_inl, omMinusTorusParam_apply,
      omMinusTorusParam_apply]
    by_cases hji : j = i
    · subst j; rw [Equiv.swap_apply_left, ht]
    · by_cases hjk : j = k
      · subst j; rw [Equiv.swap_apply_right, ht.symm]
      · rw [Equiv.swap_apply_of_ne_of_ne hji hjk]
  · rw [planePerm_apply_inr, kOmMWeight_inr_inl, kOmMWeight_inr_inl,
      omMinusTorusParam_apply, omMinusTorusParam_apply]
    by_cases hji : j = i
    · subst j; rw [Equiv.swap_apply_left, ht]
    · by_cases hjk : j = k
      · subst j; rw [Equiv.swap_apply_right, ht.symm]
      · rw [Equiv.swap_apply_of_ne_of_ne hji hjk]
  · rw [planePerm_apply_tail]

private lemma omMinus_split_plane_moved_v
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p))
    {lam : Multiplicative (ZMod p)} {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hsupiff : ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹)
    {i k : Fin m} (ht : t i = t k) (hmem : t i = lam ∨ t i = lam⁻¹) :
    ∀ a, (Equiv.sumCongr (Equiv.swap i k)
        (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2)))) a ≠ a → v a = 1 := by
  have hxi : v (Sum.inl i) = 1 := by
    refine (hsupiff _).mpr ?_
    rcases hmem with h | h
    · left; rw [kOmMWeight_inl, omMinusTorusParam_apply, h]
    · right; rw [kOmMWeight_inl, omMinusTorusParam_apply, h] <;> simp [map_inv]
  have hxk : v (Sum.inl k) = 1 := by
    refine (hsupiff _).mpr ?_
    rcases hmem with h | h
    · left; rw [kOmMWeight_inl, omMinusTorusParam_apply, ← ht, h]
    · right; rw [kOmMWeight_inl, omMinusTorusParam_apply, ← ht, h] <;> simp [map_inv]
  have hyi : v (Sum.inr (Sum.inl i)) = 1 := by
    refine (hsupiff _).mpr ?_
    rcases hmem with h | h
    · right; rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, h] <;> simp [map_inv]
    · left; rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, h] <;> simp [map_inv]
  have hyk : v (Sum.inr (Sum.inl k)) = 1 := by
    refine (hsupiff _).mpr ?_
    rcases hmem with h | h
    · right; rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, ← ht, h] <;> simp [map_inv]
    · left; rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, ← ht, h] <;> simp [map_inv]
  intro a ha
  rcases a with j | (j | t)
  · by_cases hji : j = i
    · subst j; exact hxi
    · by_cases hjk : j = k
      · subst j; exact hxk
      · exfalso; apply ha
        rw [planePerm_apply_inl, Equiv.swap_apply_of_ne_of_ne hji hjk]
  · by_cases hji : j = i
    · subst j; exact hyi
    · by_cases hjk : j = k
      · subst j; exact hyk
      · exfalso; apply ha
        rw [planePerm_apply_inr, Equiv.swap_apply_of_ne_of_ne hji hjk]
  · exfalso; apply ha; rw [planePerm_apply_tail]

private lemma omMinus_split_mixed_weight_invariant
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p))
    {lam : Multiplicative (ZMod p)} {i k : Fin m} (hti : t i = lam) (htk : t k = lam⁻¹)
    (hik : i ≠ k) :
    ∀ a : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2,
      kOmMWeight K m (omMinusTorusParam m hζ t)
        (((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k))
            :
            Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) *
          (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i))
              :
            Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2))) a) =
      kOmMWeight K m (omMinusTorusParam m hζ t) a := by
  intro a
  rcases a with j | (j | t)
  · by_cases hji : j = i
    · subst j
      rw [mixedPerm_apply_inl_self i k hik]
      rw [kOmMWeight_inl, kOmMWeight_inr_inl, omMinusTorusParam_apply,
        omMinusTorusParam_apply, hti, htk] <;> simp [map_inv]
    · by_cases hjk : j = k
      · subst j
        rw [mixedPerm_apply_inl_other i k hik]
        rw [kOmMWeight_inl, kOmMWeight_inr_inl, omMinusTorusParam_apply,
          omMinusTorusParam_apply, hti, htk] <;> simp [map_inv]
      · rw [mixedPerm_apply_inl_of_ne i k j hji hjk]
  · by_cases hji : j = i
    · subst j
      rw [mixedPerm_apply_inr_other i k hik]
      rw [kOmMWeight_inl, kOmMWeight_inr_inl, omMinusTorusParam_apply,
        omMinusTorusParam_apply, hti, htk] <;> simp [map_inv]
    · by_cases hjk : j = k
      · subst j
        rw [mixedPerm_apply_inr_self i k hik]
        rw [kOmMWeight_inr_inl, kOmMWeight_inl, omMinusTorusParam_apply,
          omMinusTorusParam_apply, hti, htk] <;> simp [map_inv]
      · rw [mixedPerm_apply_inr_of_ne i k j hji hjk]
  · rw [mixedPerm_apply_tail]

private lemma omMinus_split_mixed_moved_v
    (hζ : ζ ^ p = 1) (t : Fin m → Multiplicative (ZMod p))
    {lam : Multiplicative (ZMod p)} {v : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K}
    (hsupiff : ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        (TableBSymp.zmodPowHom hζ lam : K)⁻¹)
    {i k : Fin m} (hti : t i = lam) (htk : t k = lam⁻¹)
    (hik : i ≠ k) :
    ∀ a, (((Equiv.swap (Sum.inl i : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl k))
        :
        Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)) *
      (Equiv.swap (Sum.inl k : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (Sum.inr (Sum.inl i)) :
        Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2))) a) ≠
      a → v a = 1 := by
  have hxi : v (Sum.inl i) = 1 := by
    refine (hsupiff _).mpr (Or.inl ?_)
    rw [kOmMWeight_inl, omMinusTorusParam_apply, hti]
  have hxk : v (Sum.inl k) = 1 := by
    refine (hsupiff _).mpr (Or.inr ?_)
    rw [kOmMWeight_inl, omMinusTorusParam_apply, htk] <;> simp [map_inv]
  have hyi : v (Sum.inr (Sum.inl i)) = 1 := by
    refine (hsupiff _).mpr (Or.inr ?_)
    rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, hti] <;> simp [map_inv]
  have hyk : v (Sum.inr (Sum.inl k)) = 1 := by
    refine (hsupiff _).mpr (Or.inl ?_)
    rw [kOmMWeight_inr_inl, omMinusTorusParam_apply, htk] <;> simp [map_inv]
  intro a ha
  rcases a with j | (j | t)
  · by_cases hji : j = i
    · subst j; exact hxi
    · by_cases hjk : j = k
      · subst j; exact hxk
      · exfalso; apply ha; rw [mixedPerm_apply_inl_of_ne i k j hji hjk]
  · by_cases hji : j = i
    · subst j; exact hyi
    · by_cases hjk : j = k
      · subst j; exact hyk
      · exfalso; apply ha; rw [mixedPerm_apply_inr_of_ne i k j hji hjk]
  · exfalso; apply ha; rw [mixedPerm_apply_tail]

private lemma omMinus_split_perm_exists_mem_J
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (lam : Multiplicative (ZMod p)) (hlam : lam ≠ 1)
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
          TableBSymp.zmodPowHom hζ lam ∨
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam)⁻¹)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom))
    {E : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K}
    (hEmem : E ∈ StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))
    (hEE : E * E = 1)
    {σ : Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)}
    (hE : ∀ a, (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) *ᵥ Pi.single a 1 =
      Pi.single (σ a) 1)
    (hw0 : ∀ a, kOmMWeight K m (omMinusTorusParam m hζ t) (σ a) =
      kOmMWeight K m (omMinusTorusParam m hζ t) a)
    (hv1 : ∀ a, σ a ≠ a → v a = 1) :
    ∃ y : ↥J, ((y : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) = E := by
  classical
  let Hc := glBlockCentralizer
    (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
    ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)} :
      Set (GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) ε
  have hblock : (⟨E, hEmem⟩ :
      StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) ∈ Hc :=
    omMinus_split_mem_block_of_perm hζ t ε v hεv hEmem hE hw0 hv1
  let x : ↥Hc := ⟨⟨E, hEmem⟩, hblock⟩
  let σg : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c) ≃*
      StatedOmega (StatedQuadMinus (m + 1) K b c) :=
    MulEquiv.subgroupCongr (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus])
  let y2 : StatedOmega (StatedQuadMinus (m + 1) K b c) := σg.toMonoidHom x
  have hyG : y2 ∈ Hc.map σg.toMonoidHom := Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hx2 : (x : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) *
      (x : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) = 1 := by
    apply Subtype.ext
    exact hEE
  have hyy : y2 * y2 = 1 := by
    change σg.toMonoidHom x * σg.toMonoidHom x = 1
    rw [← map_mul, hx2, map_one]
  have hyJ : y2 ∈ J :=
    omMinus_split_linear_inv_mem hp hp2 hm hirr hζ hζo t lam hlam ε v hε hεv hv hconst hsym
      hsupp hJε y2 hyG hyy
  refine ⟨⟨y2, hyJ⟩, ?_⟩
  have hcoe := MulEquiv.subgroupCongr_apply (by
    rw [CFSG.LieType.Universal.Spin.coe_quadMinus])
    (x : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c))
  calc (((⟨y2, hyJ⟩ : ↥J) : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
        GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)
      = ((σg (x : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) :
          StatedOmega (StatedQuadMinus (m + 1) K b c)) :
          GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) := rfl
    _ = ((x : StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)) :
          GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) := hcoe
    _ = E := rfl

private lemma omMinus_split_perm_comm_diag (hζ : ζ ^ p = 1) (g : Fin m → Multiplicative (ZMod p))
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    {E : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K} {y : ↥J}
    (hyE : ((y : StatedOmega (StatedQuadMinus (m + 1) K b c)) :
      GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) = E)
    (hcent : ∀ j ∈ J,
      omMinusTorus (p := p) b c hζ g * j = j * omMinusTorus (p := p) b c hζ g) :
    (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) *
        Matrix.diagonal (fun a => kOmMWeight K m (omMinusTorusParam m hζ g) a) =
      Matrix.diagonal (fun a => kOmMWeight K m (omMinusTorusParam m hζ g) a) *
        (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
          (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) := by
  have h := congrArg (fun z : StatedOmega (StatedQuadMinus (m + 1) K b c) =>
    (z : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)) (hcent y y.2)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  rw [hyE] at h
  change (omMinusTorusGL hζ g) * E = E * (omMinusTorusGL hζ g) at h
  simpa only [Units.val_mul, omMinusTorusGL_apply, kOmMDiag_coe] using
    (congrArg Units.val h).symm

private theorem omMinus_split_criterion_linear
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (lam : Multiplicative (ZMod p)) (hlam : lam ≠ 1)
    (ε : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K)
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)))
      (Algebra.adjoin K (Units.val ''
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)))) ε)
    (hεv : ε = Matrix.diagonal v)
    (hv : ∀ a, v a = 0 ∨ v a = 1)
    (hconst : ∀ a a',
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        kOmMWeight K m (omMinusTorusParam m hζ t) a' → v a = v a')
    (hsym : ∀ a, v a = v (omMinusSwap m a))
    (hsupp : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
          TableBSymp.zmodPowHom hζ lam ∨
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam)⁻¹)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJε : CFSG.Assembly.IsComponentOf J
      ((glBlockCentralizer
          (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
          ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
            GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
            Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
        (MulEquiv.subgroupCongr (by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom)) :
    ∀ g : Fin m → Multiplicative (ZMod p),
      (∀ j ∈ J,
        omMinusTorus (p := p) b c hζ g * j = j * omMinusTorus (p := p) b c hζ g) ↔
        ∃ d : Multiplicative (ZMod p), ∀ i,
          (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹) := by
  classical
  haveI : NeZero p := ⟨by rw [← hζo]; exact (orderOf_pos ζ).ne'⟩
  have hεne : ε ≠ 0 := hε.2.2.1
  have hGid : (glBlockCentralizer
      (StatedOmega ⇑(CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c)).subtype
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε).map
      (MulEquiv.subgroupCongr (by
        rw [CFSG.LieType.Universal.Spin.coe_quadMinus])).toMonoidHom =
    glBlockCentralizer
      (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype
      ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
        GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
        Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε :=
    glBlockCentralizer_map_subgroupCongr _ ε (by
      rw [CFSG.LieType.Universal.Spin.coe_quadMinus])
  have hsupp' : ∀ a, v a = 1 →
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
          (TableBSymp.zmodPowHom hζ lam : K) ∨
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ := by
    intro a ha
    rcases hsupp a ha with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, Units.val_inv_eq_inv_val])
  have hsupiff : ∀ a, v a = 1 ↔ kOmMWeight K m (omMinusTorusParam m hζ t) a =
      (TableBSymp.zmodPowHom hζ lam : K) ∨
      kOmMWeight K m (omMinusTorusParam m hζ t) a =
        ((TableBSymp.zmodPowHom hζ lam : K))⁻¹ :=
    support_iff hζ hζo t hεv hεne hv hconst hsym hsupp'
  intro g
  constructor
  · intro hcent
    have hlam_ne_inv : lam ≠ lam⁻¹ := by
      intro h
      refine zpow_lam_ne_inv hp hp2 hζ hζo hlam ?_
      conv_lhs => rw [h]
      rw [map_inv, Units.val_inv_eq_inv_val]
    have hA : ∀ i k : Fin m, t i = t k → (t i = lam ∨ t i = lam⁻¹) → g i = g k := by
      intro i k ht hmem
      by_cases hik : i = k
      · rw [hik]
      · let u : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K :=
          Pi.single (Sum.inl i) 1 + Pi.single (Sum.inl k) 1
        let w : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K :=
          Pi.single (Sum.inr (Sum.inl i)) 1 + Pi.single (Sum.inr (Sum.inl k)) 1
        let σ : Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :=
          Equiv.sumCongr (Equiv.swap i k)
            (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2)))
        let E : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K :=
          (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).symm
            (eichler (quadMinus (m+1) K b c) u w)
        have hEmem : E ∈ StatedOmega ⇑(quadMinus (m+1) K b c) := by
          rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
          exact eichler_mem_statedOmega_quadMinus (m := m + 1) (by omega) hirr u w
        have hE : ∀ a, (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
            (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) *ᵥ Pi.single a 1 =
            Pi.single (σ a) 1 := by
          intro a
          funext p
          have h1 : toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K E
              (Pi.single a 1) = eichler (quadMinus (m+1) K b c) u w (Pi.single a 1) := by
            rw [show E = (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).symm
              (eichler (quadMinus (m+1) K b c) u w) from rfl, MulEquiv.apply_symm_apply]
          rw [← toLinEquiv_apply, h1]
          exact congrFun (plane_single_full (b := b) (c := c) (i := i) (k := k) hik a) p
        have hEE : E * E = 1 := by
          rw [show E = (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).symm
              (eichler (quadMinus (m+1) K b c) u w) from rfl, ← map_mul]
          rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.eichler_mul_self_of_two_eq_zero
            (CharTwo.two_eq_zero (R := K)) u w, map_one]
        have hw0 : ∀ a, kOmMWeight K m (omMinusTorusParam m hζ t) (σ a) =
            kOmMWeight K m (omMinusTorusParam m hζ t) a :=
          omMinus_split_plane_weight_invariant hζ t ht
        have hv1 : ∀ a, σ a ≠ a → v a = 1 :=
          omMinus_split_plane_moved_v hζ t hsupiff ht hmem
        obtain ⟨y, hyE⟩ := omMinus_split_perm_exists_mem_J hp hp2 hm hirr hζ hζo t lam
          hlam ε v hε hεv hv hconst hsym hsupp hJε hEmem hEE hE hw0 hv1
        have hcommD := omMinus_split_perm_comm_diag hζ g hyE hcent
        have hw_eq := diag_comm_weight hE hcommD
        have hσi : σ (Sum.inl i) = Sum.inl k := by
          show (Equiv.sumCongr (Equiv.swap i k)
            (Equiv.sumCongr (Equiv.swap i k) (Equiv.refl (Fin 2)))) (Sum.inl i) = Sum.inl k
          rw [planePerm_apply_inl, Equiv.swap_apply_left]
        have h1 : kOmMWeight K m (omMinusTorusParam m hζ g) (Sum.inl k) =
            kOmMWeight K m (omMinusTorusParam m hζ g) (Sum.inl i) := by
          have h := hw_eq (Sum.inl i)
          rwa [hσi] at h
        have h2 : ((TableBSymp.zmodPowHom hζ (g k) : Kˣ) : K) =
            ((TableBSymp.zmodPowHom hζ (g i) : Kˣ) : K) := by
          simpa only [kOmMWeight_inl, omMinusTorusParam_apply] using h1
        exact ((zpow_eq_iff hζ hζo (a := g k) (b := g i)).mp h2).symm
    have hB : ∀ i k : Fin m, t i = lam → t k = lam⁻¹ → g i = (g k)⁻¹ := by
      intro i k hti htk
      have hik : i ≠ k := by
        rintro rfl
        exact hlam_ne_inv (hti.symm.trans htk)
      let u : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K :=
        Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr (Sum.inl k)) 1
      let w : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K :=
        Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr (Sum.inl i)) 1
      let σ : Equiv.Perm (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :=
        (Equiv.swap (Sum.inl i) (Sum.inr (Sum.inl k))) *
          (Equiv.swap (Sum.inl k) (Sum.inr (Sum.inl i)))
      let E : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K :=
        (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).symm
          (eichler (quadMinus (m+1) K b c) u w)
      have hEmem : E ∈ StatedOmega ⇑(quadMinus (m+1) K b c) := by
        rw [CFSG.LieType.Universal.Spin.coe_quadMinus]
        exact eichler_mem_statedOmega_quadMinus (m := m + 1) (by omega) hirr u w
      have hE : ∀ a, (E : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
          (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) *ᵥ Pi.single a 1 =
          Pi.single (σ a) 1 := by
        intro a
        funext p
        have h1 : toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K E
            (Pi.single a 1) = eichler (quadMinus (m+1) K b c) u w (Pi.single a 1) := by
          rw [show E = (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).symm
            (eichler (quadMinus (m+1) K b c) u w) from rfl, MulEquiv.apply_symm_apply]
        rw [← toLinEquiv_apply, h1]
        exact congrFun (mixed_single_full (b := b) (c := c) (i := i) (k := k) hik a) p
      have hEE : E * E = 1 := by
        rw [show E = (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K).symm
            (eichler (quadMinus (m+1) K b c) u w) from rfl, ← map_mul]
        rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.eichler_mul_self_of_two_eq_zero
          (CharTwo.two_eq_zero (R := K)) u w, map_one]
      have hw0 : ∀ a, kOmMWeight K m (omMinusTorusParam m hζ t) (σ a) =
          kOmMWeight K m (omMinusTorusParam m hζ t) a :=
        omMinus_split_mixed_weight_invariant hζ t hti htk hik
      have hv1 : ∀ a, σ a ≠ a → v a = 1 :=
        omMinus_split_mixed_moved_v hζ t hsupiff hti htk hik
      obtain ⟨y, hyE⟩ := omMinus_split_perm_exists_mem_J hp hp2 hm hirr hζ hζo t lam
        hlam ε v hε hεv hv hconst hsym hsupp hJε hEmem hEE hE hw0 hv1
      have hcommD := omMinus_split_perm_comm_diag hζ g hyE hcent
      have hw_eq := diag_comm_weight hE hcommD
      have hσi : σ (Sum.inl i) = Sum.inr (Sum.inl k) := mixedPerm_apply_inl_self i k hik
      have h1 : kOmMWeight K m (omMinusTorusParam m hζ g) (Sum.inr (Sum.inl k)) =
          kOmMWeight K m (omMinusTorusParam m hζ g) (Sum.inl i) := by
        have h := hw_eq (Sum.inl i)
        rwa [hσi] at h
      have h2 : (((TableBSymp.zmodPowHom hζ (g k) : Kˣ) : K))⁻¹ =
          ((TableBSymp.zmodPowHom hζ (g i) : Kˣ) : K) := by
        simpa only [kOmMWeight_inr_inl, kOmMWeight_inl, omMinusTorusParam_apply,
          Units.val_inv_eq_inv_val] using h1
      exact (zpow_eq_inv_iff hζ hζo (a := g i) (b := g k)).mp h2.symm
    by_cases hL : ∃ i, t i = lam
    · obtain ⟨i₀, hi₀⟩ := hL
      refine ⟨g i₀, fun i => ⟨?_, ?_⟩⟩
      · intro hi
        exact hA i i₀ (hi.trans hi₀.symm) (Or.inl hi)
      · intro hi
        simpa using (congrArg (fun z => z⁻¹) (hB i₀ i hi₀ hi)).symm
    · by_cases hL' : ∃ k, t k = lam⁻¹
      · obtain ⟨k₀, hk₀⟩ := hL'
        refine ⟨(g k₀)⁻¹, fun i => ⟨?_, ?_⟩⟩
        · intro hi
          exact hB i k₀ hi hk₀
        · intro hi
          simpa using hA i k₀ (hi.trans hk₀.symm) (Or.inr hi)
      · refine ⟨1, fun i => ⟨?_, ?_⟩⟩
        · intro hi
          exact absurd ⟨i, hi⟩ hL
        · intro hi
          exact absurd ⟨i, hi⟩ hL'
  · rintro ⟨d, hd⟩ j hj
    have hj' : j ∈ glBlockCentralizer
        (StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype
        ({(kOmMDiag K m (omMinusTorusParam m hζ t) :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K)} :
          Set (GL (Fin m ⊕ Fin m ⊕ Fin 2) K)) ε := by
      rw [← hGid]
      exact hJε.1 hj
    have hjmem := Subgroup.mem_comap.mp hj'
    have hjcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hjmem).1
    let jm : GL (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K := j
    have hjfix' : (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
        (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v := by
      have h : ((StatedOmega (StatedQuadMinus (m + 1) K b c)).subtype j :
          GL (Fin m ⊕ Fin m ⊕ Fin 2) K) ∈ glFixing (1 - ε) :=
        (Subgroup.mem_inf.mp hjmem).2
      rw [hεv] at h
      exact h
    have hjcommM : (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
        (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
        (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
          (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) := by
      have h := congrArg Units.val hjcomm
      change (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
          (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) =
        (Units.val (kOmMDiag K m (omMinusTorusParam m hζ t)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) *
          (Units.val jm : Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) K) at h
      exact h
    rw [kOmMDiag_coe] at hjcommM
    have hx : ∀ a b, v a = 1 → v b = 1 →
        kOmMWeight K m (omMinusTorusParam m hζ t) a =
          kOmMWeight K m (omMinusTorusParam m hζ t) b →
        kOmMWeight K m (omMinusTorusParam m hζ g) a =
          kOmMWeight K m (omMinusTorusParam m hζ g) b :=
      fun a b ha hb hw => hx_of_coord hζ hζo t g hlam d hd hsupiff hp hp2 ha hb hw
    have hmat := ggTBJSpB_diagonal_mul_eq_mul_of_block v
      (fun a => kOmMWeight K m (omMinusTorusParam m hζ t) a)
      (fun a => kOmMWeight K m (omMinusTorusParam m hζ g) a)
      (Units.val jm) hv hjfix' hjcommM hconst hx
    refine Subtype.ext (Units.ext ?_)
    change (omMinusTorusGL hζ g : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K) * (Units.val jm) =
      (Units.val jm) * (omMinusTorusGL hζ g : Matrix (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
        (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) K)
    rw [omMinusTorusGL_apply, kOmMDiag_coe]
    exact hmat

end OmMinusSplitLinearAux


private theorem ggCommonJOmMinusSplit_component_block (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({omMinusTorus (p := p) b c hζ t} : Set
        (StatedOmega (StatedQuadMinus (m + 1) K b c))))) :
    ∃ lam : Multiplicative (ZMod p),
      ((lam = 1 ∧ 1 ≤ Nat.card {i : Fin m // t i = 1} ∧
          Nonempty (↥J ≃*
            StatedOmega (StatedQuadMinus (Nat.card {i : Fin m // t i = 1} + 1) K b c))) ∨
        (lam ≠ 1 ∧ 2 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} ∧
          Nonempty (↥J ≃* Matrix.SpecialLinearGroup
            (Fin (Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹})) K))) ∧
      ∀ g : Fin m → Multiplicative (ZMod p),
        (∀ j ∈ J, omMinusTorus (p := p) b c hζ g * j = j * omMinusTorus (p := p) b c hζ g) ↔
          ((lam = 1 ∧ ∀ i, t i = 1 → g i = 1) ∨
            (lam ≠ 1 ∧ ∃ d : Multiplicative (ZMod p), ∀ i,
              (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hpqK : p ∣ Nat.card K - 1 := by
    rw [← hζo, ← Nat.card_units]
    exact orderOf_dvd_natCard ζ
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hK2 : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hK4 : 4 ≤ Nat.card K := by
    have hpos : 0 < Nat.card K - 1 := by omega
    have hle : p ≤ Nat.card K - 1 := Nat.le_of_dvd hpos hpqK
    omega
  let Φ : QuadraticForm K (Fin m ⊕ Fin m ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus (m + 1) K b c
  have hnd : (QuadraticMap.polarBilin Φ).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr
  have hb : b ≠ 0 := by
    intro hb0
    have hsingle : (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) (1 : K) :
        Fin m ⊕ Fin m ⊕ Fin 2 → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inr (Sum.inr (0 : Fin 2)))
      simpa using this
    apply hsingle
    apply hnd.1
    intro x
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero (n := m + 1)]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [h2, hb0]
    simp
  have h8 : 8 ≤ Fintype.card (Fin m ⊕ Fin m ⊕ Fin 2) := by
    have hc : Fintype.card (Fin m ⊕ Fin m ⊕ Fin 2) = 2 * m + 2 := by
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
      ring
    omega
  let u : Fin m → Kˣ := omMinusTorusParam m hζ t
  obtain ⟨ε, hε, hJε⟩ :=
    omMinus_split_exists_idempotent hp hp2 hm hirr hζ hζo t hJ
  obtain ⟨v, hεv, hv, hconst, hsym, lam0, hlam0ne, hsupp0⟩ :=
    exists_diagonal_of_isPrimAdjIdemIn_omMinus u hnd hb hε
  have hvne : ∃ a, v a = 1 := by
    by_contra h
    apply hε.2.2.1
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  obtain ⟨a₀, ha₀⟩ := hvne
  have hweight_inl : ∀ i : Fin m,
      kOmMWeight K m u (Sum.inl i) = (TableBSymp.zmodPowHom hζ (t i) : K) := by
    intro i
    rfl
  have hweight_inr : ∀ i : Fin m,
      kOmMWeight K m u (Sum.inr (Sum.inl i)) =
        (TableBSymp.zmodPowHom hζ ((t i)⁻¹) : K) := by
    intro i
    change (((u i)⁻¹ : Kˣ) : K) = (TableBSymp.zmodPowHom hζ ((t i)⁻¹) : K)
    rw [map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, inv_inj]
    exact congrArg Units.val (omMinusTorusParam_apply hζ t i)
  have hweight_tail : ∀ j : Fin 2, kOmMWeight K m u (Sum.inr (Sum.inr j)) = 1 :=
    fun _ => rfl
  obtain ⟨lam, hlam_eq⟩ : ∃ lam : Multiplicative (ZMod p),
      TableBSymp.zmodPowHom hζ lam = lam0 := by
    rcases a₀ with i | (i | j)
    · rcases hsupp0 (Sum.inl i) ha₀ with h | h
      · exact ⟨t i, by rw [← hweight_inl i]; exact h⟩
      · refine ⟨(t i)⁻¹, ?_⟩
        rw [map_inv, Units.val_inv_eq_inv_val, ← hweight_inl i, h, inv_inv]
    · rcases hsupp0 (Sum.inr (Sum.inl i)) ha₀ with h | h
      · exact ⟨(t i)⁻¹, by rw [← hweight_inr i]; exact h⟩
      · refine ⟨t i, ?_⟩
        have h' : (↑(TableBSymp.zmodPowHom hζ (t i)) : K)⁻¹ = lam0⁻¹ := by
          rw [← Units.val_inv_eq_inv_val, ← map_inv, ← hweight_inr i]
          exact h
        exact inv_inj.mp h'
    · refine ⟨1, ?_⟩
      rw [map_one, Units.val_one]
      have hw : kOmMWeight K m u (Sum.inr (Sum.inr j)) = 1 := hweight_tail j
      rcases hsupp0 (Sum.inr (Sum.inr j)) ha₀ with h | h
      · rw [hw] at h
        exact h
      · rw [hw] at h
        exact (inv_eq_one.mp h.symm).symm
  by_cases hlam0_one : lam0 = 1
  · have hfix : ∀ a, v a = 1 → kOmMWeight K m u a = 1 := by
      intro a ha
      rcases hsupp0 a ha with h | h
      · rw [h, hlam0_one]
      · rw [h, hlam0_one, inv_one]
    obtain ⟨hn1, hiso⟩ :=
      omMinus_split_fixed_block hp hp2 hm hirr hζ hζo t ε v hε hεv hv hconst hsym hfix hJε
    refine ⟨1, Or.inl ⟨rfl, hn1, hiso⟩, ?_⟩
    intro g
    simpa using
      omMinus_split_criterion_fixed hp hp2 hm hirr hζ hζo t ε v hε hεv hv hconst hsym hfix hJε g
  · have hlam_ne : lam ≠ 1 := by
      intro h1
      exact hlam0_one (by rw [← hlam_eq, h1, map_one]; rfl)
    have hsupp : ∀ a, v a = 1 →
        kOmMWeight K m u a = TableBSymp.zmodPowHom hζ lam ∨
          kOmMWeight K m u a = (TableBSymp.zmodPowHom hζ lam)⁻¹ := by
      intro a ha
      rcases hsupp0 a ha with h | h
      · refine Or.inl ?_
        calc kOmMWeight K m u a = lam0 := h
          _ = (TableBSymp.zmodPowHom hζ lam : K) := hlam_eq.symm
      · refine Or.inr ?_
        calc kOmMWeight K m u a = lam0⁻¹ := h
          _ = (TableBSymp.zmodPowHom hζ lam)⁻¹ := by
            rw [Units.val_inv_eq_inv_val, hlam_eq]
    obtain ⟨hmlam, hiso⟩ :=
      omMinus_split_linear_block hp hp2 hm hirr hζ hζo t lam hlam_ne ε v hε hεv hv hconst hsym
        hsupp hJε
    refine ⟨lam, Or.inr ⟨hlam_ne, hmlam, hiso⟩, ?_⟩
    intro g
    simpa [hlam_ne] using
      omMinus_split_criterion_linear hp hp2 hm hirr hζ hζo t lam hlam_ne ε v hε hεv hv hconst
        hsym hsupp hJε g

private lemma ggCommonJOmMinusSplit_count_aux (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (t : Fin m → Multiplicative (ZMod p))
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    {lam : Multiplicative (ZMod p)}
    (hfix : ∀ g : Fin m → Multiplicative (ZMod p),
      (∀ j ∈ J, omMinusTorus (p := p) b c hζ g * j = j * omMinusTorus (p := p) b c hζ g) ↔
        ((lam = 1 ∧ ∀ i, t i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ d : Multiplicative (ZMod p), ∀ i,
            (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))))
    (hm : lam ≠ 1 → 1 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹}) :
    Nat.card ↥((omMinusTorus (p := p) b c hζ).range ⊓
        Subgroup.centralizer (J : Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))) =
      if lam = 1 then p ^ (m - Nat.card {i : Fin m // t i = 1})
      else p ^ (m - Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} + 1) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let Ω := StatedOmega (StatedQuadMinus (m + 1) K b c)
  let C : Subgroup Ω := Subgroup.centralizer (J : Set Ω)
  let τ : (Fin m → Multiplicative (ZMod p)) →* Ω := omMinusTorus (p := p) b c hζ
  have hτ : Function.Injective τ :=
    ggCommonJOmMinusSplit_torus_injective (p := p) (m := m) (b := b) (c := c) hζ hζo
  change Nat.card ↥(τ.range ⊓ C) =
    if lam = 1 then p ^ (m - Nat.card {i : Fin m // t i = 1})
    else p ^ (m - Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} + 1)
  have hfixτ : ∀ g : Fin m → Multiplicative (ZMod p), τ g ∈ C ↔
        ((lam = 1 ∧ ∀ i, t i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ d : Multiplicative (ZMod p), ∀ i,
            (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))) := by
    intro g
    rw [show C = Subgroup.centralizer (J : Set Ω) from rfl]
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact (hfix g).mp fun j hj => (h j hj).symm
    · intro h j hj
      exact ((hfix g).mpr h j hj).symm
  have hcard : Nat.card ↥(τ.range ⊓ C) =
      Nat.card {g : Fin m → Multiplicative (ZMod p) // τ g ∈ C} := by
    rw [← Subgroup.map_comap_eq (f := τ) (H := C)]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.comap τ C) τ hτ).toEquiv).symm
  rw [hcard, Nat.card_congr (Equiv.subtypeEquivRight hfixτ)]
  by_cases hlam : lam = 1
  · rw [if_pos hlam]
    have hiff : ∀ g : Fin m → Multiplicative (ZMod p),
        ((lam = 1 ∧ ∀ i, t i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ d : Multiplicative (ZMod p), ∀ i,
            (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))) ↔
        (∀ i, t i = 1 → g i = 1) := by
      intro g
      rw [hlam]
      simp
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    let S : Finset (Fin m) := Finset.univ.filter (fun i => t i = 1)
    have hSet : Nat.card {g : Fin m → Multiplicative (ZMod p) // ∀ i, t i = 1 → g i = 1} =
        Nat.card {g : Fin m → Multiplicative (ZMod p) // ∀ i ∈ S, g i = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [S])
    rw [hSet, FrameBs.card_frame_trivial_on S]
    have hScard : S.card = Nat.card {i : Fin m // t i = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hScard]
  · rw [if_neg hlam]
    have hne_inv : lam ≠ lam⁻¹ := by
      intro h
      apply hlam
      haveI : Fact p.Prime := ⟨hp⟩
      have hx : Multiplicative.toAdd lam = -Multiplicative.toAdd lam := by
        calc Multiplicative.toAdd lam = Multiplicative.toAdd lam⁻¹ := congrArg _ h
          _ = -Multiplicative.toAdd lam := toAdd_inv lam
      have h2x : (2 : ZMod p) * Multiplicative.toAdd lam = 0 := by
        rw [two_mul]
        exact eq_neg_iff_add_eq_zero.mp hx
      have h2z : (2 : ZMod p) ≠ 0 := by
        intro h2
        have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
        · exact hp.ne_one h1
        · exact hp2 h1
      have hx0 : Multiplicative.toAdd lam = 0 := (mul_eq_zero.mp h2x).resolve_left h2z
      have h1 : Multiplicative.ofAdd (Multiplicative.toAdd lam) = 1 := by
        rw [hx0]
        rfl
      simpa using h1
    have hdisj : ∀ i, t i = lam → t i = lam⁻¹ → False := fun i h1 h2 =>
      hne_inv (h1.symm.trans h2)
    have hne : ∃ i, t i = lam ∨ t i = lam⁻¹ := by
      have hpos : 0 < Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
        have := hm hlam
        omega
      obtain ⟨i, hi⟩ := (Nat.card_pos_iff.mp hpos).1
      exact ⟨i, hi⟩
    have hiff : ∀ g : Fin m → Multiplicative (ZMod p),
        ((lam = 1 ∧ ∀ i, t i = 1 → g i = 1) ∨
          (lam ≠ 1 ∧ ∃ d : Multiplicative (ZMod p), ∀ i,
            (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹))) ↔
        (∃ d : Multiplicative (ZMod p), ∀ i,
          (t i = lam → g i = d) ∧ (t i = lam⁻¹ → g i = d⁻¹)) := by
      intro g
      constructor
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 hlam
        · exact h2
      · intro h
        exact Or.inr ⟨hlam, h⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [CommonJ.card_scalar_param (p := p) (r := m) (P := fun i => t i = lam)
      (Q := fun i => t i = lam⁻¹) hdisj hne]
    rw [mul_comm, ← pow_succ]

theorem ggCommonJOmMinusSplit_component_count (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p)
    (t : Fin m → Multiplicative (ZMod p))
    (J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c)))
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({omMinusTorus (p := p) b c hζ t} : Set
        (StatedOmega (StatedQuadMinus (m + 1) K b c))))) :
    ∃ (a : ZMod p) (P : Finset (Fin m)),
      (∀ i ∈ P, toAdd (t i) = a ∨ toAdd (t i) = -a) ∧
      (∀ u : Fin m → Multiplicative (ZMod p),
        (∃ r : ZMod p, ∀ i ∈ P, toAdd (u i) = r * toAdd (t i)) →
        ∀ j ∈ J, omMinusTorus (p := p) b c hζ u * j = j * omMinusTorus (p := p) b c hζ u) ∧
      (t = 1 → P = Finset.univ ∧ a = 0) ∧
      Nat.card ↥((omMinusTorus (p := p) b c hζ).range ⊓
        Subgroup.centralizer (J : Set (StatedOmega (StatedQuadMinus (m + 1) K b c)))) =
        p ^ (m - P.card + (if a = 0 then 0 else 1)) := by
  classical
  obtain ⟨lam, hblock, hfix⟩ :=
    ggCommonJOmMinusSplit_component_block hp hp2 hm hirr hζ hζo t hJ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm' : lam ≠ 1 → 1 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
    intro hne
    rcases hblock with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
    · exact absurd h1 hne
    · omega
  have hcount := ggCommonJOmMinusSplit_count_aux (p := p) (m := m) (b := b) (c := c)
    hp hp2 hζ hζo t hfix hm'
  by_cases hlam : lam = 1
  · refine ⟨0, Finset.univ.filter (fun i => t i = 1), ?_, ?_, ?_, ?_⟩
    · intro i hi
      left
      rw [Finset.mem_filter] at hi
      rw [hi.2]
      simp
    · intro u hu
      obtain ⟨r, hr⟩ := hu
      refine (hfix u).mpr (Or.inl ⟨hlam, fun i hi => ?_⟩)
      have hui : toAdd (u i) = 0 := by
        simpa [hi] using hr i (by simp [hi])
      simpa using congrArg Multiplicative.ofAdd hui
    · intro ht
      refine ⟨?_, rfl⟩
      ext i
      simp [ht]
    · rw [if_pos hlam] at hcount
      rw [hcount]
      have hP : (Finset.univ.filter (fun i => t i = 1)).card =
          Nat.card {i : Fin m // t i = 1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hP]
      simp
  · have hnlam : 2 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
      rcases hblock with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
      · exact absurd h1 hlam
      · exact h2
    have ha0 : ¬ toAdd lam = 0 := by
      intro h
      apply hlam
      simpa using congrArg Multiplicative.ofAdd h
    refine ⟨toAdd lam, Finset.univ.filter (fun i => t i = lam ∨ t i = lam⁻¹),
      ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_filter] at hi
      rcases hi.2 with h | h
      · left
        rw [h]
      · right
        rw [h, toAdd_inv]
    · intro u hu
      obtain ⟨r, hr⟩ := hu
      let d : Multiplicative (ZMod p) := Multiplicative.ofAdd (r * toAdd lam)
      refine (hfix u).mpr (Or.inr ⟨hlam, d, fun i => ?_⟩)
      constructor
      · intro hi
        apply Multiplicative.toAdd.injective
        have hu' := hr i (by simp [hi])
        rw [hi] at hu'
        simpa [d] using hu'
      · intro hi
        apply Multiplicative.toAdd.injective
        have hu' := hr i (by simp [hi])
        rw [hi] at hu'
        have hd : toAdd d = r * toAdd lam := by simp [d]
        rw [toAdd_inv, hd]
        calc toAdd (u i) = r * toAdd (lam⁻¹) := hu'
          _ = r * (-toAdd lam) := by rw [toAdd_inv]
          _ = -(r * toAdd lam) := by rw [mul_neg]
    · intro ht
      exfalso
      have hpos : 0 < Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by omega
      obtain ⟨i, hi⟩ := (Nat.card_pos_iff.mp hpos).1
      have hti : t i = 1 := by simpa using congrFun ht i
      rcases hi with h | h
      · exact hlam (hti.symm.trans h).symm
      · have h1 : (1 : Multiplicative (ZMod p)) = lam⁻¹ := hti.symm.trans h
        exact hlam (by simpa using h1.symm)
    · rw [if_neg hlam] at hcount
      rw [hcount]
      have hP : (Finset.univ.filter (fun i => t i = lam ∨ t i = lam⁻¹)).card =
          Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hP, if_neg ha0]

private theorem ggCommonJOmMinusSplit_label_of_four
    (hK : Nat.card K = 2 ^ f) {r : ℕ} (hr : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {J : Type} [Group J] (e : J ≃* StatedOmega (StatedQuadMinus r K b c)) :
    GGHasLabel ⟨.twD, r, f⟩ (J ⧸ Subgroup.center J) := by
  have hZ : Subgroup.center (StatedOmega (StatedQuadMinus r K b c)) = ⊥ :=
    center_statedOmega_quadMinus_eq_bot hr hirr
  have hq : J ⧸ Subgroup.center J ≃*
      ↥(StatedOmega (StatedQuadMinus r K b c)) ⧸
        Subgroup.center ↥(StatedOmega (StatedQuadMinus r K b c)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hr' : OrthRest.RMinus K (r - 1) b c ≃* StatedOmega (StatedQuadMinus r K b c) := by
    have h := rMinusEquivStatedOmega K (r - 1) b c
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum]
  rw [if_neg (by omega : ¬ r = 2), if_neg (by omega : ¬ r = 3)]
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hirr, ?_⟩
  exact ⟨(hq.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot)).trans hr'.symm⟩

private theorem ggCommonJOmMinusSplit_label_of_three
    (hK : Nat.card K = 2 ^ f) {r : ℕ} (hr : r = 3)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {J : Type} [Group J] (e : J ≃* StatedOmega (StatedQuadMinus r K b c)) :
    GGHasLabel ⟨.twD, r, f⟩ (J ⧸ Subgroup.center J) := by
  subst r
  have hf1 : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hK
    have h1 := Finite.one_lt_card (α := K)
    omega
  obtain ⟨F, hFld, hFin, hFcard, ⟨eU⟩⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_three_mulEquiv
      (K := K) (b := b) (c := c) hK hirr
  letI : Field F := hFld
  letI : Finite F := hFin
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, hf1, by rw [hFcard, (pow_mul 2 f 2).symm, Nat.mul_comm f 2]⟩
  let ec : J ≃* ↥(StatedSU 4 (2 ^ f) F) := e.trans eU
  let eZ : J ⧸ Subgroup.center J ≃*
      ↥(StatedSU 4 (2 ^ f) F) ⧸ Subgroup.center ↥(StatedSU 4 (2 ^ f) F) :=
    QuotientGroup.congr _ _ ec (Subgroup.map_center_eq ec)
  have hproj : ↥(StatedSU 4 (2 ^ f) F) ⧸
      Subgroup.center ↥(StatedSU 4 (2 ^ f) F) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 4) F (2 ^ f)) :=
    largeEvenSUQuotEquivProj (m := 4) (k := f) hUFD (by norm_num) (by omega)
  change ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
    Nat.card K' = (2 ^ f) ^ 2 ∧
      Nonempty ((J ⧸ Subgroup.center J) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 4) K' (2 ^ f)))
  exact ⟨F, inferInstance, inferInstance, hFcard, ⟨eZ.trans hproj⟩⟩

theorem ggCommonJOmMinusSplit_sparse_label (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ f) (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) {t : Fin m → Multiplicative (ZMod p)}
    (ht : GGCoordSparse t) (ht1 : t ≠ 1)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({omMinusTorus (p := p) b c hζ t} : Set
        (StatedOmega (StatedQuadMinus (m + 1) K b c))))) :
    GGHasLabel ⟨.twD, m, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨i₀, hi₀⟩ := ht
  have hti₀ : t i₀ ≠ 1 := by
    intro h
    apply ht1
    funext j
    by_cases hj : j = i₀
    · rw [hj]; simpa using h
    · simpa using hi₀ j hj
  have hcard1 : Nat.card {i : Fin m // t i = 1} = m - 1 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (p := fun i => t i = 1) (Finset.univ.erase i₀) (fun i => ?_),
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hne; exact hi₀ i hne
    · intro hi h; rw [h] at hi; exact hti₀ hi
  obtain ⟨lam, hblock, -⟩ :=
    ggCommonJOmMinusSplit_component_block hp hp2 hm hirr hζ hζo t hJ
  rcases hblock with ⟨rfl, -, ⟨e⟩⟩ | ⟨hlamne, hm2, -⟩
  · have hsub : Nat.card {i : Fin m // t i = 1} + 1 = m := by omega
    have hlab : (⟨.twD, Nat.card {i : Fin m // t i = 1} + 1, f⟩ : LargeEvenLabel) =
        ⟨.twD, m, f⟩ := by
      rw [hsub]
    by_cases hm4 : 4 ≤ m
    · have h4 : 4 ≤ Nat.card {i : Fin m // t i = 1} + 1 := by omega
      have h := ggCommonJOmMinusSplit_label_of_four hK h4 hirr e
      rwa [hlab] at h
    · have h3 : Nat.card {i : Fin m // t i = 1} + 1 = 3 := by omega
      have h := ggCommonJOmMinusSplit_label_of_three hK h3 hirr e
      rwa [hlab] at h
  · exfalso
    have hle : Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} ≤ 1 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_of_subtype (p := fun i => t i = lam ∨ t i = lam⁻¹)
          (Finset.univ.filter fun i => t i = lam ∨ t i = lam⁻¹) (fun i => by simp),
        Finset.card_le_one]
      intro a ha b hb
      have key : ∀ x ∈ Finset.univ.filter (fun i : Fin m => t i = lam ∨ t i = lam⁻¹),
          (x : Fin m) = i₀ := by
        intro x hx
        have hx' : t x = lam ∨ t x = lam⁻¹ := (Finset.mem_filter.mp hx).2
        by_contra h
        have h1 : t x = 1 := hi₀ x h
        rcases hx' with h' | h'
        · exact hlamne (h' ▸ h1)
        · exact hlamne (inv_eq_one.mp (h' ▸ h1))
      exact (key a ha).trans (key b hb).symm
    omega

theorem ggCommonJOmMinusSplit_dense_label (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = 2 ^ f) (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) {t : Fin m → Multiplicative (ZMod p)}
    (ht : GGCoordDense t)
    {J : Subgroup (StatedOmega (StatedQuadMinus (m + 1) K b c))}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({omMinusTorus (p := p) b c hζ t} : Set
        (StatedOmega (StatedQuadMinus (m + 1) K b c))))) :
    GGHasLabel ⟨.A, m - 1, f⟩ (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨lam, hblock, -⟩ :=
    ggCommonJOmMinusSplit_component_block hp hp2 hm hirr hζ hζo t hJ
  have htne : ∀ i : Fin m, t i ≠ 1 := fun i => (ht i).1
  have hcase : lam ≠ 1 ∧
      2 ≤ Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} ∧
        Nonempty (↥J ≃* Matrix.SpecialLinearGroup
          (Fin (Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹})) K) := by
    rcases hblock with ⟨rfl, hn1, -⟩ | h
    · exfalso
      haveI : IsEmpty {i : Fin m // t i = (1 : Multiplicative (ZMod p))} :=
        ⟨fun x => htne x.1 x.2⟩
      have h0 : Nat.card {i : Fin m // t i = (1 : Multiplicative (ZMod p))} = 0 :=
        Nat.card_of_isEmpty
      rw [h0] at hn1
      omega
    · exact h
  obtain ⟨hlamne, hm2, ⟨e⟩⟩ := hcase
  obtain ⟨j, hj⟩ : ∃ j : Fin m, t j = lam ∨ t j = lam⁻¹ := by
    by_contra h
    push Not at h
    haveI : IsEmpty {i : Fin m // t i = lam ∨ t i = lam⁻¹} :=
      ⟨fun x => by
        rcases x.2 with h' | h'
        · exact (h x.1).1 h'
        · exact (h x.1).2 h'⟩
    have h0 : Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} = 0 := Nat.card_of_isEmpty
    omega
  have hall : ∀ i : Fin m, t i = lam ∨ t i = lam⁻¹ := by
    intro i
    rcases hj with hj | hj
    · rw [← hj]
      exact (ht j).2 i
    · have hlam : lam = (t j)⁻¹ := by rw [hj, inv_inv]
      rw [hlam, inv_inv]
      rcases (ht j).2 i with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
  have hcard : Nat.card {i : Fin m // t i = lam ∨ t i = lam⁻¹} = m := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_fin]
  rw [hcard] at e
  exact ggHasLabel_of_mulEquiv_specialLinear (k := m) (f := f) (by omega) hK
    (fun h => absurd (congrArg Prod.fst h) (by omega))
    (fun h => absurd (congrArg Prod.fst h) (by omega)) e.symm

end CFSG.StandardType

end

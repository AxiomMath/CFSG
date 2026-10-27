module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

private theorem lemma119_innSet_gen {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι K)) (S : Set (GL ι K)) (hS : ∀ h ∈ H, h ∈ S) :
    LargeEvenInnSet (LargeEvenProj H) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S := by
  rintro _ ⟨r, rfl⟩
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective r
  refine ⟨(h₀ : GL ι K), hS _ h₀.2, fun h h' hh' => ?_⟩
  show (h₀ : LargeEvenProj H) * (h : LargeEvenProj H) * (h₀ : LargeEvenProj H)⁻¹ =
    (h' : LargeEvenProj H)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (by rw [hh']; rfl)

private theorem lemma119_sp_form {K : Type} [Field K] {m : ℕ} {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ LargeEvenSpGroup K m) :
    Matrix.transpose (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * LargeEvenSpForm K m *
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = LargeEvenSpForm K m := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => simp
  | mul x y _ _ hx hy =>
    calc Matrix.transpose ((x * y : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
          ((x * y : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)
        = Matrix.transpose (y : Matrix _ _ K) *
            (Matrix.transpose (x : Matrix _ _ K) * LargeEvenSpForm K m * (x : Matrix _ _ K)) *
              (y : Matrix _ _ K) := by
          rw [Units.val_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [hx, hy]
  | inv x _ hx =>
    have h1 : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Matrix.transpose ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
          ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)
        = Matrix.transpose ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *
            (Matrix.transpose (x : Matrix _ _ K) * LargeEvenSpForm K m * (x : Matrix _ _ K)) *
              ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) := by rw [hx]
      _ = Matrix.transpose ((x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)) *
            LargeEvenSpForm K m *
              ((x : Matrix _ _ K) * ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = LargeEvenSpForm K m := by rw [h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

private theorem lemma119_innSet_sp {K : Type} [Field K] {m : ℕ}
    (H : Subgroup (GL (Fin m ⊕ Fin m) K)) (hH : H ≤ LargeEvenSpGroup K m) :
    LargeEvenInnSet (LargeEvenProj H) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGSpSet K m) :=
  lemma119_innSet_gen H _ (fun h hh => ⟨1, one_ne_zero, by
    rw [one_smul]; exact lemma119_sp_form (hH hh)⟩)

private theorem lemma119_su_mem_gu {K : Type} [Field K] [CharP K 2] {d n : ℕ}
    {g : GL (Fin d) K} (hg : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    g ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  have hmap : ∀ M : Matrix (Fin d) (Fin d) K,
      M.map (fun x => x ^ 2 ^ n) = M.map (iterateFrobenius K 2 n) := fun M => rfl
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, hid⟩ := hx
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    rw [one_smul]
    exact hid
  | one =>
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    simp
  | mul x y _ _ hx hy =>
    obtain ⟨μx, hμx0, hμx1, hμx⟩ := hx
    obtain ⟨μy, hμy0, hμy1, hμy⟩ := hy
    refine ⟨μx * μy, mul_ne_zero hμx0 hμy0, by rw [mul_pow, hμx1, hμy1], ?_⟩
    rw [hmap] at hμx hμy ⊢
    simp only [Units.val_mul]
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          (Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((x : Matrix (Fin d) (Fin d) K) * (y : Matrix (Fin d) (Fin d) K))
        = (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
            (x : Matrix (Fin d) (Fin d) K)) * (y : Matrix (Fin d) (Fin d) K) := by
          simp only [Matrix.mul_assoc]
      _ = (μx * μy) • (1 : Matrix (Fin d) (Fin d) K) := by
          rw [hμx, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hμy, smul_smul]
  | inv x _ hx =>
    obtain ⟨μ, hμ0, hμ1, hX⟩ := hx
    rw [hmap] at hX
    have hXZ : (x : Matrix (Fin d) (Fin d) K) *
        ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hXfZf : Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n) *
        Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          (iterateFrobenius K 2 n) = 1 := by
      rw [← Matrix.map_mul, hXZ, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = 1 := by
      rw [← Matrix.transpose_mul, hXfZf, Matrix.transpose_one]
    have h2 : μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = (x : Matrix (Fin d) (Fin d) K) := by
      calc μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose
          = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (μ • (1 : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * ((Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (x : Matrix (Fin d) (Fin d) K)) := by rw [hX]
        _ = ((Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose) * (x : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc]
        _ = (x : Matrix (Fin d) (Fin d) K) := by rw [h1, Matrix.one_mul]
    have h3 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = μ⁻¹ • (x : Matrix (Fin d) (Fin d) K) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμ1], ?_⟩
    rw [hmap]
    rw [h3, Matrix.smul_mul, hXZ]

private theorem lemma119_charP_two {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = (2 ^ n) ^ 2) : CharP K 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hc⟩ := CharP.exists K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have hcard : Fintype.card K = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, h, ← pow_mul, mul_comm]
  have hdvd : p ∣ 2 ^ (2 * n) := by
    rw [← hcard, hk]
    exact dvd_pow_self p (PNat.ne_zero k)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc

private theorem lemma119_innSet_su {K : Type} [Field K] [CharP K 2] {d n : ℕ}
    (H : Subgroup (GL (Fin d) K)) (hH : H ≤ LargeEvenSUGroup (Fin d) K (2 ^ n)) :
    LargeEvenInnSet (LargeEvenProj H) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin d) K (2 ^ n)) :=
  lemma119_innSet_gen H _ (fun h hh => lemma119_su_mem_gu (hH hh))

private theorem lemma119_recipeLinear_inn {d N : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_gen _ _ (fun _ _ => Set.mem_univ _)⟩⟩

private theorem lemma119_recipeUnitary_inn {d n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  have hc : CharP K 2 := lemma119_charP_two hK
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_su _ le_rfl⟩⟩

private theorem lemma119_recipeSymplectic_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m q false Q) :
    LargeEvenRecipeSymplectic m q false fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, lemma119_innSet_sp _ le_rfl⟩⟩

private theorem lemma119_recipeOmegaPlus_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, subset_rfl⟩⟩

private theorem lemma119_recipeOmegaMinus_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, b, c, hbc, ⟨hQ, subset_rfl⟩⟩

private theorem largeEvenMarking_of_rawDatum_inn {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hChev : GGChevStTag lab) {Q : LargeEvenRawCont}
    (hraw : LargeEvenRawDatum lab Q)
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F →
      Nonempty (X ⧸ Subgroup.center X ≃* R) ∧ LargeEvenInnSet R ⊆ I) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2
  refine ⟨hX.1, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F hRI => ?_) hraw
  obtain ⟨⟨e⟩, hInn⟩ := hQ R I F hRI
  exact ⟨e.symm.isSimpleGroup, nonabelian_of_mulEquiv e
    (exists_mul_ne_mul_centerQuot_of_perfect hX.1 inferInstance), e, hChev, hInn⟩

theorem largeEvenMarking_inn_of_statedClassicalModel {X : Type} [Group X]
    (hX : CFSG.Assembly.IsQuasisimple X) {t : StatedLieTag} {n f : ℕ}
    (hM : StatedClassicalModel (X ⧸ Subgroup.center X) t n 2 f) :
    LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  obtain ⟨-, hf, hadm⟩ := hM.1
  cases t with
  | PSL =>
    obtain ⟨hn, h22, -⟩ := hadm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m = 1 → 2 ≤ f := by
      rintro rfl
      by_contra hlt
      exact h22 (by rw [show f = 1 by omega]; rfl)
    have hlab : LargeEvenInLambda2 (⟨.A, m, f⟩ : LargeEvenLabel) :=
      ⟨hf, (by omega : 1 ≤ m), hm⟩
    refine largeEvenMarking_of_rawDatum_inn hX hlab (by simp [GGChevStTag]) ?_
      (fun _ _ _ _ h => h)
    exact lemma119_recipeLinear_inn (recipeLinear_of_statedClassicalModel hM)
  | PSU =>
    obtain ⟨hn, h32⟩ := hadm
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m = 2 → 2 ≤ f := by
      rintro rfl
      by_contra hlt
      exact h32 (by rw [show f = 1 by omega]; rfl)
    have hlab : LargeEvenInLambda2 (⟨.twA, m, f⟩ : LargeEvenLabel) :=
      ⟨hf, (by omega : 2 ≤ m), hm⟩
    refine largeEvenMarking_of_rawDatum_inn hX hlab (by simp [GGChevStTag]) ?_
      (fun _ _ _ _ h => h)
    exact lemma119_recipeUnitary_inn (recipeUnitary_of_statedClassicalModel hM)
  | PSp =>
    obtain ⟨hn, h22⟩ := hadm
    have hm : n = 2 → 2 ≤ f := by
      rintro rfl
      by_contra hlt
      exact h22 (by rw [show f = 1 by omega]; rfl)
    have hlab : LargeEvenInLambda2 (⟨.C, n, f⟩ : LargeEvenLabel) := ⟨hf, hn, hm⟩
    refine largeEvenMarking_of_rawDatum_inn hX hlab (by simp [GGChevStTag]) ?_
      (fun _ _ _ _ h => h)
    exact lemma119_recipeSymplectic_inn (recipeSymplectic_of_statedClassicalModel hM)
  | POmegaOdd => exact absurd rfl hadm.2
  | POmegaPlus =>
    have h3 : n ≠ 3 := by omega
    have hlab : LargeEvenInLambda2 (⟨.D, n, f⟩ : LargeEvenLabel) :=
      ⟨hf, (by omega : 3 ≤ n)⟩
    refine largeEvenMarking_of_rawDatum_inn hX hlab (by simp [GGChevStTag]) ?_
      (fun _ _ _ _ h => h)
    simpa only [LargeEvenRawDatum, h3, ↓reduceIte] using
      lemma119_recipeOmegaPlus_inn (recipeOmegaPlus_of_statedClassicalModel hM)
  | POmegaMinus =>
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have hlab : LargeEvenInLambda2 (⟨.twD, n, f⟩ : LargeEvenLabel) :=
      ⟨hf, (by omega : 2 ≤ n)⟩
    refine largeEvenMarking_of_rawDatum_inn hX hlab (by simp [GGChevStTag]) ?_
      (fun _ _ _ _ h => h)
    simpa only [LargeEvenRawDatum, h2, h3, ↓reduceIte] using
      lemma119_recipeOmegaMinus_inn (recipeOmegaMinus_of_statedClassicalModel hM)
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact hM.2.elim

theorem isQuasisimple_largeEvenMarking_of_equiv_statedSp {X : Type} [Group X] {K : Type}
    [Field K] [Finite K] {m f : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 2 ≤ m)
    (hmf : (m, 2 ^ f) ≠ (2, 2)) (e : X ≃* ↥(StatedSp m K)) :
    CFSG.Assembly.IsQuasisimple X ∧
      LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hSp : CFSG.IsQuasisimple (StatedSp m K) := by
    refine CFSG.LieType.Universal.Symplectic.isQuasisimple m K (by omega) ?_
    by_cases h2 : Nat.card K = 2
    · right; right
      refine ⟨h2, ?_⟩
      have hp : 2 ^ f = 2 := by rw [← hK]; exact h2
      by_contra hlt
      exact hmf (by rw [show m = 2 by omega, hp])
    · left; right
      have hf2 : 2 ≤ f := by
        rcases Nat.lt_or_ge f 2 with hlt | hge
        · have hf1 : f = 1 := by omega
          subst hf1
          rw [pow_one] at hK
          exact (h2 hK).elim
        · exact hge
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        _ = Nat.card K := hK.symm
  have hX : CFSG.Assembly.IsQuasisimple X :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e ⟨hSp.1.commutator_eq_top, hSp.2.1⟩
  have hModel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp m 2 f := by
    refine ⟨⟨Nat.prime_two, hf, hm, hmf⟩, K, inferInstance, inferInstance, hK, ⟨?eZ⟩⟩
    exact (QuotientGroup.congr (Subgroup.center X) (Subgroup.center (StatedSp m K)) e
      (Subgroup.map_center_eq e)).trans
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m K)
  exact ⟨hX, largeEvenMarking_inn_of_statedClassicalModel hX hModel⟩

theorem isQuasisimple_largeEvenMarking_of_equiv_SL2 {X : Type} [Group X] {K : Type}
    [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    CFSG.Assembly.IsQuasisimple X ∧
      LargeEvenMarking X (fun lab R _ I _ _ => GGChevStTag lab ∧ LargeEvenInnSet R ⊆ I) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr h4)
  have hX : CFSG.Assembly.IsQuasisimple X :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e ⟨hSL.1.commutator_eq_top, hSL.2.1⟩
  have hModel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 f := by
    refine ⟨⟨Nat.prime_two, (by omega : 1 ≤ f), le_rfl, ?_, ?_⟩, K, inferInstance,
      inferInstance, hK, ⟨?eZ⟩⟩
    · intro h
      rw [Prod.mk.injEq] at h
      omega
    · intro h
      rw [Prod.mk.injEq] at h
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      rw [h.2] at h2
      norm_num at h2
    · exact (QuotientGroup.congr (Subgroup.center X)
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) e
        (Subgroup.map_center_eq e)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)
  exact ⟨hX, largeEvenMarking_inn_of_statedClassicalModel hX hModel⟩

theorem isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two {G : Type} [Group G]
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {T : Subgroup G}
    (e : ↥T ≃* ↥(StatedSp 2 K)) :
    CFSG.Assembly.IsQuasisimple ↥⁅T, T⁆ ∧
      LargeEvenMarking ↥⁅T, T⁆ (fun lab R _ I _ θ => GGChevStTag lab ∧
        ∀ α ∈ {α : MulAut ↥⁅T, T⁆ | ∃ t ∈ T, ∀ y : ↥⁅T, T⁆,
            ((α y : ↥⁅T, T⁆) : G) = t⁻¹ * (y : G) * t},
          ∃ φ ∈ I, ∀ y : ↥⁅T, T⁆, φ (θ (QuotientGroup.mk y)) =
            θ (QuotientGroup.mk (α y))) := by
  let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
  let c₁ : ↥⁅T, T⁆ ≃* ↥(commutator ↥T) :=
    (((commutator ↥T).equivMapOfInjective T.subtype T.subtype_injective).trans
      (MulEquiv.subgroupCongr T.map_subtype_commutator)).symm
  let c₂ : ↥(commutator ↥T) ≃* ↥(commutator ↥(StatedSp 2 K)) :=
    ((commutator ↥T).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]))
  let c₃ : ↥(commutator ↥(StatedSp 2 K)) ≃* ↥H :=
    ((commutator ↥(StatedSp 2 K)).equivMapOfInjective (StatedSp 2 K).subtype
      (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (StatedSp 2 K)))
  let e₁ : ↥⁅T, T⁆ ≃* ↥H := c₁.trans (c₂.trans c₃)
  have h₁ : ∀ x : ↥(commutator ↥T), ((c₁.symm x : ↥⁅T, T⁆) : G) = (x : G) := fun _ => rfl
  have h₂ : ∀ x : ↥(commutator ↥T),
      ((c₂ x : ↥(commutator ↥(StatedSp 2 K))) : ↥(StatedSp 2 K)) = e x := fun _ => rfl
  have h₃ : ∀ x : ↥(commutator ↥(StatedSp 2 K)),
      ((c₃ x : ↥H) : GL (Fin 2 ⊕ Fin 2) K) =
        ((x : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) := fun _ => rfl
  have he₁ : ∀ y : ↥⁅T, T⁆,
      ((e₁ y : ↥H) : GL (Fin 2 ⊕ Fin 2) K) =
        ((e ⟨(y : G), Subgroup.commutator_le_self T y.2⟩ : ↥(StatedSp 2 K)) :
          GL (Fin 2 ⊕ Fin 2) K) := by
    intro y
    have hc : ((c₁ y : ↥(commutator ↥T)) : ↥T) =
        ⟨(y : G), Subgroup.commutator_le_self T y.2⟩ := by
      apply Subtype.ext
      have hs := h₁ (c₁ y)
      rw [MulEquiv.symm_apply_apply] at hs
      exact hs.symm
    calc ((e₁ y : ↥H) : GL (Fin 2 ⊕ Fin 2) K)
        = ((c₃ (c₂ (c₁ y)) : ↥H) : GL (Fin 2 ⊕ Fin 2) K) := by
          simp only [e₁, MulEquiv.trans_apply]
      _ = ((c₂ (c₁ y) : ↥(commutator ↥(StatedSp 2 K))) : GL (Fin 2 ⊕ Fin 2) K) := h₃ _
      _ = ((e (c₁ y) : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) := by rw [h₂]
      _ = ((e ⟨(y : G), Subgroup.commutator_le_self T y.2⟩ : ↥(StatedSp 2 K)) :
            GL (Fin 2 ⊕ Fin 2) K) := by rw [hc]
  have hSp4 : CFSG.IsQuasisimple ↥(commutator ↥T) :=
    (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour
      (e.trans (CFSG.SeitzReduction.F4Pilot.sp4EquivSympFour hK))).1
  have hqL : CFSG.IsQuasisimple ↥⁅T, T⁆ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv c₁.symm hSp4
  have hIsQ : CFSG.Assembly.IsQuasisimple ↥⁅T, T⁆ :=
    ⟨hqL.1.commutator_eq_top, hqL.2.1⟩
  haveI hA₆ : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eRH⟩ := nonempty_largeEvenProj_equiv_of_card_two hK H
  obtain ⟨eR⟩ := nonempty_b2der_equiv_alternatingGroup hK
  have hSimpleR : IsSimpleGroup (LargeEvenProj H) := eR.isSimpleGroup
  let eA₆ : ↥⁅T, T⁆ ≃* ↥(alternatingGroup (Fin 6)) := e₁.trans (eRH.symm.trans eR)
  have hSimpleL : IsSimpleGroup ↥⁅T, T⁆ := eA₆.isSimpleGroup
  haveI : Group.IsPerfect ↥⁅T, T⁆ := hqL.1
  have hnabL : ∃ a b : ↥⁅T, T⁆, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨h⟩⟩
  have hnabR : ∃ a b : LargeEvenProj H, a * b ≠ b * a :=
    nonabelian_of_mulEquiv (e₁.trans eRH.symm) hnabL
  haveI := hSimpleL
  have hcenterL : Subgroup.center ↥⁅T, T⁆ = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_nonabelian hnabL
  have hscalarsH : (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H = ⊥ := by
    rw [largeEvenScalars_eq_bot hK, Subgroup.bot_subgroupOf]
  have hmapθ : (Subgroup.center ↥⁅T, T⁆).map e₁.toMonoidHom =
      (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H := by
    rw [hcenterL, hscalarsH, Subgroup.map_bot]
  let θ : ↥⁅T, T⁆ ⧸ Subgroup.center ↥⁅T, T⁆ ≃* LargeEvenProj H :=
    QuotientGroup.congr (Subgroup.center ↥⁅T, T⁆)
      ((LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H) e₁ hmapθ
  have hθ : ∀ y : ↥⁅T, T⁆, θ (QuotientGroup.mk y) = QuotientGroup.mk (e₁ y) :=
    fun y => QuotientGroup.congr_mk _ _ _ _ y
  refine ⟨hIsQ, ?_⟩
  refine ⟨hqL.1.commutator_eq_top, ⟨⟨.B2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ?_⟩⟩
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  refine ⟨hSimpleR, hnabR, θ, ?_, ?_⟩
  · simp [GGChevStTag]
  · intro α hα
    obtain ⟨t, htT, htα⟩ := hα
    let A : GL (Fin 2 ⊕ Fin 2) K :=
      ((e ⟨t, htT⟩ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K)⁻¹
    have hA_mem : A ∈ LargeEvenSpGroup K 2 :=
      (LargeEvenSpGroup K 2).inv_mem (e ⟨t, htT⟩).2
    have hA : A ∈ LargeEvenGSpSet K 2 :=
      ⟨1, one_ne_zero, by rw [one_smul]; exact lemma119_sp_form hA_mem⟩
    have hSp_conj : (LargeEvenSpGroup K 2).map (MulAut.conj A).toMonoidHom =
        LargeEvenSpGroup K 2 := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (LargeEvenSpGroup K 2).mul_mem
          ((LargeEvenSpGroup K 2).mul_mem hA_mem hy) ((LargeEvenSpGroup K 2).inv_mem hA_mem)
      · intro hx
        refine ⟨A⁻¹ * x * A, ?_, ?_⟩
        · exact (LargeEvenSpGroup K 2).mul_mem
            ((LargeEvenSpGroup K 2).mul_mem ((LargeEvenSpGroup K 2).inv_mem hA_mem) hx) hA_mem
        · change MulAut.conj A (A⁻¹ * x * A) = x
          rw [MulAut.conj_apply]; group
    have hmapH : H.map (MulAut.conj A).toMonoidHom = H := by
      show (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆).map
        (MulAut.conj A).toMonoidHom = ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
      rw [Subgroup.map_commutator, hSp_conj]
    let cH : ↥H ≃* ↥H :=
      (H.equivMapOfInjective (MulAut.conj A).toMonoidHom (MulEquiv.injective _)).trans
        (MulEquiv.subgroupCongr hmapH)
    have hcH : ∀ h : ↥H,
        ((cH h : ↥H) : GL (Fin 2 ⊕ Fin 2) K) = A * (h : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹ := by
      intro h
      change (MulAut.conj A) (h : GL (Fin 2 ⊕ Fin 2) K) = A * (h : GL _ K) * A⁻¹
      rw [MulAut.conj_apply]
    let φ : MulAut (LargeEvenProj H) :=
      QuotientGroup.congr ((LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H)
        ((LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H) cH (by rw [hscalarsH, Subgroup.map_bot])
    have hφmem : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGSpSet K 2) := by
      refine ⟨A, hA, fun h h' hh' => ?_⟩
      have hcHeq : cH h = h' := by
        apply Subtype.ext
        rw [hcH, hh']
      have : φ (LargeEvenProjMk H h) = LargeEvenProjMk H (cH h) :=
        QuotientGroup.congr_mk _ _ _ _ h
      rw [this, hcHeq]
    refine ⟨φ, hφmem, fun y => ?_⟩
    have hKey : cH (e₁ y) = e₁ (α y) := by
      apply Subtype.ext
      rw [hcH, he₁ y, he₁ (α y)]
      have h1 : (⟨((α y : ↥⁅T, T⁆) : G), Subgroup.commutator_le_self T (α y).2⟩ : ↥T) =
          (⟨t, htT⟩ : ↥T)⁻¹ * ⟨(y : G), Subgroup.commutator_le_self T y.2⟩ * ⟨t, htT⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact htα y
      rw [h1, map_mul, map_mul, map_inv]
      rfl
    have hφθ : φ (QuotientGroup.mk (e₁ y)) = QuotientGroup.mk (cH (e₁ y)) :=
      QuotientGroup.congr_mk _ _ _ _ (e₁ y)
    rw [hθ y, hφθ, hKey, hθ (α y)]

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParOMTailAA
public import CFSG.LargeExtraspecial.DWFldOrth

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped commutatorElement

theorem s16t3_minus_cuts_orthCuts {r : ℕ} (hr : 1 ≤ r) : OrthCuts r (s16t3MinusCuts r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hdiv : 2 * ((r + 1) / 2) ≤ r + 1 := by
      rw [mul_comm]
      exact Nat.div_mul_le_self (r + 1) 2
    have hi_lt : (i : ℕ) < (r + 1) / 2 := by
      have h1 : (i : ℕ) < (j : ℕ) := hij
      have h2 : (j : ℕ) ≤ (r + 1) / 2 := by
        have := j.isLt
        omega
      omega
    have hi : 2 * (i : ℕ) + 1 ≤ r := by
      have h1 : (i : ℕ) + 1 ≤ (r + 1) / 2 := Nat.succ_le_of_lt hi_lt
      have h2 : 2 * ((i : ℕ) + 1) ≤ 2 * ((r + 1) / 2) := Nat.mul_le_mul_left 2 h1
      have h3 : 2 * ((i : ℕ) + 1) ≤ r + 1 := h2.trans hdiv
      omega
    have hdi : s16t3MinusCuts r i = 2 * (i : ℕ) := by
      simp only [s16t3MinusCuts]
      exact min_eq_left (by omega)
    rw [hdi]
    show 2 * (i : ℕ) < min (2 * (j : ℕ)) r
    exact lt_min (by omega) (by omega)
  · simp [s16t3MinusCuts]
  · show min (2 * ((Fin.last ((r + 1) / 2) : Fin ((r + 1) / 2 + 1)) : ℕ)) r ≤ r
    exact min_le_right _ _

theorem s16t3_minus_cuts_last (r : ℕ) :
    s16t3MinusCuts r (Fin.last ((r + 1) / 2)) = r := by
  simp only [s16t3MinusCuts]
  rw [min_eq_right]
  have hdiv : r ≤ 2 * ((r + 1) / 2) := by omega
  exact hdiv

theorem s16t3_minus_cuts_block_len {r : ℕ} (hr : 1 ≤ r) (l : Fin ((r + 1) / 2)) :
    s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc =
      if (l : ℕ) < r / 2 then 2 else 1 := by
  simp only [s16t3MinusCuts, Fin.val_succ, Fin.val_castSucc]
  by_cases h : (l : ℕ) < r / 2
  · rw [if_pos h]
    have h2 : 2 * ((l : ℕ) + 1) ≤ r := by
      have := Nat.div_mul_le_self r 2
      omega
    have h1 : 2 * (l : ℕ) ≤ r := by omega
    rw [min_eq_left h2, min_eq_left h1]
    omega
  · rw [if_neg h]
    have hl : (l : ℕ) < (r + 1) / 2 := l.isLt
    have h1 : 2 * (l : ℕ) ≤ r := by
      have := Nat.div_mul_le_self r 2
      omega
    have h2 : r ≤ 2 * ((l : ℕ) + 1) := by
      have := Nat.div_mul_le_self (r + 1) 2
      omega
    rw [min_eq_right h2, min_eq_left h1]
    omega

private theorem s16t3_prod_ite_pow (s m : ℕ) (hm : m ≤ s) :
    ∏ l : Fin s, (if (l : ℕ) < m then (6 : ℕ) else 1) = 6 ^ m := by
  rw [← Finset.prod_range (fun i : ℕ => if i < m then (6 : ℕ) else 1) (n := s)]
  rw [show s = m + (s - m) by omega, Finset.prod_range_add]
  rw [Finset.prod_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))]
  rw [Finset.prod_const, Finset.card_range]
  have h1 : ∀ i ∈ Finset.range (s - m), (if m + i < m then (6 : ℕ) else 1) = 1 := by
    intro i hi
    rw [if_neg]
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_const_one, mul_one]

theorem s16t3_gl_card_two {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) = 6 := by
  rw [Matrix.card_GL_field, Fin.prod_univ_two, hK]
  norm_num

theorem s16t3_gl_card_one {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    Nat.card (Matrix.GeneralLinearGroup (Fin 1) K) = 1 := by
  rw [Matrix.card_GL_field, Fin.prod_univ_one, hK]
  norm_num

theorem s16t3_minus_cuts_prod_gl {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    {r : ℕ} (hr : 1 ≤ r) :
    ∏ l : Fin ((r + 1) / 2),
        Nat.card (Matrix.GeneralLinearGroup
          (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K) = 6 ^ (r / 2) := by
  have hcongr : ∀ l : Fin ((r + 1) / 2),
      Nat.card (Matrix.GeneralLinearGroup
        (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K) =
      (if (l : ℕ) < r / 2 then (6 : ℕ) else 1) := by
    intro l
    rw [s16t3_minus_cuts_block_len hr l]
    by_cases h : (l : ℕ) < r / 2
    · rw [if_pos h, if_pos h]
      exact s16t3_gl_card_two hK
    · rw [if_neg h, if_neg h]
      exact s16t3_gl_card_one hK
  rw [Finset.prod_congr rfl (fun l _ => hcongr l)]
  exact s16t3_prod_ite_pow ((r + 1) / 2) (r / 2) (by omega)

theorem s16t3_resLevi_card {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    Nat.card (((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K))) = 6 := by
  rw [show Nat.card (((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K))) =
      Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) from
    Nat.card_congr (LinearEquiv.autCongr (LinearEquiv.uniqueProd (R := K)
      (M := Fin 2 → K) (M₂ := Fin 0 ⊕ Fin 0 → K))).toEquiv,
    show Nat.card ((Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
      Nat.card (LinearMap.GeneralLinearGroup K (Fin 2 → K)) from
    Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 2 → K)).symm.toEquiv,
    show Nat.card (LinearMap.GeneralLinearGroup K (Fin 2 → K)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) K) from
    Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := K)).toEquiv.symm,
    s16t3_gl_card_two hK]

theorem s16t3_orthLeviGroup_card_dvd_six {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {r : ℕ} (hr : 1 ≤ r) (j : Fin ((r + 1) / 2) ⊕ Unit) :
    Nat.card (orthLeviGroup K r (s16t3MinusCuts r) j) ∣ 6 := by
  rcases j with l | u
  · change Nat.card (Matrix.GeneralLinearGroup
      (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K) ∣ 6
    rw [s16t3_minus_cuts_block_len hr l]
    by_cases h : (l : ℕ) < r / 2
    · rw [if_pos h, s16t3_gl_card_two hK]
    · rw [if_neg h, s16t3_gl_card_one hK]
      exact one_dvd 6
  · obtain rfl : u = () := rfl
    change Nat.card (((Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) ⊕
      Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) ⊕
          Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) → K) × (Fin 2 → K))) ∣ 6
    rw [s16t3_minus_cuts_last r, Nat.sub_self]
    rw [s16t3_resLevi_card hK]

theorem s16t3_sl_card_eq_gl_card {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (Matrix.SpecialLinearGroup (Fin k) K) =
      Nat.card (Matrix.GeneralLinearGroup (Fin k) K) := by
  haveI : NeZero k := ⟨by omega⟩
  rw [Matrix.card_SL_field, Matrix.card_GL_field, hK]
  norm_num

theorem s16t3_orthLeviBlock_card_inl {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    {r : ℕ} (hr : 1 ≤ r) (l : Fin ((r + 1) / 2)) :
    Nat.card ↥(orthLeviBlock K r (s16t3MinusCuts r) 1 1 (.inl l)) =
      if (l : ℕ) < r / 2 then 6 else 1 := by
  change Nat.card ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup
        (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K →* _).range = _
  rw [show Nat.card ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup
        (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K →*
          Matrix.GeneralLinearGroup
            (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K).range =
      Nat.card (Matrix.SpecialLinearGroup
        (Fin (s16t3MinusCuts r l.succ - s16t3MinusCuts r l.castSucc)) K) from
    Nat.card_congr (slEquivToGLRange (K := K) _).symm.toEquiv]
  rw [s16t3_minus_cuts_block_len hr l]
  by_cases h : (l : ℕ) < r / 2
  · rw [if_pos h, if_pos h]
    exact (s16t3_sl_card_eq_gl_card hK (by norm_num)).trans (s16t3_gl_card_two hK)
  · rw [if_neg h, if_neg h]
    exact (s16t3_sl_card_eq_gl_card hK (by norm_num)).trans (s16t3_gl_card_one hK)

theorem s16t3_orthLeviGroup_prod {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    {r : ℕ} (hr : 1 ≤ r) :
    Nat.card (∀ j : Fin ((r + 1) / 2) ⊕ Unit, orthLeviGroup K r (s16t3MinusCuts r) j) =
      6 ^ (r / 2 + 1) := by
  rw [Nat.card_pi, Fintype.prod_sum_type]
  have h1 : (∏ a : Fin ((r + 1) / 2),
      Nat.card (orthLeviGroup K r (s16t3MinusCuts r) (.inl a))) = 6 ^ (r / 2) :=
    s16t3_minus_cuts_prod_gl hK hr
  have h2 : (∏ a : Unit,
      Nat.card (orthLeviGroup K r (s16t3MinusCuts r) (.inr a))) = 6 := by
    rw [Fintype.prod_unique]
    change Nat.card (((Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) ⊕
      Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) ⊕
          Fin (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2))) → K) × (Fin 2 → K))) = 6
    rw [s16t3_minus_cuts_last r, Nat.sub_self, s16t3_resLevi_card hK]
  rw [h1, h2]
  exact (pow_succ 6 (r / 2)).symm

private theorem s16t3_card_subgroup_pi {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Group (A i)] (H : ∀ i, Subgroup (A i)) :
    Nat.card ↥(Subgroup.pi Set.univ H) = ∏ i, Nat.card ↥(H i) := by
  calc Nat.card ↥(Subgroup.pi Set.univ H)
      = Nat.card {f : ∀ i, A i // ∀ i, f i ∈ H i} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun f => by rw [Subgroup.mem_pi]; simp))
    _ = Nat.card (Π i, ↥(H i)) :=
        Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i z => z ∈ H i))
    _ = ∏ i, Nat.card ↥(H i) := Nat.card_pi

private noncomputable def s16t3_tauA {K : Type} [Field K] :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun a := ![a 1, a 0]
  invFun a := ![a 1, a 0]
  left_inv a := by ext i; fin_cases i <;> simp
  right_inv a := by ext i; fin_cases i <;> simp
  map_add' a b := by ext i; fin_cases i <;> simp
  map_smul' c a := by ext i; fin_cases i <;> simp

@[simp] private theorem s16t3_tauA_apply_zero {K : Type} [Field K] (a : Fin 2 → K) :
    s16t3_tauA a 0 = a 1 := by simp [s16t3_tauA]

@[simp] private theorem s16t3_tauA_apply_one {K : Type} [Field K] (a : Fin 2 → K) :
    s16t3_tauA a 1 = a 0 := by simp [s16t3_tauA]

private noncomputable def s16t3_omegaA {K : Type} [Field K] [CharP K 2] :
    (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) where
  toFun a := ![a 1, a 0 + a 1]
  invFun a := ![a 0 + a 1, a 0]
  left_inv a := by
    ext i
    fin_cases i <;> simp <;> linear_combination CharTwo.add_self_eq_zero (a 1)
  right_inv a := by
    ext i
    fin_cases i <;> simp <;> linear_combination CharTwo.add_self_eq_zero (a 0)
  map_add' a b := by
    ext i
    fin_cases i <;> simp <;> abel
  map_smul' c a := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp] private theorem s16t3_omegaA_apply_zero {K : Type} [Field K] [CharP K 2]
    (a : Fin 2 → K) : s16t3_omegaA a 0 = a 1 := by simp [s16t3_omegaA]

@[simp] private theorem s16t3_omegaA_apply_one {K : Type} [Field K] [CharP K 2]
    (a : Fin 2 → K) : s16t3_omegaA a 1 = a 0 + a 1 := by simp [s16t3_omegaA]

private theorem s16t3_tauA_mem {K : Type} [Field K] :
    s16t3_tauA ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro a
  rw [minusTailForm_apply, minusTailForm_apply]
  simp only [s16t3_tauA_apply_zero, s16t3_tauA_apply_one]
  ring

private theorem s16t3_omegaA_mem {K : Type} [Field K] [CharP K 2] :
    s16t3_omegaA ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro a
  rw [minusTailForm_apply, minusTailForm_apply]
  simp only [s16t3_omegaA_apply_zero, s16t3_omegaA_apply_one]
  linear_combination (a 1) * CharTwo.add_self_eq_zero (a 0 + a 1)

private theorem s16t3_tauA_mul_omegaA_ne {K : Type} [Field K] [CharP K 2] :
    (s16t3_tauA (K := K)) * (s16t3_omegaA (K := K)) ≠
      (s16t3_omegaA (K := K)) * (s16t3_tauA (K := K)) := by
  intro h
  have h1 := congrArg
    (fun f : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) => f (Pi.single 0 1)) h
  have h2 := congrArg (fun f : Fin 2 → K => f 1) h1
  simp [s16t3_tauA_apply_zero, s16t3_tauA_apply_one, s16t3_omegaA_apply_zero,
    s16t3_omegaA_apply_one, Pi.single_apply] at h2

private theorem s16t3_commutator_minusTailForm_one_one_ne_bot {K : Type} [Field K]
    [CharP K 2] :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1)⁆ ≠ ⊥ := by
  intro hbot
  have hmem : ⁅s16t3_tauA, s16t3_omegaA⁆ ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1),
        TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K 1 1)⁆ :=
    Subgroup.commutator_mem_commutator s16t3_tauA_mem s16t3_omegaA_mem
  rw [hbot, Subgroup.mem_bot] at hmem
  exact s16t3_tauA_mul_omegaA_ne (commutatorElement_eq_one_iff_mul_comm.mp hmem)

theorem s16t3_orthResDer_zero_card {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2) :
    Nat.card ↥(orthResDer K 1 1 0) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two
      (by rw [Nat.card_eq_fintype_card]; exact hK)
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) hK
  have hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.irreducible_one_one
  have hQ : (QuadraticMap.polarBilin (quadTail 0 (minusTailForm K 1 1))).Nondegenerate :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.nondegenerate_polarBilin_quadTail
      (CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail.nondegenerate_minusTailForm hirr)
  have hle : orthResDer K 1 1 0 ≤
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup
        (quadTail 0 (minusTailForm K 1 1)) hQ :=
    CFSG.LargeExtraspecial.DW.commutator_le_omegaGroup hQ
  have hrel : (CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (quadTail 0 (minusTailForm K 1 1)) hQ).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K 1 1))) = 2 :=
    CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup _ hQ
  have hleO : CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (quadTail 0 (minusTailForm K 1 1)) hQ ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K 1 1)) :=
    CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le _ hQ
  have hO : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadTail 0 (minusTailForm K 1 1))) = 6 :=
    s16t3_orthMinus_card_binary hK
  have hmul := Subgroup.relIndex_mul_card
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadTail 0 (minusTailForm K 1 1)) hQ)
    (TauCeti.QuadraticMap.orthogonalGroup (quadTail 0 (minusTailForm K 1 1)))
  rw [inf_eq_left.mpr hleO, hrel, hO] at hmul
  have hcardω : Nat.card ↥(CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (quadTail 0 (minusTailForm K 1 1)) hQ) = 3 := by omega
  have hdvd : Nat.card ↥(orthResDer K 1 1 0) ∣ 3 := by
    rw [← hcardω]
    exact Subgroup.card_dvd_of_le hle
  have hne : orthResDer K 1 1 0 ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card ↥(orthResDer K 1 1 0) = 1 := Subgroup.card_eq_one.mpr hbot
    have hcongr := Nat.card_congr (orthMinusCommutatorCongr
      (minusTailZeroIsometry (K := K) (b := 1) (c := 1))).toEquiv
    rw [hcard1] at hcongr
    exact s16t3_commutator_minusTailForm_one_one_ne_bot
      (Subgroup.card_eq_one.mp hcongr.symm)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hne
  · exact h

theorem s16t3_orthLeviBlock_prod {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2)
    {r : ℕ} (hr : 1 ≤ r) :
    Nat.card ↥(Subgroup.pi Set.univ (orthLeviBlock K r (s16t3MinusCuts r) 1 1)) =
      6 ^ (r / 2) * 3 := by
  rw [s16t3_card_subgroup_pi, Fintype.prod_sum_type]
  have h1 : (∏ a : Fin ((r + 1) / 2),
      Nat.card ↥(orthLeviBlock K r (s16t3MinusCuts r) 1 1 (.inl a))) = 6 ^ (r / 2) := by
    rw [Finset.prod_congr rfl (fun a _ => s16t3_orthLeviBlock_card_inl hK hr a)]
    exact s16t3_prod_ite_pow ((r + 1) / 2) (r / 2) (by omega)
  have h2 : (∏ a : Unit,
      Nat.card ↥(orthLeviBlock K r (s16t3MinusCuts r) 1 1 (.inr a))) = 3 := by
    rw [Fintype.prod_unique]
    change Nat.card ↥(orthResDer K 1 1 (r - s16t3MinusCuts r (Fin.last ((r + 1) / 2)))) = 3
    rw [s16t3_minus_cuts_last r, Nat.sub_self]
    exact s16t3_orthResDer_zero_card hK
  rw [h1, h2]

private theorem s16t3_eq_of_dvd_two_pow_mul_three_pow {n x a : ℕ}
    (hn : n ∣ 2 ^ x * 3 ^ a) :
    n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := by
  have hpos : 0 < 2 ^ x * 3 ^ a := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hpos.ne' (zero_dvd_iff.mp hn)
  have hsupp : n.factorization.support ⊆ {2, 3} := by
    intro q hq
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hq
    obtain ⟨hqprime, hqdvd, -⟩ := hq
    rcases (Nat.Prime.dvd_mul hqprime).1 (hqdvd.trans hn) with h | h
    · exact Finset.mem_insert.2 (Or.inl ((Nat.prime_dvd_prime_iff_eq hqprime
        Nat.prime_two).1 (hqprime.dvd_of_dvd_pow h)))
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
        ((Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).1 (hqprime.dvd_of_dvd_pow h))))
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _,
    Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]

theorem s16t3_card_eq_two_pow_mul_three_pow {n c : ℕ}
    (hlo : 2 ^ c * 3 ^ (c + 1) ∣ n) (hhi : n ∣ 2 ^ (c + 1) * 3 ^ (c + 1)) :
    ∃ x : ℕ, n = 2 ^ x * 3 ^ (c + 1) := by
  have hpos : 0 < 2 ^ (c + 1) * 3 ^ (c + 1) := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hpos.ne' (zero_dvd_iff.mp hhi)
  have hfac : (2 ^ (c + 1) * 3 ^ (c + 1)).factorization 3 = c + 1 := by
    have h1 : (2 ^ (c + 1)).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => absurd
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num))
    rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply, h1,
      Nat.factorization_pow_self Nat.prime_three, zero_add]
  have hle3 : n.factorization 3 ≤ c + 1 := by
    have h : 3 ^ (n.factorization 3) ∣ 2 ^ (c + 1) * 3 ^ (c + 1) :=
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn0).mpr le_rfl).trans hhi
    have h' := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      (by positivity : 2 ^ (c + 1) * 3 ^ (c + 1) ≠ 0)).mp h
    rwa [hfac] at h'
  have hge3 : c + 1 ≤ n.factorization 3 := by
    have h : 3 ^ (c + 1) ∣ n :=
      (dvd_mul_left (3 ^ (c + 1)) (2 ^ c)).trans hlo
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn0).mp h
  refine ⟨n.factorization 2, ?_⟩
  have hmain := s16t3_eq_of_dvd_two_pow_mul_three_pow hhi
  have hfac3 : n.factorization 3 = c + 1 := le_antisymm hle3 hge3
  calc n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) := hmain
    _ = 2 ^ (n.factorization 2) * 3 ^ (c + 1) := by rw [hfac3]

theorem s16t3_pow_three_of_pow_six {G : Type*} [Group G] (h6 : ∀ g : G, g ^ 6 = 1) :
    ∀ g : G, ∀ k : ℕ, g ^ 3 ^ k = 1 → g ^ 3 = 1 := by
  intro g k hk
  have hdk : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd6 : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one (h6 g)
  have hcop : Nat.Coprime (orderOf g) 2 := by
    have h32 : Nat.Coprime (3 : ℕ) 2 := by decide
    exact (h32.pow_left k).coprime_dvd_left hdk
  have hd3 : orderOf g ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using hd6)
  rwa [← orderOf_dvd_iff_pow_eq_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

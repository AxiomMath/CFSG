module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoXfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoClose
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoSLEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoSLPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoSLSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoSpEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoSpPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmPEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmPPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmMEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmMPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoTriality
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoAltEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoAltPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Sig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_nat_exists_ne_ker {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (i : ι) (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    ∃ m : ↥(FFModel.nat Γ).sec, (m : (FFModel.nat Γ).Amb) ∉ (FFModel.nat Γ).ker := by
  refine ⟨⟨Multiplicative.ofAdd (Pi.single i (1 : K) : ι → K), Subgroup.mem_top _⟩, ?_⟩
  rw [show (FFModel.nat Γ).ker = ⊥ from rfl, Subgroup.mem_bot]
  intro h
  have h1 : Multiplicative.ofAdd (Pi.single i (1 : K) : ι → K) = 1 := h
  have h2 : (Pi.single i (1 : K) : ι → K) = 0 := ofAdd_eq_one.mp h1
  have h3 := congrFun h2 i
  simp at h3

private theorem s16k_alt_exists_ne_ker {n : ℕ} (hn : 3 ≤ n) :
    ∃ m : ↥(FFModel.altDn n).sec, (m : (FFModel.altDn n).Amb) ∉ (FFModel.altDn n).ker := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h10 : i1 ≠ i0 := fun h => by
    have h' : (1 : ℕ) = 0 := congrArg Fin.val h
    omega
  have h20 : i2 ≠ i0 := fun h => by
    have h' : (2 : ℕ) = 0 := congrArg Fin.val h
    omega
  have h21 : i2 ≠ i1 := fun h => by
    have h' : (2 : ℕ) = 1 := congrArg Fin.val h
    omega
  let v : Fin n → ZMod 2 :=
    (Pi.single i0 (1 : ZMod 2) : Fin n → ZMod 2) + (Pi.single i1 (1 : ZMod 2) : Fin n → ZMod 2)
  have hv : Multiplicative.ofAdd v ∈ G6.coreMod n := by
    rw [G6.mem_coreMod]
    change (∑ i, (((Pi.single i0 (1 : ZMod 2) : Fin n → ZMod 2)) i +
      ((Pi.single i1 (1 : ZMod 2) : Fin n → ZMod 2)) i)) = 0
    rw [Finset.sum_add_distrib]
    have h0 : (∑ i, ((Pi.single i0 (1 : ZMod 2) : Fin n → ZMod 2)) i) = 1 := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro b _ hb
        exact Pi.single_eq_of_ne hb 1
      · intro h
        exact absurd (Finset.mem_univ i0) h
    have h1 : (∑ i, ((Pi.single i1 (1 : ZMod 2) : Fin n → ZMod 2)) i) = 1 := by
      rw [Finset.sum_eq_single i1]
      · simp
      · intro b _ hb
        exact Pi.single_eq_of_ne hb 1
      · intro h
        exact absurd (Finset.mem_univ i1) h
    rw [h0, h1]
    decide
  refine ⟨⟨Multiplicative.ofAdd v, hv⟩, ?_⟩
  intro hker
  have hker' : Multiplicative.ofAdd v ∈
      Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := hker
  rw [Subgroup.mem_inf] at hker'
  rcases B5FinPerm.mem_zpowers_allOnes_iff.mp hker'.1 with h1 | h1
  · have hv0 : v i0 = 0 := congrFun (ofAdd_eq_one.mp h1) i0
    have h1' : v i0 = 1 := by
      change ((Pi.single i0 (1 : ZMod 2) : Fin n → ZMod 2) +
        (Pi.single i1 (1 : ZMod 2) : Fin n → ZMod 2)) i0 = 1
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne h10.symm 1, add_zero]
    rw [h1'] at hv0
    exact one_ne_zero hv0
  · have hveq : v = fun _ => (1 : ZMod 2) :=
      Multiplicative.ofAdd.injective (by rw [h1]; rfl)
    have hv2 : v i2 = 1 := congrFun hveq i2
    have h0 : v i2 = 0 := by
      change ((Pi.single i0 (1 : ZMod 2) : Fin n → ZMod 2) +
        (Pi.single i1 (1 : ZMod 2) : Fin n → ZMod 2)) i2 = 0
      rw [Pi.add_apply, Pi.single_eq_of_ne h20 1, Pi.single_eq_of_ne h21 1, add_zero]
    rw [h0] at hv2
    exact one_ne_zero hv2.symm

theorem s16k_false_of_sum_two_sl (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ} (hn : 6 ≤ n)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    False := by
  have hr := h.toRowCtx hq
  have h3 : 3 ∈ D.sig := by
    by_cases hn8 : 8 ≤ n
    · exact hr.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inl ⟨hSL, hn8⟩⟩
    · exact s16k_three_mem_sig_sl_small hr (by omega) hSL hS
  obtain ⟨I₁, I₂, hZ₁, hZ₂, -, -, hsup, hN₁, hN₂⟩ := s16k_sum_two_data hr hS
  obtain ⟨K₁, hK₁f, hK₁fin, hK₁card, hR₁⟩ := hN₁
  obtain ⟨K₂, hK₂f, hK₂fin, hK₂card, hR₂⟩ := hN₂
  letI : Field K₁ := hK₁f
  letI : Finite K₁ := hK₁fin
  letI : Field K₂ := hK₂f
  letI : Finite K₂ := hK₂fin
  obtain ⟨π₁, h₁⟩ := hR₁
  obtain ⟨π₂, h₂⟩ := hR₂
  have hK₁ : Nat.card K₁ = 2 := by simpa using hK₁card
  have hK₂ : Nat.card K₂ = 2 := by simpa using hK₂card
  have hπ₁ : Function.Surjective π₁ := h₁.1
  have hπ₂ : Function.Surjective π₂ := h₂.1
  obtain ⟨hinj₁, -, hEq | hEq⟩ := s16k_sl_two_equiv (n := n) (by omega) hSL hK₁ hK₂ hπ₁ hπ₂
  · have hfix := s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hEq
      (fun a b hab => (s16k_sl_pair_fix hK₁ (by omega) a b hab).1)
    have hne := s16k_nat_exists_ne_ker (⟨0, by omega⟩ : Fin n) (StatedSL n K₁)
    exact s16k_false_of_sum_two_models hr hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) h3 hne
      (by simpa only [S16kPairFix] using hfix)
  · have hfix := s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hEq
      (fun a b hab => (s16k_sl_pair_fix hK₁ (by omega) a b hab).2)
    have hne := s16k_nat_exists_ne_ker (⟨0, by omega⟩ : Fin n) (StatedSL n K₁)
    exact s16k_false_of_sum_two_models hr hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) h3 hne
      (by simpa only [S16kPairFix] using hfix)

theorem s16k_false_of_sum_two_sp (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ} (hn : 8 ≤ n)
    (hSp : IsSpn ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => NatSpn H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    False := by
  have hr := h.toRowCtx hq
  have h3 : 3 ∈ D.sig :=
    hr.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inr (Or.inl ⟨hSp, hn⟩)⟩
  obtain ⟨I₁, I₂, hZ₁, hZ₂, -, -, hsup, hN₁, hN₂⟩ := s16k_sum_two_data hr hS
  obtain ⟨-, K₁, hK₁f, hK₁fin, hK₁card, hR₁⟩ := hN₁
  obtain ⟨-, K₂, hK₂f, hK₂fin, hK₂card, hR₂⟩ := hN₂
  letI : Field K₁ := hK₁f
  letI : Finite K₁ := hK₁fin
  letI : Field K₂ := hK₂f
  letI : Finite K₂ := hK₂fin
  obtain ⟨π₁, h₁⟩ := hR₁
  obtain ⟨π₂, h₂⟩ := hR₂
  have hK₁ : Nat.card K₁ = 2 := by simpa using hK₁card
  have hK₂ : Nat.card K₂ = 2 := by simpa using hK₂card
  have hπ₁ : Function.Surjective π₁ := h₁.1
  have hπ₂ : Function.Surjective π₂ := h₂.1
  obtain ⟨hinj₁, -, hEq⟩ := s16k_sp_two_equiv (n := n) hn hSp hK₁ hK₂ hπ₁ hπ₂
  have hm : 4 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hfix := s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hEq
    (fun a b hab => s16k_sp_pair_fix hK₁ hm a b hab)
  have hne := s16k_nat_exists_ne_ker (Sum.inl (⟨0, Nat.div_pos (by omega : 2 ≤ n) (by norm_num)⟩ :
    Fin (n / 2)) : Fin (n / 2) ⊕ Fin (n / 2)) (StatedSp (n / 2) K₁)
  exact s16k_false_of_sum_two_models hr hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) h3 hne
    (by simpa only [S16kPairFix] using hfix)

theorem s16k_false_of_sum_two_omegaPlus (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hOut : S16kOmega8OutInner)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ} (hn : 8 ≤ n)
    (hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => NatOmegaPlus H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    False := by
  have hr := h.toRowCtx hq
  have h3 : 3 ∈ D.sig :=
    hr.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inr (Or.inr (Or.inl ⟨hΩ, hn⟩))⟩
  obtain ⟨I₁, I₂, hZ₁, hZ₂, hind₁, hind₂, hsup, hN₁, hN₂⟩ := s16k_sum_two_data hr hS
  obtain ⟨hEven, K₁, hK₁f, hK₁fin, hK₁card, hR₁⟩ := hN₁
  obtain ⟨-, K₂, hK₂f, hK₂fin, hK₂card, hR₂⟩ := hN₂
  letI : Field K₁ := hK₁f
  letI : Finite K₁ := hK₁fin
  letI : Field K₂ := hK₂f
  letI : Finite K₂ := hK₂fin
  obtain ⟨π₁, h₁⟩ := hR₁
  obtain ⟨π₂, h₂⟩ := hR₂
  have hK₁ : Nat.card K₁ = 2 := by simpa using hK₁card
  have hK₂ : Nat.card K₂ = 2 := by simpa using hK₂card
  have hπ₁ : Function.Surjective π₁ := h₁.1
  have hπ₂ : Function.Surjective π₂ := h₂.1
  obtain ⟨hinj₁, -, hEq⟩ := s16k_omegaPlus_two_equiv (n := n) hn hΩ hK₁ hK₂ hπ₁ hπ₂
  have hm : 4 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  by_cases hmod : S16kModelsEquivVia (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K₁)))
      (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K₁))).act
      (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K₂))) π₁ π₂
  · have hfix := s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hmod
      (fun a b hab => s16k_omegaPlus_pair_fix hK₁ hm a b hab)
    have hne := s16k_nat_exists_ne_ker (Sum.inl (⟨0, Nat.div_pos (by omega : 2 ≤ n) (by norm_num)⟩ :
      Fin (n / 2)) : Fin (n / 2) ⊕ Fin (n / 2)) (StatedOmega (StatedQuadPlus (n / 2) K₁))
    exact s16k_false_of_sum_two_models hr hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) h3 hne
      (by simpa only [S16kPairFix] using hfix)
  · have hn8 : n = 8 := by
      obtain ⟨k, hk⟩ := hEven
      by_contra h
      exact hmod (hEq (by omega))
    subst hn8
    exact s16k_false_of_sum_two_omegaPlus_triality hOut hr
      ⟨hK₁, hK₂, hZ₁, hZ₂, hind₁, hind₂, hsup, h₁, h₂, hmod⟩

theorem s16k_false_of_sum_two_omegaMinus (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ} (hn : 10 ≤ n)
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    False := by
  have hr := h.toRowCtx hq
  have h3 : 3 ∈ D.sig :=
    hr.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hΩ, hn⟩)))⟩
  obtain ⟨I₁, I₂, hZ₁, hZ₂, -, -, hsup, hN₁, hN₂⟩ := s16k_sum_two_data hr hS
  obtain ⟨-, K₁, hK₁f, hK₁fin, b₁, c₁, hK₁card, hirr₁, hR₁⟩ := hN₁
  obtain ⟨-, K₂, hK₂f, hK₂fin, b₂, c₂, hK₂card, hirr₂, hR₂⟩ := hN₂
  letI : Field K₁ := hK₁f
  letI : Finite K₁ := hK₁fin
  letI : Field K₂ := hK₂f
  letI : Finite K₂ := hK₂fin
  obtain ⟨π₁, h₁⟩ := hR₁
  obtain ⟨π₂, h₂⟩ := hR₂
  have hK₁ : Nat.card K₁ = 2 := by simpa using hK₁card
  have hK₂ : Nat.card K₂ = 2 := by simpa using hK₂card
  have hπ₁ : Function.Surjective π₁ := h₁.1
  have hπ₂ : Function.Surjective π₂ := h₂.1
  obtain ⟨hinj₁, -, hEq⟩ :=
    s16k_omegaMinus_two_equiv (n := n) hn hΩ hK₁ hK₂ hirr₁ hirr₂ hπ₁ hπ₂
  have hm : 5 ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  have hpos : 0 < n / 2 - 1 := by omega
  have hfix := s16k_pairFix_of_equiv_nat hinj₁ hπ₂ hEq
    (fun a b hab => s16k_omegaMinus_pair_fix hK₁ hm hirr₁ a b hab)
  have hne := s16k_nat_exists_ne_ker (Sum.inl (⟨0, hpos⟩ : Fin (n / 2 - 1)) :
    Fin (n / 2 - 1) ⊕ Fin (n / 2 - 1) ⊕ Fin 2)
    (StatedOmega (StatedQuadMinus (n / 2) K₁ b₁ c₁))
  exact s16k_false_of_sum_two_models hr hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) h3 hne
    (by simpa only [S16kPairFix] using hfix)

theorem s16k_false_of_sum_two_alt (h : S16kBase D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hq : CFSG.Open.IsQuasisimple ↥(lBar V₀ V hV L)) {n : ℕ} (hn : 12 ≤ n)
    (hA : IsAlt ↥(lBar V₀ V hV L) n)
    (hS : SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    False := by
  have hr := h.toRowCtx hq
  have h3 : 3 ∈ D.sig :=
    hr.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hA, hn⟩)))⟩
  obtain ⟨I₁, I₂, hZ₁, hZ₂, -, -, hsup, hN₁, hN₂⟩ := s16k_sum_two_data hr hS
  obtain ⟨π₁, h₁⟩ := hN₁
  obtain ⟨π₂, h₂⟩ := hN₂
  have hπ₁ : Function.Surjective π₁ := h₁.1
  have hπ₂ : Function.Surjective π₂ := h₂.1
  obtain ⟨hinj₁, -, hEq⟩ := s16k_alt_two_equiv (n := n) (by omega) hA hπ₁ hπ₂
  have hfix := s16k_pairFix_of_equiv hinj₁ hπ₂ hEq (s16k_alt_pair_fix (by omega))
  have hne := s16k_alt_exists_ne_ker (by omega : 3 ≤ n)
  exact s16k_false_of_sum_two_models hr hZ₁ hZ₂ hsup h₁ h₂ Nat.prime_three (by norm_num) h3 hne
    (by simpa only [S16kPairFix] using hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

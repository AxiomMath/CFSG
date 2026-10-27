module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmMark
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LieType.SeitzGeneration.OuterLinearLift
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.OuterLinearPlane
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def GGNbrNsSpLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrNsOrthLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrNsLinLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ (lab.n = 1 ∧ p = 3) ∧
    ¬ (lab.rank = 5 ∧ lab.n = 2 ∧ p = 5) ∧ ¬ (lab.rank = 8 ∧ lab.n = 1 ∧ p = 7)

namespace NbrInnerMore

theorem halfSplit_A_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.A, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) ∨ (l = 5 ∧ n = 2 ∧ p = 5) ∨ (l = 8 ∧ n = 1 ∧ p = 7) := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr (Or.inl h)
  · simp at ht
  · simp at ht
  · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h.2.1, h.2.2.1, h.2.2.2⟩))
  · simp at h

theorem ggOutdiagPrime_linear {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 1 ≤ d) :
    GGOutdiagPrime p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  intro φ hφ hφp
  obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hφ
  have h1 : conjAut d K (A ^ p) = 1 := by
    rw [map_pow, hA, ← map_pow, hφp, map_one]
  have h2 := AutPSL.mem_center_of_conjAut_eq_one hd h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  obtain ⟨μ, hμ⟩ := OrdPNS.exists_pow_eq hp hpK c
  set A' : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) μ⁻¹ * A with hA'
  have hA'p : A' ^ p = 1 :=
    TypeA.PGLTor.pow_eq_one_of_pow_eq_scalar_pow (by rw [← hc, hμ])
  have hdet : (A' : Matrix (Fin d) (Fin d) K).det = 1 :=
    OrdPNS.det_eq_one_of_pow_eq_one hp hpK
      (by rw [← Units.val_pow_eq_pow_val, hA'p, Units.val_one])
  set X : Matrix.SpecialLinearGroup (Fin d) K := ⟨A', hdet⟩ with hX
  have hXA : conjAut d K (Matrix.SpecialLinearGroup.toGL X) = conjAut d K A := by
    have e : Matrix.SpecialLinearGroup.toGL X = A' := Units.ext rfl
    rw [e, hA', map_mul, conjAut_scalar, one_mul]
  rw [← ggCongr_mem_range_conj_iff (TypeA.recipeEquiv d K), ← hA, ← hXA,
    CFSG.LieType.SeitzGeneration.conjAut_toGL]
  exact ⟨_, rfl⟩

theorem charP_two_of_card_pow {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK

theorem recipeSymplectic_outdiagPrime (p : ℕ) {l n : ℕ} (hn : 1 ≤ n) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧ GGOutdiagPrime p R I := by
  obtain ⟨K, _, _, hK, hq⟩ := h
  have : CharP K 2 := charP_two_of_card_pow hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hq, fun _ hφ _ => TableBSymp.sp_I_subset_inn hφ⟩

theorem largeEvenLabelAll_outdiagPrime_sp (p : ℕ) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .B ∨ lab.tag = .C) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases ht with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_outdiagPrime p hn hQ

theorem largeEvenLabelAll_outdiagPrime_orth (p : ℕ) {lab : LargeEvenLabel}
    (ht : lab.tag = .D ∨ lab.tag = .twD) (hl : 4 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hl
  intro Q hQ
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  rcases ht with h | h <;> dsimp only at h <;> subst h
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [h3, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hq⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hq, OrthRest.ggOutdiagPrime_inn⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [h2, h3, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, OrthRest.ggOutdiagPrime_inn⟩

theorem largeEvenLabelAll_outdiagPrime_linear {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .A) (hq : ¬ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hq'⟩ := hQ
  have : CharP K 2 := charP_two_of_card_pow hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hq',
    ggOutdiagPrime_linear hp (by rwa [hK]) (by omega)⟩

theorem lieModel_of_markedModel_two {X : Type} [Group X] {lab : LargeEvenLabel}
    (hc : markChar lab = 2) (hX : MarkedModel lab X) :
    LieModel X (markTag lab) (markRank lab) 2 (markDeg lab) := by
  have h := hX
  unfold MarkedModel at h
  rwa [hc] at h

section TypeDet

theorem not_halfSplit_of_markedModel_sp {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .B ∨ lab.tag = .C) (hq1 : ¬ p ∣ 2 ^ lab.n - 1) (hq2 : ¬ p ∣ 2 ^ lab.n + 1)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hL : LieModel X .PSp lab.rank 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    rcases ht with h | h <;> dsimp only at h <;> subst h <;> exact hX
  obtain ⟨hT, -, hD⟩ := CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique hL
    (lieModel_of_markedModel_two hc' hX')
  exact ClNonsplit.not_halfSplit_of_markPSp hp3 hT hD hq1 hq2

theorem not_halfSplit_of_markedModel_orth {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (ht : lab.tag = .D ∨ lab.tag = .twD) (hl : 4 ≤ lab.rank)
    (hq1 : ¬ p ∣ 2 ^ lab.n - 1) (hq2 : ¬ p ∣ 2 ^ lab.n + 1) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  obtain ⟨s, hs, hL⟩ : ∃ s : StatedLieTag, (s = .POmegaPlus ∨ s = .POmegaMinus) ∧
      LieModel X s lab.rank 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at hl ⊢
    have h2 : l ≠ 2 := by omega
    have h3 : l ≠ 3 := by omega
    rcases ht with h | h <;> dsimp only at h <;> subst h
    · have e1 : markTag ⟨.D, l, n⟩ = .POmegaPlus := by simp [markTag, h3]
      have e2 : markRank ⟨.D, l, n⟩ = l := by simp [markRank, h3]
      have h' := lieModel_of_markedModel_two rfl hX
      rw [e1, e2] at h'
      exact ⟨_, Or.inl rfl, h'⟩
    · have e1 : markTag ⟨.twD, l, n⟩ = .POmegaMinus := by simp [markTag, h2, h3]
      have e2 : markRank ⟨.twD, l, n⟩ = l := by simp [markRank, h2, h3]
      have e3 : markDeg ⟨.twD, l, n⟩ = n := by simp [markDeg, h2]
      have h' := lieModel_of_markedModel_two rfl hX
      rw [e1, e2, e3] at h'
      exact ⟨_, Or.inr rfl, h'⟩
  obtain ⟨hT, hR, hD⟩ := CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique hs hL
    (lieModel_of_markedModel_two hc' hX')
  refine (OmNonsplit.markOm_label hlab' hc' hp hp2 hp3 hq1 hq2
    (Or.inl ⟨?_, by omega, hD⟩)).1 c
  rcases hs with rfl | rfl
  · exact Or.inl hT
  · exact Or.inr hT

theorem not_halfSplit_of_markedModel_lin {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsLinLabel p lab) {X : Type} [Group X] (hX : MarkedModel lab X)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hl, hq1, h13, h5, h8⟩ := h
  have hL : LieModel X .PSL (lab.rank + 1) 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨hT, hR, hD⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by omega) hL
    (lieModel_of_markedModel_two hc' hX')
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  rcases LinNonsplit.markPSL_cases hT hc' hD with ⟨ht', hn'⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ <;>
    dsimp only at ht' <;> subst ht'
  · dsimp only at hn'
    subst hn'
    have hl' : l' = lab.rank := by
      simp only [markRank] at hR
      omega
    subst hl'
    rcases halfSplit_A_cases hHS with h1 | h1 | h1 | h1
    · exact hq1 h1
    · exact h13 h1
    · exact h5 h1
    · exact h8 h1
  · by_cases hl3 : l' = 3
    · simp only [markRank, hl3, ↓reduceIte] at hR
      omega
    · simp [markTag, hl3] at hT
  · by_cases hl2 : l' = 2
    · simp only [markRank, hl2, ↓reduceIte] at hR
      omega
    · by_cases hl3 : l' = 3 <;> simp [markTag, hl2, hl3] at hT

theorem not_markedModel_of_char_ne_two {X : Type} [Group X] {t : StatedLieTag} {m f : ℕ}
    (hL : LieModel X t m 2 f) (h1 : ¬ (t = .PSL ∧ m = 2 ∧ f = 2))
    (h2 : ¬ (t = .PSL ∧ m = 3 ∧ f = 1)) (h3 : ¬ (t = .PSU ∧ m = 4 ∧ f = 1))
    {lab' : LargeEvenLabel} (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  intro hX'
  have hc3 : markChar lab' = 3 := by
    obtain ⟨t', l', n'⟩ := lab'
    cases t' <;> simp_all [markChar]
  refine CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hL h1 h2 h3
    ⟨markTag lab', markRank lab', markChar lab', markDeg lab', by rw [hc3]; exact Nat.prime_three,
      hc, CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hX', hX'⟩

theorem not_markedModel_char_ne_two_lin {lab : LargeEvenLabel} (ht : lab.tag = .A)
    (hl : 4 ≤ lab.rank) {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  have hL : LieModel X .PSL (lab.rank + 1) 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => by omega) (fun h => by omega)
    (fun h => absurd h.1 (by decide)) hc

end TypeDet

end NbrInnerMore

section Labels

theorem ggTableBNbrInnerInputOn_nsSp : GGTableBNbrInnerInputOn GGNbrNsSpLabel :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun p _ _ _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_sp p hlab h.1).mono fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_sp h.1 h.2.1 h.2.2 hX hc' hX' c)

theorem ggTableBNbrInnerInputOn_nsOrth : GGTableBNbrInnerInputOn GGNbrNsOrthLabel :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.2.1 h.2.2.2))
    (fun p _ _ _ _ h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_orth p h.1 h.2.1).mono fun _ _ _ _ h _ _ => h)
    (fun _ _ hp hp2 _ h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_orth hp hp2 h.1 h.2.1 h.2.2.1 h.2.2.2 hX hlab'
        hc' hX' c)

theorem ggTableBNbrInnerInputOn_nsLin : GGTableBNbrInnerInputOn GGNbrNsLinLabel :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_lin h.1 h.2.1 hX hc)
    (fun _ _ hp _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab h.1 h.2.2.1).mono
        fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_lin h hX hc' hX' c)

end Labels

end CFSG.StandardType

end

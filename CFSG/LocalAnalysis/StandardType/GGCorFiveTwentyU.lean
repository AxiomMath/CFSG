module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly UCoord

theorem UCoord.card_sumZero_le (m p : ℕ) [NeZero p] : Nat.card ↥(sumZero (m + 1) p) ≤ p ^ m := by
  let F : ↥(sumZero (m + 1) p) → (Fin m → Multiplicative (ZMod p)) :=
    fun f i => (f : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc i)
  have hF : Function.Injective F := by
    intro f g hfg
    have hi : ∀ i : Fin m, crd f (Fin.castSucc i) = crd g (Fin.castSucc i) := fun i =>
      congrArg Multiplicative.toAdd (congrFun hfg i)
    refine ext_crd fun k => ?_
    induction k using Fin.lastCases with
    | last =>
      have hf := sum_crd f
      have hg := sum_crd g
      rw [Fin.sum_univ_castSucc] at hf hg
      simp only [hi] at hf
      exact add_left_cancel (hf.trans hg.symm)
    | cast i => exact hi i
  calc Nat.card ↥(sumZero (m + 1) p) ≤ Nat.card (Fin m → Multiplicative (ZMod p)) :=
        Nat.card_le_card_of_injective F hF
    _ = p ^ m := by
        rw [Nat.card_fun, Nat.card_fin]
        congr 1
        exact Nat.card_zmod p

theorem ggTorusWeylNormInnerSC_of_permElt' {p d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : 1 ≤ d) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) : GGTorusWeylNormInnerSC p R I := by
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
    exfalso
    obtain ⟨Θ, -⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hA hAI h3 hsc
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    have hle := UCoord.card_sumZero_le m p
    rw [Nat.card_congr Θ.toEquiv] at hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
    omega
  · exact ggTorusWeylNormInnerSC_of_permElt hp hp2 hd4 hZ hIp hcp h

theorem recipeUnitary_weylInputsSC
    {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      (GGTorusPseudoReflGenSC p R I ∧ GGTorusSchurSC p R I ∧ GGTorusWeylNormInnerSC p R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), φ ^ p = 1 →
        φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  exact ⟨ggTorusPseudoReflGenSC_of_permElt hp hp2 hZ hIp hcp hT,
    ggTorusSchurSC_of_permElt hp hp2 (by omega) hpd hZ hIp hcp hT,
    ggTorusWeylNormInnerSC_of_permElt' hp hp2 (by omega) hZ hIp hcp hT⟩

theorem ggTorusAutCardSC_unitary_all
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGTorusAutCardSC p
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) (d - 1) d.factorial := by
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), φ ^ p = 1 →
        φ ∈ Set.range (MulAut.conj :
          LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
            MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  exact ggTorusAutCardSC_of_permEltSC hp hp2 (by omega) hZ hIp hcp hT

theorem ggTorusAutCardSC_unitary_twA_label
    {p r n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hr : 3 ≤ r)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ r + 1) :
    LargeEvenLabelAll (⟨.twA, r, n⟩ : LargeEvenLabel) fun R _ I _ =>
      GGTorusAutCardSC p R I r (r + 1).factorial := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ, ?_⟩
  have hd : 3 ≤ r + 1 := by omega
  have hdq : (r + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hpd' : ¬ p ∣ r + 1 := hpd
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have h := ggTorusAutCardSC_unitary_all (K := K) (n := n) (d := r + 1) (p := p)
    hK hn hd hdq hp hp2 hpq hpd'
  simpa [show r + 1 - 1 = r by omega] using h

theorem ggTorusAutCardSC_unitary_four
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusAutCardSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenGUSet (Fin 4) K (2 ^ n))) 3 24 := by
  have hdq : (4, 2 ^ n) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  simpa only [show (4 - 1 : ℕ) = 3 by norm_num, show Nat.factorial 4 = 24 by norm_num] using
    ggTorusAutCardSC_unitary_all hK hn (by norm_num : 3 ≤ 4) hdq
      (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) h3 (by norm_num : ¬ 3 ∣ 4)

theorem ggPumpLineAutKnown_unitary_four_label
    {n : ℕ}
    (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twA, 3, n⟩ fun R _ I _ => GGTorusAutCardSC 3 R I 3 24 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ
  obtain ⟨K, hKfield, hKfin, hK, hQ⟩ := hQ
  exact ⟨K, hKfield, hKfin, hK, hQ, ggTorusAutCardSC_unitary_four hK hn h3⟩

@[expose] def GGUnitaryCoprimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1) ∨
    (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n + 1)

theorem largeEvenLabelAll_weylInputsSC_unitary
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGUnitaryCoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusPseudoReflGenSC p R I ∧ GGTorusSchurSC p R I ∧ GGTorusWeylNormInnerSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    have hl2n : l = 2 → 2 ≤ n := hlab.2.2
    refine recipeUnitary_weylInputsSC hp hpn hn (by omega) ?_ hpl hQ
    intro heq
    simp only [Prod.mk.injEq] at heq
    have hn2 := hl2n (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
    refine recipeUnitary_weylInputsSC hp hpn hn (by norm_num) (by simp) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

theorem ggWeylPseudoReflGenInputOn_unitary :
    GGWeylPseudoReflGenInputOn GGUnitaryCoprimeLabel :=
  ggWeylPseudoReflGenInputOn_of_labelsSC fun _ _ hp hlab h =>
    (largeEvenLabelAll_weylInputsSC_unitary hp hlab h).mono fun _ _ _ _ hP => hP.1

theorem ggWeylCentralizerScalarInputOn_unitary :
    GGWeylCentralizerScalarInputOn GGUnitaryCoprimeLabel :=
  ggWeylCentralizerScalarInputOn_of_labelsSC fun _ _ hp hlab h =>
    (largeEvenLabelAll_weylInputsSC_unitary hp hlab h).mono fun _ _ _ _ hP => hP.2.1

theorem ggInnerOnWeylInputOn_unitary :
    GGInnerOnWeylInputOn GGUnitaryCoprimeLabel :=
  ggInnerOnWeylInputOn_of_labelsSC fun _ _ hp hlab h =>
    (largeEvenLabelAll_weylInputsSC_unitary hp hlab h).mono fun _ _ _ _ hP => ⟨hP.1, hP.2.2⟩

theorem ggCorFiveTwentyOuterInputOn_unitary :
    GGCorFiveTwentyOuterInputOn GGUnitaryCoprimeLabel :=
  ggCorFiveTwentyOuterInputOn_of_inner ggInnerOnWeylInputOn_unitary

@[expose] def GGCorFiveTwentyRestULabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFiveTwentyRestSpLabel p lab ∧ ¬ GGUnitaryCoprimeLabel p lab

theorem ggCorFiveTwentyWeylInputsOn_restSp_of_restU
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestULabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestULabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestULabel) :
    GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestSpLabel ∧
      GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestSpLabel ∧
      GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestSpLabel := by
  have hsplit : ∀ p lab, GGCorFiveTwentyRestSpLabel p lab →
      GGUnitaryCoprimeLabel p lab ∨ GGCorFiveTwentyRestULabel p lab := fun p lab h => by
    by_cases hs : GGUnitaryCoprimeLabel p lab
    · exact Or.inl hs
    · exact Or.inr ⟨h, hs⟩
  exact ⟨ggWeylPseudoReflGenInputOn_of_split hsplit ggWeylPseudoReflGenInputOn_unitary hG,
    ggWeylCentralizerScalarInputOn_of_split hsplit ggWeylCentralizerScalarInputOn_unitary hSc,
    ggCorFiveTwentyOuterInputOn_of_split hsplit ggCorFiveTwentyOuterInputOn_unitary hO⟩

theorem ggCorFiveTwentyWeylInputs_of_restU
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestULabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestULabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestULabel) :
    GGWeylPseudoReflGenInput ∧ GGWeylCentralizerScalarInput ∧ GGCorFiveTwentyOuterInput :=
  let h := ggCorFiveTwentyWeylInputsOn_restSp_of_restU hG hSc hO
  ggCorFiveTwentyWeylInputs_of_restSp h.1 h.2.1 h.2.2

theorem ggCorFiveTwentyInput_of_stab_restU
    (ha₀ : GGLNoncyclicInput)
    (hRL : GGPseudoReflStabInput) (hRO : GGPseudoReflOrbitInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestULabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestULabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestULabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputsOn_restSp_of_restU hG hSc hO
  ggCorFiveTwentyInput_of_stab_restSp ha₀ hRL hRO h.1 h.2.1 h.2.2

theorem ggCorFiveTwentyInput_of_reflRest_restU
    (ha₀ : GGLNoncyclicInput)
    (hBL4 : GGNbrSStarInput) (hrest : GGPseudoReflStabModInputOn GGReflRestLabel)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestULabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestULabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestULabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputsOn_restSp_of_restU hG hSc hO
  ggCorFiveTwentyInput_of_reflRest_restSp ha₀ hBL4 hrest hnrest hA h.1 h.2.1 h.2.2

end CFSG.StandardType

end

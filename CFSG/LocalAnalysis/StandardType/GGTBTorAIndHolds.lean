module

public import CFSG.LocalAnalysis.StandardType.GGTDLabels
public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModelCoprime
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFour

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorusTorW_mono {p r r' m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {R : Type} [Group R] {I : Set (MulAut R)} (hp : 0 < p)
    (hrr : r ≤ r') (h : GGTorusTorW p r m N C M R I) : GGTorusTorW p r' m N C M R I := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  exact h L' ψ A ⟨hψ, hker, hperf, hA, hAI, (Nat.pow_le_pow_right hp hrr).trans hr, h3, hsc⟩

theorem ggTorusTorW_unitary_coprime_weak {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hN : 3 ≤ N) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ N + 1) (hU : LineU.UnitaryCoverAt n (N + 1) K)
    {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n))}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAe : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
      (LargeEvenGUSet (Fin (N + 1)) K (2 ^ n)),
      ∀ l : L', φ (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    GGTorusTorData (2 ^ n + 1) N (CartanMatrix.A N) (CoxeterMatrix.A N) L' A := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel_coprime hK hn (by omega) hp hpq hpd hU hψ hker hperf hAe hAI
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  exact ggTorusTorData_of_model_U hK hp hp2 hpq hN hM hAe hsc hdiag

theorem ggTorusTorW_unitary_coprime {K : Type} [Field K] [Finite K] {n p N : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hN : 3 ≤ N) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ N + 1) (hU : LineU.UnitaryCoverAt n (N + 1) K) :
    GGTorusTorW p (N - 1) (2 ^ n + 1) N (CartanMatrix.A N) (CoxeterMatrix.A N)
      (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (N + 1)) K (2 ^ n))) := by
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hsc⟩ := hTB
  exact ggTorusTorW_unitary_coprime_weak hK hn hN hp hpq hpd hU hψ hker hperf hAe hAI hsc

@[expose] def GGTBTorAIndUThree : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    lab.tag = .twA → lab.rank = 3 → p ∣ ggTorM lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusTorW p (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
          (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank) R I

theorem ggTBTorAInd_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .A ∨ lab.tag = .twA) (hl : lab.rank < 3)
    (hM : p ∣ ggTorM lab) {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusTorW p r m N C M R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hM
  rcases htag with rfl | rfl
  · have hM' : p ∣ 2 ^ n - 1 := by simpa [ggTorM] using hM
    have hl1 : 1 ≤ l := hlab.2.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hM'
    refine ⟨K, i1, i2, hK, hQ', fun L' _ _ ψ A hTB => ?_⟩
    exact absurd (hTB.mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ))
      (not_ggTorusTBGroup_small hp hp2 hpK (by omega) (by omega))
  · have hpq : p ∣ 2 ^ n + 1 := by simpa [ggTorM] using hM
    have h2l : 2 ≤ l := hlab.2.1
    have hl2 : l = 2 := by omega
    subst hl2
    have hn2 : 2 ≤ n := hlab.2.2 rfl
    have hn : 1 ≤ n := hlab.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    refine ⟨K, i1, i2, hK, hQ', fun L' _ _ ψ A hTB => ?_⟩
    obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, -⟩ := hTB
    have h2 : 2 < 2 ^ n := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact absurd h3 (not_le.mpr (TableBUE.card_lt_unitary_three_all
      (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hp2 hψ hker hperf hA hAI))

theorem ggTBTorAInd_of_uThree
    (hU3 : GGTBTorAIndUThree) : GGTBTorAInd := by
  intro p hp hp2 lab hlab htag hndvd hM
  rcases Nat.lt_or_ge lab.rank 3 with hl | hl
  · exact ggTBTorAInd_small hp hp2 hlab htag hl hM
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hndvd hM hl ⊢
  rcases htag with rfl | rfl
  · exact LargeEvenLabelAll.mono (fun _ _ _ _ h => ggTorusTorW_mono hp.pos (by omega) h)
      (ggTorusTorW_lin_label hp hp2 hl hM)
  rcases Nat.lt_or_ge l 4 with hl4 | hl4
  · obtain rfl : l = 3 := by omega
    exact hU3 p hp hp2 _ hlab rfl rfl hM
  have hpq : p ∣ 2 ^ n + 1 := by simpa [ggTorM] using hM
  have hE : ggTorEnn p ⟨.twA, l, n⟩ = 1 := by
    unfold ggTorEnn
    dsimp only
    rw [if_pos hpq]
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  have hdnd : (l + 1, n) ≠ (6, 1) := by
    rintro h
    obtain ⟨h1, rfl⟩ := Prod.mk.inj h
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
    exact hndvd (by rw [h1, hp3]; norm_num)
  have key := ggTorusTorW_unitary_coprime (K := K) hK hn (by omega) hp hpq hndvd
    (LineU.unitaryUniversalCover_holds n (l + 1) K hK (by omega) hdnd)
  simpa [ggTorM, hE] using key

@[expose] def GGTBTorAIndUFourTwo : Prop :=
  LargeEvenLabelAll ⟨.twA, 3, 1⟩ fun R _ I _ =>
    GGTorusTorW 3 (3 - 1) (2 ^ 1 + 1) 3 (CartanMatrix.A 3) (CoxeterMatrix.A 3) R I

theorem ggTBTorAIndUThree_of_uFourTwo
    (h : GGTBTorAIndUFourTwo) : GGTBTorAIndUThree := by
  intro p hp hp2 lab hlab htag hl hM
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hM ⊢
  subst htag
  subst hl
  have hpq : p ∣ 2 ^ n + 1 := by simpa [ggTorM] using hM
  have hE : ggTorEnn p ⟨.twA, 3, n⟩ = 1 := by
    unfold ggTorEnn
    dsimp only
    rw [if_pos hpq]
  have hn : 1 ≤ n := hlab.1
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
    subst hp3
    simpa [GGTBTorAIndUFourTwo, ggTorM, hE] using h
  have hpd : ¬ p ∣ 3 + 1 := fun h4 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ', ?_⟩
  have key := ggTorusTorW_unitary_coprime (K := K) hK hn le_rfl hp hpq hpd
    (unitaryCoverAt_of_even hK hn2 ⟨2, rfl⟩ le_rfl)
  simpa [ggTorM, hE] using key

end CFSG.StandardType

end

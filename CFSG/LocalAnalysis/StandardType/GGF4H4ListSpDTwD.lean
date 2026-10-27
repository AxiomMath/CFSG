module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSpOrth
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
import CFSG.LocalAnalysis.StandardType.GGK1ScLin
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBCard
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace F4H4Sp

section Models


theorem ggTorusAutCardSC_unitary_four_of_dvd {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) ∧
      GGTorusAutCardSC p (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
          (LargeEvenGUSet (Fin 4) K (2 ^ n))) 3 24 := by
  have hd : 3 ≤ 4 := by norm_num
  have hdq : (4, 2 ^ n) ≠ (3, 2) := by
    intro he
    simp only [Prod.mk.injEq] at he
    omega
  have hpd : ¬ p ∣ 4 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h)))
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
      (LargeEvenGUSet (Fin 4) K (2 ^ n)), φ ^ p = 1 →
        φ ∈ Set.range (MulAut.conj :
          LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) →*
            MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  have hSC := ggTorusAutCardSC_of_permEltSC hp hp2 (by norm_num) hZ hIp hcp hT
  rw [show (4 - 1) = 3 by norm_num, show Nat.factorial 4 = 24 by norm_num] at hSC
  exact ⟨hcp, hSC⟩

theorem largeEvenLabelAll_dThree_split {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.D, 3, n⟩ fun R _ I _ =>
      GGCenterPrime p R ∧ GGTorusAutCardSCr p (4 - 2) R I (Nat.factorial 4) := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hpd : ¬ (p ∣ 4 ∧ p ∣ Nat.card K - 1) := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h.1)))
  exact ⟨K, inferInstance, inferInstance, hK, hq, ggCenterPrime_linear_gcd (by norm_num) hp hp2 hpd,
    ggTorusAutCardSCr_of_mulEquiv (TypeA.recipeEquiv 4 K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (ggTorusAutCardSCr_PSL hp hpK le_rfl)⟩

theorem largeEvenLabelAll_twDThree_nonsplit {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1) :
    LargeEvenLabelAll ⟨.twD, 3, n⟩ fun R _ I _ =>
      GGCenterPrime p R ∧ GGTorusAutCardSC p R I 3 24 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [show (3 : ℕ) ≠ 2 by norm_num, ↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq,
    ggTorusAutCardSC_unitary_four_of_dvd hK hn hp hp2 hpq⟩

end Models

section Nbr


variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {ks : Finset (Subgroup G)}

theorem false_of_dThree_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.D, 3, n⟩)
    (hlab : GGHasLabel ⟨.D, 3, n⟩ (K ⧸ Subgroup.center K)) : False := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  by_cases hpq : p ∣ 2 ^ n - 1
  · obtain ⟨R, _, I, F, θ, hN, ⟨-, hcard⟩, hTB, -, hdvd, -⟩ :=
      exists_model_at_nbr hres hB hK hΛ hlab (largeEvenLabelAll_dThree_split hp hp2 hpq)
        fun _ _ _ _ h => h.1
    obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ := hTB
    have hTB2 : GGTorusTBGroup p (4 - 2) R I K (ggQuotHom θ) (ggGamma K hN).range :=
      ⟨hψ, hker, hperf, hA, hAI, le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) h3, h3, hsc⟩
    rw [hcard _ _ _ hTB2] at hdvd
    exact absurd hdvd (by decide)
  · refine false_of_card_lt_at_nbr hres hK hΛ hlab
      (largeEvenLabelAll_card_lt_nineClassical hp hp2 hΛ (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩))
    intro j hj hj3
    simp only [↓reduceIte] at hj3
    obtain rfl : j = 1 := by omega
    rwa [pow_one]

theorem false_of_twDThree_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.twD, 3, n⟩)
    (hlab : GGHasLabel ⟨.twD, 3, n⟩ (K ⧸ Subgroup.center K)) : False := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  by_cases hm : p ∣ 2 ^ n - 1
  · exact false_of_card_lt_at_nbr hres hK hΛ hlab
      ((largeEvenLabelAll_card_lt_twDThree hp hΛ ⟨rfl, rfl, hm⟩).mono fun _ _ _ _ h _ _ => h)
  by_cases hpl : p ∣ 2 ^ n + 1
  · obtain ⟨R, _, I, F, θ, hN, ⟨-, hcard⟩, hTB, -, hdvd, -⟩ :=
      exists_model_at_nbr hres hB hK hΛ hlab
        (largeEvenLabelAll_twDThree_nonsplit hp hp2 hΛ.1 hpl) fun _ _ _ _ h => h.1
    obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ := hTB
    rw [(hcard _ _ hψ hker hperf _ hA hAI h3 hsc).2] at hdvd
    exact absurd hdvd (by decide)
  · refine false_of_card_lt_at_nbr hres hK hΛ hlab
      (largeEvenLabelAll_card_lt_nineClassical hp hp2 hΛ (Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩)))
    intro j hj hj3
    simp only [↓reduceIte] at hj3
    obtain rfl : j = 1 := by omega
    rw [pow_one]
    intro h
    have h2 := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow] at h2
    rw [h2] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hpl h
    · exact hm h

theorem false_of_twDTwo_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks) {K : Subgroup G}
    (hK : K ∈ ks) {n : ℕ} (hΛ : LargeEvenInLambda2 ⟨.twD, 2, n⟩)
    (hlab : GGHasLabel ⟨.twD, 2, n⟩ (K ⧸ Subgroup.center K)) : False := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  exact false_of_card_lt_at_nbr hres hK hΛ hlab
    ((largeEvenLabelAll_card_lt_linearTwo hp hp2 hΛ (Or.inr ⟨rfl, rfl⟩)).mono
      fun _ _ _ _ h _ _ => h)

theorem nbrList_of_DtwD
    (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htD : lab.tag = .D ∨ lab.tag = .twD) (hlab : GGHasLabel lab (K ⧸ Subgroup.center K)) :
    GGF4NbrList p K := by
  by_cases hl : 4 ≤ lab.rank
  · exact nbrList_of_orth hres hB hK hΛ htD hl hlab
  exfalso
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htD hl
  rcases htD with rfl | rfl
  · have hl3 : l = 3 := by
      have := hΛ.2
      dsimp only at this
      omega
    subst hl3
    exact false_of_dThree_at_nbr hres hB hK hΛ hlab
  · have hl2 : 2 ≤ l := hΛ.2
    obtain rfl | rfl : l = 2 ∨ l = 3 := by omega
    · exact false_of_twDTwo_at_nbr hres hK hΛ hlab
    · exact false_of_twDThree_at_nbr hres hB hK hΛ hlab

end Nbr

end F4H4Sp

end CFSG.StandardType

end

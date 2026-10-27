module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YInput
public import CFSG.LocalAnalysis.UniquenessCase.UCK35w
import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
import CFSG.GroupTheory.PElementSubgroup
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.Sporadic.Fi22.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Opp IsSpor)
open scoped commutatorElement

private theorem quotient_data_of_stronglyPEmbedded {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {N : Subgroup X} (hN : IsStronglyPEmbedded p N)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) :
    IsStronglyPEmbedded p (N.map (QuotientGroup.mk' (CFSG.pPrimeCore p X))) ∧
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore p X)) ∧
      CFSG.pPrimeCore p (X ⧸ CFSG.pPrimeCore p X) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pPrimeCore p X).Normal := CFSG.pPrimeCore_normal
  have hY := CFSG.LocalAnalysis.UniquenessCase.UCK.pPrimeCore_le_of_stronglyPEmbedded hN h2
  have hcop : ¬ p ∣ Nat.card (CFSG.pPrimeCore p X) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  refine ⟨hN.map_quotient hY hcop, ?_, CFSG.pPrimeCore_quotient_eq_bot hp⟩
  rw [CFSG.SectionRank.pRank_quotient_eq _ hcop]
  exact h2

private theorem pow_three_dvd_card_pElementSubgroup_quotient {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (h3 : p ^ 3 ∣ Nat.card X) :
    p ^ 3 ∣ Nat.card ↥(Opp p (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore p X))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup X := CFSG.pPrimeCore p X
  haveI hOnorm : O.Normal := by
    dsimp [O]
    infer_instance
  have hcop : ¬ p ∣ Nat.card O := by
    dsimp [O]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card X = Nat.card (X ⧸ O) * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hcop3 : Nat.Coprime (p ^ 3) (Nat.card O) :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hcop)
  have hdvd : p ^ 3 ∣ Nat.card (X ⧸ O) := by
    refine hcop3.dvd_of_dvd_mul_right ?_
    rwa [← hcard]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p (X ⧸ O)))
  have hSdvd : p ^ 3 ∣ Nat.card (S : Subgroup (X ⧸ O)) :=
    S.pow_dvd_card_of_pow_dvd_card (n := 3) hdvd
  have hSle : (S : Subgroup (X ⧸ O)) ≤ Opp p (⊤ : Subgroup (X ⧸ O)) := by
    rw [Opp]
    exact CFSG.le_pElementSubgroup_of_isPGroup hp S.isPGroup' le_top
  exact hSdvd.trans (Subgroup.card_dvd_of_le hSle)

theorem isPSolvable_of_stronglyPEmbedded_of_pow_three_dvd
    (hK35w : CFSG.LocalAnalysis.UniquenessCase.UCK.K35w) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) (h3 : p ^ 3 ∣ Nat.card X) :
    CFSG.HallHigman.IsPSolvable p ↥N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup X := CFSG.pPrimeCore p X
  haveI hOnorm : O.Normal := by
    dsimp [O]
    infer_instance
  let Nbar : Subgroup (X ⧸ O) := N.map (QuotientGroup.mk' O)
  have hdata := quotient_data_of_stronglyPEmbedded hp hN h2
  have hNbar : IsStronglyPEmbedded p Nbar := by
    simpa only [Nbar, O] using hdata.1
  have h2bar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ O)) := by
    simpa only [O] using hdata.2.1
  have hObar : CFSG.pPrimeCore p (X ⧸ O) = ⊥ := by
    simpa only [O] using hdata.2.2
  have hXbar : CFSG.Open.IsKGroup (X ⧸ O) := hX.quotient O
  have hY : CFSG.pPrimeCore p X ≤ N :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.pPrimeCore_le_of_stronglyPEmbedded hN h2
  have hcases := hK35w (X ⧸ O) hXbar p hp hp2 Nbar hNbar h2bar hObar
  rcases hcases with hMps | hAlt | hFi
  · exact CFSG.LocalAnalysis.UniquenessCase.UCK.isPSolvable_of_quotient_pPrimeCore hY (by
      simpa only [Nbar, O] using hMps)
  · exfalso
    have hdvdOpp : p ^ 3 ∣ Nat.card ↥(Opp p (⊤ : Subgroup (X ⧸ O))) := by
      simpa only [O] using pow_three_dvd_card_pElementSubgroup_quotient hp h3
    obtain ⟨e⟩ := hAlt
    have hdvdAlt : p ^ 3 ∣ Nat.card (alternatingGroup (Fin (2 * p))) := by
      rwa [Nat.card_congr e.toEquiv] at hdvdOpp
    exact CFSG.AGLEmbeddingD2.AltSurvivor.not_pow_three_dvd_card_alternatingGroup hp hp2
      hdvdAlt
  · exfalso
    rcases hFi with ⟨rfl, hSpor⟩
    have hdvdOpp : 5 ^ 3 ∣
        Nat.card ↥(Opp 5 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 5 X))) :=
      pow_three_dvd_card_pElementSubgroup_quotient hp h3
    have hSpor' : Nonempty (↥(Opp 5 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 5 X))) ≃*
        CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := hSpor
    obtain ⟨e⟩ := hSpor'
    have hcardFi : Nat.card ↥(Opp 5 (⊤ : Subgroup (X ⧸ CFSG.pPrimeCore 5 X))) =
        64561751654400 := by
      rw [Nat.card_congr e.toEquiv]
      dsimp only [CFSG.Blueprint.NativeSporadic.Carrier]
      exact CFSG.Sporadic.Fi22.card_Fi22
    have hpow : 5 ^ 3 = 125 := by norm_num
    have h125 : 125 ∣ 64561751654400 := by
      rw [← hcardFi, ← hpow]
      exact hdvdOpp
    exact absurd h125 (by norm_num)

private theorem eq_one_of_forall_commutator_mem_of_pPrimeCore_eq_bot
    (hKZ : StronglyEmbeddedCentralFree) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : CFSG.pPrimeCore p X = ⊥) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded p N) {K : Subgroup X}
    (hK : ¬ p ∣ Nat.card K) {x : X} (hxN : x ∈ N)
    (hxp : ∃ k : ℕ, x ^ p ^ k = 1) (hx : ∀ n ∈ N, ⁅n, x⁆ ∈ K) : x = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Pχ, hPχsyl, hPχN⟩ := hN.exists_isSylowOf_le
  have hNindex : ¬ p ∣ N.index := by
    intro hd
    exact hPχsyl.2.2 (by
      simpa [Subgroup.relIndex_top_right] using
        hd.trans (Subgroup.index_dvd_of_le hPχN))
  obtain ⟨k, hk⟩ := hxp
  have hxNp : IsPGroup p (Subgroup.zpowers (⟨x, hxN⟩ : ↥N)) := by
    have hk' : (⟨x, hxN⟩ : ↥N) ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P₀N, hP₀N⟩ := hxNp.exists_le_sylow
  let P₀ : Subgroup X := (P₀N : Subgroup ↥N).map N.subtype
  have hP0p : IsPGroup p P₀ := P₀N.isPGroup'.map N.subtype
  have hP0leN : P₀ ≤ N := Subgroup.map_subtype_le _
  have hxP0N : (⟨x, hxN⟩ : ↥N) ∈ (P₀N : Subgroup ↥N) :=
    hP₀N (Subgroup.mem_zpowers (⟨x, hxN⟩ : ↥N))
  have hxP0 : x ∈ P₀ :=
    Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hxP0N, rfl⟩
  by_cases hP0bot : P₀ = ⊥
  · rw [hP0bot] at hxP0
    simpa using hxP0
  · have hP0dvd : p ∣ Nat.card P₀ := by
      rcases hP0p.card_eq_or_dvd with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hP0bot
      · exact h1
    have hP0idx : ¬ p ∣ P₀.index := by
      have hidx : P₀.index = (P₀N : Subgroup ↥N).index * N.index := by
        simpa [P₀] using (Subgroup.index_map_subtype (H := N) (K := (P₀N : Subgroup ↥N)))
      rw [hidx]
      exact Nat.Prime.not_dvd_mul hp P₀N.not_dvd_index hNindex
    have hcomm : ∀ n ∈ Subgroup.normalizer (P₀ : Set X), x * n = n * x := by
      intro n hn
      have hnN : n ∈ N := by
        by_contra hnnot
        have hP0conj : P₀ ≤ N.map (MulAut.conj n).toMonoidHom := by
          intro y hy
          have hconj : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
          have hy' : n⁻¹ * y * n ∈ P₀ :=
            (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * y * n)).mpr (hconj.symm ▸ hy)
          exact Subgroup.mem_map.mpr
            ⟨n⁻¹ * y * n, hP0leN hy', by simp [MulAut.conj_apply, mul_assoc]⟩
        have hle : P₀ ≤ N ⊓ N.map (MulAut.conj n).toMonoidHom := le_inf hP0leN hP0conj
        exact hN.2.2 n hnnot (hP0dvd.trans (Subgroup.card_dvd_of_le hle))
      have hcommP : ⁅n, x⁆ ∈ P₀ := by
        rw [commutatorElement_def]
        exact P₀.mul_mem ((Subgroup.mem_normalizer_iff.mp hn x).mp hxP0) (P₀.inv_mem hxP0)
      have hinf : K ⊓ P₀ = ⊥ := by
        rw [inf_comm]
        exact CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hK hP0p
      have hmem : ⁅n, x⁆ ∈ K ⊓ P₀ := ⟨hx n hnN, hcommP⟩
      have hone : ⁅n, x⁆ = 1 := by
        rwa [hinf, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
    let P : Sylow p X := hP0p.toSylow hP0idx
    have hPcoe : (P : Subgroup X) = P₀ := IsPGroup.toSylow_coe hP0p hP0idx
    refine hKZ p hp hp2 X hX hO h2 N hN P x ?_ ?_
    · rwa [hPcoe]
    · intro n hn
      rw [hPcoe] at hn
      exact hcomm n hn

theorem eq_one_of_forall_commutator_mem_of_stronglyPEmbedded
    (hKZ : StronglyEmbeddedCentralFree) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N) {K : Subgroup X}
    (hK : ¬ p ∣ Nat.card K) {x : X} (hxN : x ∈ N) (hxp : ∃ k : ℕ, x ^ p ^ k = 1)
    (hx : ∀ n ∈ N, ⁅n, x⁆ ∈ K) : x = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup X := CFSG.pPrimeCore p X
  haveI hOnorm : O.Normal := by
    dsimp [O]
    infer_instance
  have hdata := quotient_data_of_stronglyPEmbedded hp hN h2
  have hNbar : IsStronglyPEmbedded p (N.map (QuotientGroup.mk' O)) := by
    simpa only [O] using hdata.1
  have h2bar : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ O)) := by
    simpa only [O] using hdata.2.1
  have hObar : CFSG.pPrimeCore p (X ⧸ O) = ⊥ := by
    simpa only [O] using hdata.2.2
  have hXbar : CFSG.Open.IsKGroup (X ⧸ O) := hX.quotient O
  let xbar : X ⧸ O := QuotientGroup.mk' O x
  let Kbar : Subgroup (X ⧸ O) := K.map (QuotientGroup.mk' O)
  have hxbarN : xbar ∈ N.map (QuotientGroup.mk' O) :=
    Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
  have hxbarp : ∃ k : ℕ, xbar ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hxp
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hKbar : ¬ p ∣ Nat.card Kbar := by
    intro hd
    exact hK (hd.trans (Subgroup.card_map_dvd K (QuotientGroup.mk' O)))
  have hxbar : ∀ n ∈ N.map (QuotientGroup.mk' O), ⁅n, xbar⁆ ∈ Kbar := by
    intro n hn
    obtain ⟨m, hmN, rfl⟩ := hn
    rw [← map_commutatorElement]
    exact Subgroup.mem_map.mpr ⟨⁅m, x⁆, hx m hmN, rfl⟩
  have hxbar1 : xbar = 1 :=
    eq_one_of_forall_commutator_mem_of_pPrimeCore_eq_bot hKZ hXbar hp hp2 hObar h2bar
      hNbar hKbar hxbarN hxbarp hxbar
  have hxO : x ∈ O := by
    have h : (QuotientGroup.mk' O x : X ⧸ O) = 1 := by simpa only [xbar] using hxbar1
    rw [QuotientGroup.mk'_apply] at h
    exact (QuotientGroup.eq_one_iff x).mp h
  have hzp : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨k, hk⟩ := hxp
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hOcop : ¬ p ∣ Nat.card O := by
    dsimp [O]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hbot : Subgroup.zpowers x = ⊥ := by
    rw [← inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxO)]
    exact CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hOcop hzp
  exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers x)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

module

public import CFSG.Quasithin.H13.NQCatExcParSq
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528Sz

public section

namespace CFSG.Quasithin.H13.NQCat.F4SzPar

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.A5.G3
  CFSG.Quasithin.H13.NQCat.ExcParSq
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

abbrev szOrd (f : ℕ) : ℕ := (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1)

@[expose] def SzBound (f a b : ℕ) : Prop := a = b * szOrd f → (2 ^ f) ^ 10 ≤ b

theorem two_le_szOrd {f : ℕ} (hf : 1 ≤ f) : 2 ≤ szOrd f := by
  have h2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h1 : 1 ≤ 2 ^ f - 1 := by omega
  have h4 : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
  calc 2 ≤ 4 * 1 * 1 := by norm_num
    _ ≤ (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h4 h1) (by omega)

theorem szBound_one {f : ℕ} (hf : 1 ≤ f) : SzBound f 1 1 := fun h => by
  have := two_le_szOrd hf
  omega

theorem szBound_of_parabolicFacts {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hF : ParabolicFacts P Q) {f : ℕ} (hf : 1 ≤ f) (hQ : (2 ^ f) ^ 10 ≤ Nat.card ↥Q) :
    OrdCond (SzBound f) (perfectCore P) := by
  intro hcard
  rcases parabolicFacts_cases hF with htop | hQO
  · rw [htop] at hcard
    have hpos : 0 < Nat.card ↥(perfectCore P) := Nat.card_pos
    have := two_le_szOrd hf
    nlinarith
  · exact hQ.trans hQO

theorem szBound_f4
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount) :
    OrdCond (SzBound (2 * a + 1)) (perfectCore (F4.reeLocalParabolic K a j)) := by
  obtain ⟨hF0, hF1⟩ := F4.largeReeParabolicFacts a K ha hK
  have hUcard := card_reeFixedPosUnipotent hK
  have hprod := card_reeFixedPosUnipotent_eq_mul (K := K) (a := a) j
  have hq : 0 < 2 ^ (2 * a + 1) := by positivity
  obtain ⟨j, hj⟩ := j
  have hj2 : j < 2 := hj
  interval_cases j
  · refine szBound_of_parabolicFacts hF0 (by omega) ?_
    rw [card_reeFixedOrbitUnipotent_zero hK, hK, hUcard] at hprod
    have hv : Nat.card ↥(F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) =
        (2 ^ (2 * a + 1)) ^ 11 := by
      apply Nat.eq_of_mul_eq_mul_right hq
      rw [← hprod]
      ring
    rw [hv]
    exact Nat.pow_le_pow_right hq (by norm_num)
  · refine szBound_of_parabolicFacts hF1 (by omega) ?_
    rw [card_reeFixedOrbitUnipotent_one hK, hK, hUcard] at hprod
    have hv : Nat.card ↥(F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩) =
        (2 ^ (2 * a + 1)) ^ 10 := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hq 2)
      rw [← hprod]
      ring
    rw [hv]

theorem szBound_top
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    OrdCond (SzBound (2 * a + 1)) (perfectCore (⊤ : Subgroup ↥(F4.reeGamma K a))) := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hperf : perfectCore (⊤ : Subgroup ↥(F4.reeGamma K a)) = ⊤ :=
    perfectCore_eq_self_of_perfect
      ((commutator_def _).symm.trans (commutator_reeGamma_eq_top ha hK))
  rw [hperf]
  intro hcard
  rw [Subgroup.card_top] at hcard
  set q := 2 ^ (2 * a + 1) with hqdef
  have hU : Nat.card ↥(F4.reeFixedPosUnipotent K a) ∣ Nat.card ↥(F4.reeGamma K a) :=
    Subgroup.card_dvd_of_le reeFixedPosUnipotent_le_reeGamma
  rw [card_reeFixedPosUnipotent hK, hcard] at hU
  have hq2 : Even q := (Nat.even_pow' (by omega)).mpr even_two
  have hodd : Odd ((q - 1) * (q ^ 2 + 1)) :=
    (Nat.Even.sub_odd (Nat.one_le_two_pow) hq2 odd_one).mul
      ((Nat.even_pow' two_ne_zero).mpr hq2).add_one
  have hcop : Nat.Coprime (q ^ 12) ((q - 1) * (q ^ 2 + 1)) := by
    rw [hqdef, ← pow_mul]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h1 : q ^ 12 ∣ Nat.card (CFSG.pCore 2 ↥(⊤ : Subgroup ↥(F4.reeGamma K a))) * q ^ 2 := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [show Nat.card (CFSG.pCore 2 ↥(⊤ : Subgroup ↥(F4.reeGamma K a))) * q ^ 2 *
      ((q - 1) * (q ^ 2 + 1)) = Nat.card (CFSG.pCore 2 ↥(⊤ : Subgroup ↥(F4.reeGamma K a))) *
        szOrd (2 * a + 1) by rw [szOrd]; ring]
    exact hU
  have h2 : q ^ 10 ∣ Nat.card (CFSG.pCore 2 ↥(⊤ : Subgroup ↥(F4.reeGamma K a))) :=
    Nat.dvd_of_mul_dvd_mul_right (show 0 < q ^ 2 by positivity)
      (by rw [show q ^ 10 * q ^ 2 = q ^ 12 by ring]; exact h1)
  exact Nat.le_of_dvd Nat.card_pos h2

theorem szBound_of_isParabolic2
    {G : Type} [Group G] [Finite G] {X P : Subgroup G} {f : ℕ} (hX : Is2F4 f ↥X)
    (hP : IsParabolic2 X P) : OrdCond (SzBound f) (perfectCore P) := by
  refine ordCond_of_subgroupOf hP fun Pa hpa _ => ?_
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  refine ordCond_of_map_equiv e ?_
  by_cases hne : Pa.map e.toMonoidHom = ⊤
  · rw [hne]
    exact szBound_top ha hK
  · refine ordCond_of_parabolic (isSylowTwoOf_subgroupOf_top hUsyl)
      (large_Ree_residualOvergroupsAt hK) (szBound_one (by omega)) (fun j => ?_)
      (isParabolic2_top_map_equiv e hpa) hne
    refine ordCond_subgroupOf_of (reeParabolic_le F4 K a _) ?_
    rw [reeParabolic_singleton (t := F4) (K := K) (a := a)]
    exact szBound_f4 ha hK _

theorem f4SzParabolicFact_holds :
    F4SzParabolicFact := by
  intro G _ _ X P B f hX hP hB hSz
  subst hB
  obtain ⟨-, a, -, F, _, _, hf, hF, ⟨e⟩⟩ := hSz
  subst hf
  have hq : Nat.card (ModO2 (perfectCore P)) = szOrd (2 * a + 1) := by
    rw [Nat.card_congr e.toEquiv, suzuki_order hF]
  have hcard : Nat.card ↥(perfectCore P) =
      Nat.card (CFSG.pCore 2 ↥(perfectCore P)) * szOrd (2 * a + 1) := by
    rw [← hq, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  exact szBound_of_isParabolic2 hX hP hcard

end CFSG.Quasithin.H13.NQCat.F4SzPar

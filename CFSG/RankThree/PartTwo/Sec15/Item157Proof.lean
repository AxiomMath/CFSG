module

public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof157

theorem factorization_three_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : ¬ 3 ∣ b) :
    (a * b).factorization 3 = a.factorization 3 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h,
    add_zero]

variable {G : Type} [Group G] [Finite G]

theorem factorization_three_eq_of_not_dvd {X K : Subgroup G} (hXK : X ≤ K)
    (h : ¬ 3 ∣ X.relIndex K) : (Nat.card K).factorization 3 = (Nat.card X).factorization 3 := by
  have h1 := Subgroup.relIndex_mul_card X K
  rw [inf_of_le_left hXK] at h1
  have hr : X.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [← h1, mul_comm, factorization_three_mul Nat.card_pos.ne' hr h]

theorem not_dvd_relIndex_of_factorization_three_eq {X K : Subgroup G} (hXK : X ≤ K)
    (h : (Nat.card K).factorization 3 = (Nat.card X).factorization 3) :
    ¬ 3 ∣ X.relIndex K := by
  have h1 := Subgroup.relIndex_mul_card X K
  rw [inf_of_le_left hXK] at h1
  have hr : X.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  intro h3
  have hpos := Nat.Prime.factorization_pos_of_dvd Nat.prime_three hr h3
  rw [← h1, Nat.factorization_mul hr Nat.card_pos.ne', Finsupp.add_apply] at h
  omega

omit [Group G] [Finite G] in
theorem factorization_three_card_quotient {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q)
    (hN : ¬ 3 ∣ Nat.card N) :
    (Nat.card Q).factorization 3 = (Nat.card (Q ⧸ N)).factorization 3 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
    factorization_three_mul Nat.card_pos.ne' Nat.card_pos.ne' hN]

end Proof157

open Proof157

theorem claim157EY_of (h142 : Item142AllS14) : Claim157EY := by
  intro G _ _ A c L h Y hY ⟨φ⟩ c' L' hc' hL' ⟨ψ⟩ hdec E hEle hEab hE27 _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : Sec14Std G A c' L' :=
    { h.toSec14Std with zpowers_mem_omegaA := hc', mem_lA := hL' }
  have hD' := hS'.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c' : Set G) with hH
  set D := deltaZero A (lB A) (Y ⊓ H) with hDdef
  set K := delta A (lB A) H with hKdef
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hU : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hDY : D ≤ Y := (deltaZero_le _).trans inf_le_left
  have hDK : D ≤ K := sSup_le fun Q hQ => le_delta hQ.1.1 (hQ.2.trans inf_le_right)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_sSup fun Q hQ => hQ.1.1.1.2.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hvD : (Nat.card D).factorization 3 = (Nat.card Y).factorization 3 := by
    have hO : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 Y) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
    have hDO : D ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
      hDY.trans (le_normalizer_pPrimeCoreOf 3 Y)
    have h1 := factorization_three_eq_of_not_dvd le_sup_left
      (not_dvd_relIndex_sup_of_le_normalizer hO hDO)
    rw [sup_comm, ← hdec] at h1
    exact h1.symm
  have hvY : (Nat.card Y).factorization 3 =
      (Nat.card CFSG.Blueprint.NativeSporadic.M12).factorization 3 := by
    have h2 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥Y) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
      rw [hk]
      intro h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    rw [factorization_three_card_quotient (CFSG.pCore 2 ↥Y) h2, Nat.card_congr φ.toEquiv]
  have hvL : (Nat.card L').factorization 3 =
      (Nat.card CFSG.Blueprint.NativeSporadic.M12).factorization 3 := by
    rw [factorization_three_card_quotient (aschbacherSolvableCore 3 ↥L')
      CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore, Nat.card_congr ψ.toEquiv]
  have h3M : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
    rw [KFacts.KS14.card_nativeM12]
    norm_num
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨-, halt⟩ := h142 G A c' L' hS' Qs hQs
  rcases halt with ⟨-, hQsK, -, -⟩ | ⟨hKeq, -⟩
  ·
    exfalso
    have hK3 : ¬ 3 ∣ Nat.card K := by
      have := (isPiSubgroup_piCompl_iff Nat.prime_three Qs).mp hQs.prop.2.1
      rwa [hQsK] at this
    apply hK3
    refine (Nat.dvd_of_factorization_pos ?_).trans (Subgroup.card_dvd_of_le hDK)
    rw [hvD, hvY]
    exact (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3M).ne'
  ·
    have hKeq' : K = L' ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔
        pPrimeCoreOf 3 H := by
      rw [hKdef, ← sup_right_comm]
      exact hKeq
    have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c'} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD'.mem_A)
    have hCH : Subgroup.centralizer ({c'} : Set G) ≤ H :=
      centralizer_singleton_le_normalizer_zpowers c'
    have hCN : Subgroup.centralizer ({c'} : Set G) ≤ Subgroup.normalizer (L' : Set G) :=
      centralizer_le_normalizer_of_three_dvd hS' (three_dvd_card_of_thetaQuot ψ h3M)
    have hR2 : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.centralizer ({c'} : Set G) := (pPrimeCoreOf_le 3 _).trans hCA
    have hvK : (Nat.card K).factorization 3 = (Nat.card L').factorization 3 := by
      have hX : L' ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
          Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
        (sup_le (hD'.le_centralizer.trans hCH) (hR2.trans hCH)).trans
          (le_normalizer_pPrimeCoreOf 3 H)
      rw [hKeq', factorization_three_eq_of_not_dvd le_sup_left
        (not_dvd_relIndex_sup_of_le_normalizer ((Nat.Prime.coprime_iff_not_dvd
          Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 H)) hX),
        factorization_three_eq_of_not_dvd le_sup_left
        (not_dvd_relIndex_sup_of_normalizer_le ((Nat.Prime.coprime_iff_not_dvd
          Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)) (hR2.trans hCN))]
    have hidx : ¬ 3 ∣ D.relIndex K :=
      not_dvd_relIndex_of_factorization_three_eq hDK (by rw [hvK, hvL, hvD, hvY])
    have hidx' : ¬ 3 ∣ (A ⊔ D).relIndex (A ⊔ K) := fun h3 =>
      hidx (h3.trans (relIndex_sup_dvd_of_le_normalizer hDK hAD hAK))
    have hLK : L' ≤ K := by
      rw [hKeq']
      exact le_sup_left.trans le_sup_left
    have hMU : A ⊔ D ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
      sup_le (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (hDY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
    exact mem_partTwoE_of_not_dvd_relIndex (sup_le_sup_left hDK A) hidx' hU
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) hMU
      (hEle.trans (inf_le_left.trans (sup_le_sup_left hLK A))) hEab hE27

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_7_of_item142
    (h137 : Item137) (h142 : Item142AllS14) (h134 : Item134) (h135 : Item135)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥)
    (hPGL : KFacts.KS15Z3PGLNonabelian)
    (hM12s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M12)
    (hM12L3 : ∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt CFSG.Blueprint.NativeSporadic.M12 p f)
    (hM12A : IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 10)))
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h148 : Item148 A (lB A)) : Item157 A (lB A) :=
  rank3II_15_7_of h137 h134 h135 h48 h415 hJ2c hPGL hM12s hM12L3 hM12A (claim157EY_of h142) h
    h148

end CFSG.RankThree.PartTwo.Sec15

module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionQD32
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionGeometry
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionCD
public import CFSG.RankThree.PartOne.S9.StatementsSylow

public section

namespace CFSG.RankThree.PartOne.Sec9Excl

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly.RankThreeEven
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem exclusion_core (hRTST : ResidualTwoSubgroupTransfer)
    (hQDG : QuaternionDihedralOddCentralizerGeometry)
    (hQDA : QuaternionDihedralAutomorphismPrimeSupport) (hI2 : TwoLocalRankTwoOddCoreAction)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (hev : CFSG.Assembly.evenRank G ≤ 3)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) (hloc : localRank q G ≤ 2)
    {A R D : Subgroup G} {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hAel : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 125)
    (hRθ : R ≤ inSubgroup (aschbacherSolvableCore 5) (normalizer (zpowers c : Set G)))
    (hAR : A ≤ normalizer (R : Set G)) (hRA : ⁅R, A⁆ = R) (hRQD : Nonempty (R ≃* QD32))
    (hBcard : Nat.card (A ⊓ centralizer (R : Set G) : Subgroup G) = 25)
    (hcR : c ∈ centralizer (R : Set G))
    (hD : D = omegaOne q (inSubgroup (pCore q) (normalizer (zpowers c : Set G))))
    (hRD : R ⊓ centralizer (D : Set G) = ⊥) (hQD : IsQDShape q D) : False := by
  have h5 : Nat.Prime 5 := by norm_num
  have hq2 : q ≠ 2 := by omega
  have hq5' : q ≠ 5 := by omega
  have : Fact (Nat.Prime 5) := ⟨h5⟩
  have hcomm : IsMulCommutative A := hAel.toIsMulCommutative
  have hc5 : orderOf c = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 5) c hcA) hc1
  set H : Subgroup G := normalizer (zpowers c : Set G) with hH
  have hAH : A ≤ H := le_normalizer_zpowers_of_mem hcA
  set B : Subgroup G := A ⊓ centralizer (R : Set G) with hB
  have hcB : c ∈ B := ⟨hcA, hcR⟩
  have hBA : B ≤ A := inf_le_left
  have hBR : B ≤ centralizer (R : Set G) := inf_le_right
  have hRH : R ≤ H := hRθ.trans (Subgroup.map_subtype_le _)
  set Oq : Subgroup G := inSubgroup (pCore q) H with hOq
  have hOqq : IsPGroup q Oq := isPGroup_inSubgroup_pCore q H
  have hHOq : H ≤ normalizer (Oq : Set G) := le_normalizer_inSubgroup_pCore q H
  have hDOq : D ≤ Oq := by rw [hD]; exact omegaOne_le q Oq
  have hDq : IsPGroup q D := hOqq.to_le hDOq
  have hDH : D ≤ H := hDOq.trans (Subgroup.map_subtype_le _)
  have hHD : H ≤ normalizer (D : Set G) := by
    rw [hD]
    exact fun h hh => mem_normalizer_omegaOne (hHOq hh)
  have hRDn : R ≤ normalizer (D : Set G) := hRH.trans hHD
  have hADn : A ≤ normalizer (D : Set G) := hAH.trans hHD
  have hBDn : B ≤ normalizer (D : Set G) := hBA.trans hADn
  have hfrat : ⁅R, inSubgroup frattini D⁆ = ⊥ :=
    commutator_inSubgroup_frattini_eq_bot hq hRDn hADn hRA hQD
  have hcDcomm : ∀ d ∈ D, c * d = d * c := fun d hd =>
    mul_comm_of_isPGroup h5 hq (Ne.symm hq5') hc5 hDq hDH
      (hHD (mem_normalizer_zpowers_self c)) hd
  have e := hRQD.some
  obtain ⟨hRcard, hRpg⟩ := card_isPGroup_of_qd32 e
  obtain ⟨z, hzR, hz1, hzc, -⟩ := exists_central_involution e
  obtain ⟨r, hrR, hr2, hrc⟩ := exists_noncentral_involution e
  obtain ⟨Y, hYF, hYc, hBY, hzY, hrank, hP, hnt⟩ := exists_good_line hQDG hchar hq hq2 hRQD hRDn
    hBDn hBR hRD hfrat hQD hDq hzR hz1 hzc hrR hr2 hrc
  set M : Subgroup G := normalizer (Y : Set G) with hM
  have hMtop : M ≠ ⊤ := normalizer_ne_top_of_simple hnonab hq hYc
  have hZ : Subgroup.center G = ⊥ := center_eq_bot_of_simple hnonab
  have hA3 : Nat.card A = 5 ^ 3 := by rw [hAcard]; norm_num
  have hB2 : Nat.card (A ⊓ centralizer (R : Set G) : Subgroup G) = 5 ^ 2 := by
    rw [hBcard]; norm_num
  obtain ⟨-, hRM⟩ := hRTST G hZ hK hev 5 h5 (by norm_num) A hAel hA3 c hcA hc1 R hRθ hRpg hAR hRA
    hB2 hcR
  have hzθ : z ∈ inSubgroup (aschbacherSolvableCore 5) M := hRM M hBY hMtop ⟨hzR, hzY⟩
  have hMθ : M ≤ normalizer ((inSubgroup (aschbacherSolvableCore 5) M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype M (aschbacherSolvableCore 5 M)
  set P : Subgroup G := D ⊓ centralizer (Y : Set G) with hPdef
  set F : Subgroup G := D ⊓ centralizer ({r} : Set G) with hFdef
  set E : Subgroup G := F ⊓ centralizer (Y : Set G) with hEdef
  set K : Subgroup G := inSubgroup (pCore 2) (centralizer ({r} : Set G)) with hKdef
  set V : Subgroup G := K ⊓ centralizer (Y : Set G) with hVdef
  have hPM : P ≤ M := inf_le_right.trans (centralizer_le_normalizer _)
  have hPθ : P ≤ inSubgroup (aschbacherSolvableCore 5) M := by
    have := commutator_le_of_le_normalizer (T := inSubgroup (aschbacherSolvableCore 5) M)
      (X := P) (W := zpowers z) (hPM.trans hMθ) (Subgroup.zpowers_le.mpr hzθ)
    rwa [← hP] at this
  have hEP : E ≤ P := inf_le_inf_right _ inf_le_left
  have hED : E ≤ D := hEP.trans inf_le_left
  have hEq : IsPGroup q E := hDq.to_le hED
  have hEθ : E ≤ inSubgroup (aschbacherSolvableCore 5) M := hEP.trans hPθ
  have hK2 : IsPGroup 2 K := isPGroup_inSubgroup_pCore 2 _
  have hV2 : IsPGroup 2 V := hK2.to_le inf_le_left
  have hCr : centralizer ({r} : Set G) ≤ normalizer (K : Set G) :=
    le_normalizer_inSubgroup_pCore 2 _
  have hECr : E ≤ centralizer ({r} : Set G) := (inf_le_left.trans inf_le_right)
  have hEV : E ≤ normalizer (V : Set G) := fun e he =>
    mem_normalizer_inf (hCr (hECr he))
      (mem_normalizer_centralizer (centralizer_le_normalizer _ he.2))
  set U : Subgroup G := ⁅V, E⁆ with hUdef
  have hUV : U ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hEV
  have hU2 : IsPGroup 2 U := hV2.to_le hUV
  have hqV : ¬ q ∣ Nat.card V := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hV2
    rw [ha]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  have hUU : ⁅U, E⁆ = U :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent q hq E V hEq hqV hEV
  have hUM : U ≤ M := hUV.trans (inf_le_right.trans (centralizer_le_normalizer _))
  have hUθ : U ≤ inSubgroup (aschbacherSolvableCore 5) M := by
    have := commutator_le_of_le_normalizer (T := inSubgroup (aschbacherSolvableCore 5) M)
      (X := U) (W := E) (hUM.trans hMθ) hEθ
    rwa [hUU] at this
  have hEU : E ≤ normalizer (U : Set G) := Subgroup.normalizer_commutator_ge_right V E
  have hcM : c ∈ M := hBY hcB
  have hcr : c ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcR r hrR).symm
  have hcV : c ∈ normalizer (V : Set G) :=
    mem_normalizer_inf (hCr hcr) (mem_normalizer_centralizer (hBY hcB))
  have hcE : c ∈ centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => (hcDcomm e (hED he)).symm
  have hcU : c ∈ normalizer (U : Set G) :=
    mem_normalizer_commutator hcV (centralizer_le_normalizer _ hcE)
  have hUne : U ≠ ⊥ := hnt
  have hKD : K ⊓ D = ⊥ := inf_eq_bot_of_isPGroup Nat.prime_two hq (Ne.symm hq2) hK2 hDq
  have hz5 : IsPGroup 5 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc5, pow_one])
  have hU5 : ¬ 5 ∣ Nat.card U := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU2
    rw [ha]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq h5 Nat.prime_two).mp (h5.dvd_of_dvd_pow h)
    omega
  have hzU : zpowers c ≤ normalizer (U : Set G) := Subgroup.zpowers_le.mpr hcU
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    5 h5 (zpowers c) U hz5 hU5 hzU
  have hnt' : ⁅⁅U, zpowers c⁆, E⁆ ≠ ⊥ := by
    intro hbot
    have h1 : ⁅U, zpowers c⁆ ≤ centralizer (E : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have h2 : U ⊓ centralizer ((zpowers c : Subgroup G) : Set G) ≤ centralizer (E : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (mul_comm_of_inf_eq_bot hKD ((hUV.trans inf_le_left) hu.1) (hED he)
        (hHD (centralizer_le_normalizer _ hu.2)) (hCr (hECr he))).symm
    have hle : U ≤ centralizer (E : Set G) :=
      calc U = ⁅U, zpowers c⁆ ⊔ U ⊓ centralizer ((zpowers c : Subgroup G) : Set G) := hfac
        _ ≤ centralizer (E : Set G) := sup_le h1 h2
    have h3 : ⁅U, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [hUU] at h3
    exact hUne h3
  obtain ⟨r', hr', X, hXP, hXc, hXe, hXr⟩ := exists_elemAbelian_of_three_le_pRank hq hrank
  exact final_contradiction hI2 hQDA hq hq5 hloc hc5 hcM hUθ hEθ hU2 hEq hcU hcE hEU hr'
    (hXP.trans hPθ) hXc hXe hXr hnt'

end CFSG.RankThree.PartOne.Sec9Excl

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.GroupTheory CFSG.Assembly.RankThreeEven

theorem exceptionalSmallActionExclusion_of (hRTST : ResidualTwoSubgroupTransfer)
    (hQDG : QuaternionDihedralOddCentralizerGeometry)
    (hQDA : QuaternionDihedralAutomorphismPrimeSupport) (hI2 : TwoLocalRankTwoOddCoreAction) :
    ExceptionalSmallActionExclusion := by
  intro G _ _ _ hnonab hK hchar hev q hq hq5 hloc A R D c hcA hc1
    ⟨hAel, hAcard, hRθ, hAR, hRA, hRQD, hBcard, hcR, hD, hRD, hQD⟩
  exact Sec9Excl.exclusion_core hRTST hQDG hQDA hI2 hnonab hK hchar hev hq hq5 hloc hcA hc1 hAel
    hAcard hRθ hAR hRA hRQD hBcard hcR hD hRD hQD

end CFSG.RankThree.PartOne

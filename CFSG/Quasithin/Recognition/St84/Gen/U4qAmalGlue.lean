module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalModel
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDC
import CFSG.Quasithin.Recognition.St84.Gen.U4qModel
import CFSG.Quasithin.Recognition.St84.Gen.AmalGlueDC
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.EmptyFaithful.SBd8Psl2
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverA
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Am

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique CFSG.Quasithin.H13
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem isL2Quot_of_surjective {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n) {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) : IsL2Quot n (oTwoQuot ↥L) := by
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  exact CFSG.Quasithin.F146Field.isL2Quot_of_isPSL
    (SBd8.Psl2.isPSL_of_statedSL hn (by rw [Nat.card_eq_fintype_card]; exact hF)
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)))

theorem U4qLocalData.hyp111R (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f) :
    Hyp111R L1 L2 S := by
  obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := hD.twoNat_left
  obtain ⟨K, _, _, hK, α₂, hα₂, hker₂, -⟩ := hD.omega_right
  exact hyp111R_of_isL2Quot (by omega) (by omega) hH
    (isL2Quot_of_surjective hf hF α hα hker) (isL2Quot_of_surjective (by omega) hK α₂ hα₂ hker₂)

theorem amalgamIso_psu4_of_mulEquiv (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {K : Type} [Field K]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(parP hU))
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L2 ↔ ((ψ₁ x : ↥(parP hU)) : hypSU hU 2 0) ∈ radQ2 hU)
    (hψ₁N : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ₁ x : ↥(parP hU)) : hypSU hU 2 0) ∈
        Subgroup.normalizer (hypUnitriangular hU 2 0 : Set (hypSU hU 2 0)))
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(parP2 hU))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L2 ↔ ((ψ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈ radQ2 hU)
    (hψ₂N : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈
        Subgroup.normalizer (hypUnitriangular hU 2 0 : Set (hypSU hU 2 0))) :
    Nonempty ((RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)).Iso
      (RankTwoAmalgam.ofSubgroups (parP hU) (parP2 hU))) := by
  classical
  let Y := hypSU hU 2 0
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  have hR : Hyp111R L1 L2 S := hD.hyp111R hf hH
  have hbigB1 : bigB L1 L2 S = P1 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := bigB_eq_parabolic_inf hR
    rwa [inf_eq_left.mpr (hD.le_left hH hS)] at h
  have hbigB2 : bigB L1 L2 S = P2 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := bigB_eq_parabolic_inf hR.symm
    rw [bigB_comm L1 L2 S, inf_eq_left.mpr (hD.le_right hH hS)] at h
    exact h
  have hN : Subgroup.normalizer (hypUnitriangular hU 2 0 : Set Y) = parP hU ⊓ parP2 hU := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular hU
      (by norm_num) (by norm_num), parP_inf_parP2_eq_u4 hU]
  have hcore2 : pCoreOf 2 (parP2 hU) = radQ2 hU := U4qModel.pCoreOf_parP2_eq hU hf
  have hB1 : ∀ x : ↥P2, (x : G) ∈ P1 ↔ ((ψ₂ x : ↥(parP2 hU)) : Y) ∈ parP hU := by
    intro x
    constructor
    · intro hx
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [← parabolic_inf_parabolic hR]
        exact ⟨hx, x.2⟩
      rw [hbigB2] at hxB
      have hψ := (hψ₂N x).mp hxB.2
      rw [hN] at hψ
      exact hψ.1
    · intro hx
      have hψ : ((ψ₂ x : ↥(parP2 hU)) : Y) ∈
          Subgroup.normalizer (hypUnitriangular hU 2 0 : Set Y) := by
        rw [hN]
        exact ⟨hx, (ψ₂ x).2⟩
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [hbigB2]
        exact ⟨x.2, (hψ₂N x).mpr hψ⟩
      exact (le_sup_right : bigB L1 L2 S ≤ P1) hxB
  have hB2 : ∀ x : ↥P1, (x : G) ∈ P2 ↔ ((ψ₁ x : ↥(parP hU)) : Y) ∈ parP2 hU := by
    intro x
    constructor
    · intro hx
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [← parabolic_inf_parabolic hR]
        exact ⟨x.2, hx⟩
      rw [hbigB1] at hxB
      have hψ := (hψ₁N x).mp hxB.2
      rw [hN] at hψ
      exact hψ.2
    · intro hx
      have hψ : ((ψ₁ x : ↥(parP hU)) : Y) ∈
          Subgroup.normalizer (hypUnitriangular hU 2 0 : Set Y) := by
        rw [hN]
        exact ⟨(ψ₁ x).2, hx⟩
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [hbigB1]
        exact ⟨x.2, (hψ₁N x).mpr hψ⟩
      exact (le_sup_right : bigB L1 L2 S ≤ P2) hxB
  have hQ1 : ∀ x : ↥P2, (x : G) ∈ pCoreOf 2 L2 ↔
      ((ψ₂ x : ↥(parP2 hU)) : Y) ∈ pCoreOf 2 (parP2 hU) := by
    intro x
    rw [hcore2]
    exact hψ₂Q x
  have hQ1' : ∀ x : ↥P1, (x : G) ∈ pCoreOf 2 L2 ↔
      ((ψ₁ x : ↥(parP hU)) : Y) ∈ pCoreOf 2 (parP2 hU) := by
    intro x
    rw [hcore2]
    exact hψ₁Q x
  have hiso : Nonempty ((RankTwoAmalgam.ofSubgroups P2 P1).Iso
      (RankTwoAmalgam.ofSubgroups (parP2 hU) (parP hU))) :=
    amalgam_iso_of_dcProp (dcProp_parP2_parP hU hf) ψ₂ ψ₁ hB1 hB2 hQ1 hQ1'
  exact ⟨ofSubgroupsIsoSwap hiso.some⟩

theorem isAmalgamOfGroup_psu4_of_mulEquiv (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) {K : Type} [Field K]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
    (ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(parP hU))
    (hψ₁Q : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L2 ↔ ((ψ₁ x : ↥(parP hU)) : hypSU hU 2 0) ∈ radQ2 hU)
    (hψ₁N : ∀ x : ↥(L1 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ₁ x : ↥(parP hU)) : hypSU hU 2 0) ∈
        Subgroup.normalizer (hypUnitriangular hU 2 0 : Set (hypSU hU 2 0)))
    (ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(parP2 hU))
    (hψ₂Q : ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L2 ↔ ((ψ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈ radQ2 hU)
    (hψ₂N : ∀ x : ↥(L2 ⊔ bigB L1 L2 S), (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      ((ψ₂ x : ↥(parP2 hU)) : hypSU hU 2 0) ∈
        Subgroup.normalizer (hypUnitriangular hU 2 0 : Set (hypSU hU 2 0))) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 f) :=
  ⟨hypSU hU 2 0, inferInstance, isLieOverTwo_psu4 hU, hypUnitriangular hU 2 0, parP hU, parP2 hU,
    isYAmalgamPair_parP_parP2 hU,
    amalgamIso_psu4_of_mulEquiv hf hH hD hS hU ψ₁ hψ₁Q hψ₁N ψ₂ hψ₂Q hψ₂N⟩

end CFSG.Quasithin.F112R.St84

end

module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapIdxFive
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSp4ParAux2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)

private theorem wcgapsr_central {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    ∀ a ∈ (Q₂ F ⊓ Q₁ F : Subgroup (StatedSp 2 F)),
      ∀ s ∈ (unipotent 2 F : Subgroup (StatedSp 2 F)), a * s = s * a := by
  haveI : CharP F 2 := charP_two_of_card_eq_four hF
  intro a ha s hs
  have haQ1 : a ∈ radical F := by
    rw [← Q₁_eq_radical]
    exact ha.2
  obtain ⟨C, hC, haC⟩ := haQ1
  have hQ2 : mat a (Sum.inl 1) (Sum.inr 1) = 0 := (mem_Q₂_iff.mp ha.1).2
  have hC11 : C 1 1 = 0 := by
    have h2 : mat (tau hC) (Sum.inl 1) (Sum.inr 1) = 0 := by
      rw [← haC]
      exact hQ2
    have h3 := entry_of_mem_sylS (F := F) (g := tau hC) (a := 0) (mat_tau hC)
    rw [h3] at h2
    exact h2
  have hCe : C = sym2 (C 0 0) (C 0 1) 0 := by
    simpa [hC11] using eq_sym2 hC
  have haeq : a = tau (sym2_transpose (C 0 0) (C 0 1) 0) := by
    rw [haC]
    exact tau_congr hC (sym2_transpose (C 0 0) (C 0 1) 0) hCe
  have haU : a ∈ unipotent 2 F := Q₂_le_sylS ha.1
  obtain ⟨-, -, -, -, -, -, -, hcenter, -⟩ :=
    unique_symplectic_four_Sylow_center (K := F) 4 hF
  have hmem : (⟨a, haU⟩ : ↥(unipotent 2 F)) ∈ Subgroup.center (unipotent 2 F) :=
    (hcenter ⟨a, haU⟩).mpr ⟨C 0 0, C 0 1, haeq⟩
  exact (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hmem ⟨s, hs⟩)).symm

private theorem wcgapsr_isMaxParabolicMod {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (i : Fin 2) :
    IsMaxParabolicMod (⊥ : Subgroup (StatedSp 2 F)) ⊤ (Q2 F i) := by
  haveI : CharP F 2 := charP_two_of_card_eq_four hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  have hU2 : IsPGroup 2 (unipotent 2 F : Subgroup (StatedSp 2 F)) := by
    rw [← hP]
    exact P.isPGroup'
  have hUidx : ¬ 2 ∣ (unipotent 2 F : Subgroup (StatedSp 2 F)).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right, ← hP]
    exact P.not_dvd_index
  have hcoat : IsCoatom (Q2 F i) := by
    fin_cases i
    · exact isCoatom_P₂
    · exact isCoatom_P₁
  refine ⟨bot_le, lt_of_le_of_ne le_top hcoat.1, fun Y hY _ => hcoat.2 Y hY,
    unipotent 2 F, bot_le, le_top, ?_, hUidx, ?_⟩
  · intro s hs
    obtain ⟨k, hk⟩ := hU2 ⟨s, hs⟩
    exact ⟨k, Subgroup.mem_bot.mpr (Subtype.ext_iff.mp hk)⟩
  · rw [top_inf_eq, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent]
    exact CFSG.QuasithinUnique.Vol2Native.A312L.borelSubgroup_le_Q2 i

theorem rankTwoParabData_unipotent_sp4 {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    RankTwoParabData (unipotent 2 F : Subgroup (StatedSp 2 F)) := by
  haveI : CharP F 2 := charP_two_of_card_eq_four hF
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKeq0 : oddResMod (⊥ : Subgroup (StatedSp 2 F)) (Q2 F 0) = L₂ F := by
    rw [wcgapsq_oddResMod_bot_eq_oTwoPrime, show Q2 F 0 = P₂ F from rfl, oTwo_P₂]
  have hKeq1 : oddResMod (⊥ : Subgroup (StatedSp 2 F)) (Q2 F 1) = L₁ F := by
    rw [wcgapsq_oddResMod_bot_eq_oTwoPrime, show Q2 F 1 = P₁ F from rfl, oTwo_P₁]
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  have hU2 : IsPGroup 2 (unipotent 2 F : Subgroup (StatedSp 2 F)) := by
    rw [← hP]
    exact P.isPGroup'
  have hUidx : ¬ 2 ∣ (unipotent 2 F : Subgroup (StatedSp 2 F)).relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right, ← hP]
    exact P.not_dvd_index
  have hUK0 : (unipotent 2 F : Subgroup (StatedSp 2 F)) ≤ L₂ F := by
    rw [← hKeq0, wcgapsq_oddResMod_bot_eq_oTwoPrime]
    exact le_oTwo (unipotent_le_borelSubgroup.trans
      (CFSG.QuasithinUnique.Vol2Native.A312L.borelSubgroup_le_Q2 0)) hU2
  have hUK1 : (unipotent 2 F : Subgroup (StatedSp 2 F)) ≤ L₁ F := by
    rw [← hKeq1, wcgapsq_oddResMod_bot_eq_oTwoPrime]
    exact le_oTwo (unipotent_le_borelSubgroup.trans
      (CFSG.QuasithinUnique.Vol2Native.A312L.borelSubgroup_le_Q2 1)) hU2
  have hQn0 : ((Q₂ F).subgroupOf (L₂ F)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Q₂_le_L₂).mpr L₂_le_normalizer_Q₂
  have hQn1 : ((Q₁ F).subgroupOf (L₁ F)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Q₁_le_L₁).mpr L₁_le_normalizer_Q₁
  have hsurj0 := wcgapsq_oTwoMod_eq_of_surj (M := StatedSp 2 F) (U := unipotent 2 F)
    (K := L₂ F) (Q := Q₂ F) (F := F) hF hU2 hUK0 Q₂_le_sylS hQn0
    (wcgapsq_leviL0 (F := F)) wcgapsq_leviL0_surjective wcgapsq_leviL0_ker
  have hsurj1 := wcgapsq_oTwoMod_eq_of_surj (M := StatedSp 2 F) (U := unipotent 2 F)
    (K := L₁ F) (Q := Q₁ F) (F := F) hF hU2 hUK1 Q₁_le_sylS hQn1
    (wcgapsq_leviL1 (F := F)) wcgapsq_leviL1_surjective wcgapsq_leviL1_ker
  have hcore0 : oTwoMod (⊥ : Subgroup (StatedSp 2 F)) (oddResMod ⊥ (Q2 F 0)) = Q₂ F := by
    rw [hKeq0]
    exact hsurj0.1
  have hcore1 : oTwoMod (⊥ : Subgroup (StatedSp 2 F)) (oddResMod ⊥ (Q2 F 1)) = Q₁ F := by
    rw [hKeq1]
    exact hsurj1.1
  have hidx0 : (L₂ F ⊓ (⊤ ⊓ normalizer (unipotent 2 F : Set (StatedSp 2 F)))).relIndex
      (L₂ F) = 5 :=
    relIndex_normalizer_eq_five_of_surj_sl2 (M := StatedSp 2 F) (U := unipotent 2 F)
      (K := L₂ F) (Q := Q₂ F) (F := F) hF hU2 hUK0 Q₂_le_sylS hUidx
      (wcgapsq_leviL0 (F := F)) wcgapsq_leviL0_surjective wcgapsq_leviL0_ker
  have hidx1 : (L₁ F ⊓ (⊤ ⊓ normalizer (unipotent 2 F : Set (StatedSp 2 F)))).relIndex
      (L₁ F) = 5 :=
    relIndex_normalizer_eq_five_of_surj_sl2 (M := StatedSp 2 F) (U := unipotent 2 F)
      (K := L₁ F) (Q := Q₁ F) (F := F) hF hU2 hUK1 Q₁_le_sylS hUidx
      (wcgapsq_leviL1 (F := F)) wcgapsq_leviL1_surjective wcgapsq_leviL1_ker
  refine ⟨![Q2 F 0, Q2 F 1], ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using wcgapsr_isMaxParabolicMod (F := F) hF 0
    · simpa using wcgapsr_isMaxParabolicMod (F := F) hF 1
  · intro i
    fin_cases i
    · show (unipotent 2 F : Subgroup (StatedSp 2 F)) ≤ oddResMod ⊥ (Q2 F 0)
      rw [wcgapsq_oddResMod_bot_eq_oTwoPrime]
      exact le_oTwo (unipotent_le_borelSubgroup.trans
        (CFSG.QuasithinUnique.Vol2Native.A312L.borelSubgroup_le_Q2 0)) hU2
    · show (unipotent 2 F : Subgroup (StatedSp 2 F)) ≤ oddResMod ⊥ (Q2 F 1)
      rw [wcgapsq_oddResMod_bot_eq_oTwoPrime]
      exact le_oTwo (unipotent_le_borelSubgroup.trans
        (CFSG.QuasithinUnique.Vol2Native.A312L.borelSubgroup_le_Q2 1)) hU2
  · intro i
    fin_cases i
    · show HasQuotShape (oddResMod ⊥ (Q2 F 0))
        (oTwoMod ⊥ (oddResMod ⊥ (Q2 F 0)) : Set (StatedSp 2 F)) (fun X _ => IsL2 X 2)
      rw [hKeq0]
      exact hsurj0.2
    · show HasQuotShape (oddResMod ⊥ (Q2 F 1))
        (oTwoMod ⊥ (oddResMod ⊥ (Q2 F 1)) : Set (StatedSp 2 F)) (fun X _ => IsL2 X 2)
      rw [hKeq1]
      exact hsurj1.2
  · intro i
    fin_cases i
    · show (oddResMod ⊥ (Q2 F 0) ⊓ (⊤ ⊓ normalizer (unipotent 2 F :
          Set (StatedSp 2 F)))).relIndex (oddResMod ⊥ (Q2 F 0)) = 5
      rw [hKeq0]
      exact hidx0
    · show (oddResMod ⊥ (Q2 F 1) ⊓ (⊤ ⊓ normalizer (unipotent 2 F :
          Set (StatedSp 2 F)))).relIndex (oddResMod ⊥ (Q2 F 1)) = 5
      rw [hKeq1]
      exact hidx1
  · intro a ha ha1 s hs
    have ha0 : a ∈ Q₂ F := by
      have h := ha
      change a ∈ oTwoMod ⊥ (oddResMod ⊥ (Q2 F 0)) at h
      rwa [hcore0] at h
    have ha1' : a ∈ Q₁ F := by
      have h := ha1
      change a ∈ oTwoMod ⊥ (oddResMod ⊥ (Q2 F 1)) at h
      rwa [hcore1] at h
    exact wcgapsr_central (F := F) hF a ⟨ha0, ha1'⟩ s hs

end CFSG.LocalAnalysis.WeakClosure81

end


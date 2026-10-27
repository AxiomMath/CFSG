module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint


theorem funSet_eq_singleton_of_degree_three
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) (hadm : StatedLieAdmissible t 3 p f)
    (hX : LieModel X t 3 p f) (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) = {K} := by
  have hFT : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  have hA1 : ¬ (t = .PSL ∧ 3 = 2) := by simp
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX hA1 hK.1
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t 3 p f hp.out hp2 hFT hadm X hX
  obtain ⟨R, hR, hKR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp.out hp2 hadm hX hFT hA1 hL2 ψ hψ hker hK.1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ LieModel (X ⧸ center X) t n p e :=
    ⟨t, 3, f, hadm, rfl, hX.quotient_center hZ⟩
  ext J
  constructor
  · intro hJ
    rw [Set.mem_singleton_iff]
    by_contra hne
    obtain ⟨S, hS, hJS, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX hFT hA1 hL2 ψ hψ hker hJ.1
    have hneRS : R ≠ S := fun h => hne (hJS.trans (h ▸ hKR.symm))
    have hcomm := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hK hJ (Ne.symm hne)
    have hc : Commutes (R.map ψ) (S.map ψ) := by
      rw [← hKR, ← hJS]
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
    exact no_commuting_fund_three hp2 hadm ht rfl hR hS hneRS
      (commutes_modelFund_of_commutes_map hp2 hFT hadm ψ hker hR hc)
  · intro hJ
    rw [Set.mem_singleton_iff] at hJ
    exact hJ ▸ hK

theorem centralizingLayer_funSet_eq_top_of_degree_three
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) (hadm : StatedLieAdmissible t 3 p f)
    (hX : LieModel X t 3 p f) (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = ⊤ := by
  have hsingle := funSet_eq_singleton_of_degree_three hp2 ht hadm hX P hK
  have hΓ : {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ K ∧ x ∈ L} = ∅ := by
    ext x
    simp [hsingle]
  have hgen : omegaGen {L : Subgroup X | IsFundamentalOver (p ^ f) L} = ⊤ :=
    ih8_omegaGen_eq_top (fun g L hL => isFundamentalOver_map_mulEquiv (MulAut.conj g) hL)
      hK.1 (IsFundamentalOver.ne_bot hK.1)
  rw [hΓ]
  have hmembers : centralizingMembers {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      (∅ : Set X) = {L : Subgroup X | IsFundamentalOver (p ^ f) L} := by
    ext L
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => hy.elim⟩
  rw [centralizingLayer, hmembers]
  exact hgen

theorem lieModel_centralizingLayer_quotient_of_degree_three
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .PSL ∨ t = .PSU) (hadm : StatedLieAdmissible t 3 p f)
    (hX : LieModel X t 3 p f) (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    let A := centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L}
    LieModel (A ⧸ center A) t 3 p f := by
  intro A
  have hAtop : A = ⊤ := centralizingLayer_funSet_eq_top_of_degree_three hp2 ht hadm hX P hK
  obtain ⟨hZ, _, _, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) hK.1
  let e : X ≃* A := Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hAtop.symm)
  exact (hX.quotient_center hZ).quotient_center_of_mulEquiv e

end CFSG.LocalAnalysis.UniquenessCase.UC22

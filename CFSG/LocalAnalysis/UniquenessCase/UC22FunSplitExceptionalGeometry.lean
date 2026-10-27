module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwoModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
public import CFSG.ClassicalInvolution.SmallCases.G2SModel
public import CFSG.ClassicalInvolution.ModelFacts.FundTwinCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD


theorem involution_eq_of_commutes_g2d4_modelFund
    {p e n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4)
    {R A : Subgroup (modelUniv t n p e hp.out).K}
    (hR : R ∈ ModelFund p t n e) (hc : Commutes R A)
    {z u : (modelUniv t n p e hp.out).K}
    (hz : IsUniqueInvolution R z) (hu : IsUniqueInvolution A u) : u = z := by
  have huc : u ∈ centralizer (R : Set (modelUniv t n p e hp.out).K) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr => hc r hr u hu.mem
  have hfg := CFSG.ClassicalInvolution.NDB.G2S.fg0Model_of_tag hp2 hadm.2.1 ht hR
  have hmem := hfg.1 u huc hu.sq
  exact (hz.unique u (hmem.resolve_left hu.ne_one) hu.sq).resolve_left hu.ne_one

theorem eq_of_commutes_g2d4_modelFund
    {p e n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4)
    {R A B : Subgroup (modelUniv t n p e hp.out).K}
    (hR : R ∈ ModelFund p t n e) (hA : A ∈ ModelFund p t n e)
    (hB : B ∈ ModelFund p t n e) (cRA : Commutes R A) (cRB : Commutes R B) : A = B := by
  have hfund : IsFundTag t := by rcases ht with rfl | rfl <;> trivial
  obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isUniqueInvolution_of_mem_fundamentalSubgroups
    hp2 hfund hadm hR
  obtain ⟨u, hu⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isUniqueInvolution_of_mem_fundamentalSubgroups
    hp2 hfund hadm hA
  obtain ⟨v, hv⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isUniqueInvolution_of_mem_fundamentalSubgroups
    hp2 hfund hadm hB
  have hu' : IsUniqueInvolution A z := involution_eq_of_commutes_g2d4_modelFund hp2 hadm ht hR cRA hz hu ▸ hu
  have hv' : IsUniqueInvolution B z := involution_eq_of_commutes_g2d4_modelFund hp2 hadm ht hR cRB hz hv ▸ hv
  by_contra hAB
  have cAB : Commutes A B := by
    have h := CFSG.ClassicalInvolution.ModelFacts.commutator_eq_bot_of_mem_fundamentalSubgroups
      hp2 hfund hadm hA hB hAB hu' hv'
    exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
  have hnc : ¬ Commutes R R := by
    intro hc
    obtain h | ⟨_, h⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hp2 hfund hadm hR
    · obtain ⟨eR⟩ := h
      obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
        (MonoidHom.id _) (by simp) eR
      exact hab (hc a ha b hb)
    · obtain ⟨eR⟩ := h
      obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
        (MonoidHom.id _) (by simp) eR
      exact hab (hc a ha b hb)
  have hRA : R ≠ A := fun h => hnc (h ▸ cRA)
  have hRB : R ≠ B := fun h => hnc (h ▸ cRB)
  have htwo : FunTwoType t n := by rcases ht with rfl | rfl <;> simp [FunTwoType]
  exact no_three_commuting_modelFund_of_funTwo hp2 hadm htwo
    hR hA hB hRA hRB hAB cRA cRB cAB


theorem centralizingLayer_funSet_eq_of_g2d4
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (hX : LieModel X t n p e)
    (ht : t = .G2 ∨ t = .trialityD4)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ e) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  have hfund : IsFundTag t := by
    rcases ht with rfl | rfl <;> trivial
  have htwo : FunTwoType t n := by
    rcases ht with rfl | rfl <;> simp [FunTwoType]
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rcases ht with rfl | rfl <;> simp
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX hA1 hK.1
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ LieModel (X ⧸ center X) t n p f :=
    ⟨t, n, e, hadm, rfl, hX.quotient_center hZ⟩
  have hcount := ncard_funSet_eq_two_of_funTwoType hp.out hp2 hadm hX htwo P
  obtain ⟨J, hJ, hJK⟩ : ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X), J ≠ K := by
    obtain ⟨A, B, hAB, hΔ⟩ := Set.ncard_eq_two.mp hcount
    by_cases hAK : A = K
    · exact ⟨B, hΔ ▸ Set.mem_insert_of_mem _ (Set.mem_singleton B), by simpa [hAK] using hAB.symm⟩
    · exact ⟨A, hΔ ▸ Set.mem_insert A _, hAK⟩
  obtain ⟨ψ, hψ, hker⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p e hp.out hp2 hfund hadm X hX
  have hreal : ∀ {L : Subgroup X}, IsFundamentalOver (p ^ e) L →
      ∃ R ∈ ModelFund p t n e, L = R.map ψ := by
    intro L hL
    obtain ⟨R, hR, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX hfund hA1 hL2 ψ hψ hker hL
    exact ⟨R, hR, hLR⟩
  obtain ⟨RJ, hRJ, hJmap⟩ := hreal hJ.1
  obtain ⟨RK, hRK, hKmap⟩ := hreal hK.1
  have cJK : Commutes J K := by
    have hc := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hJ hK hJK
    exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm
  have cModel : Commutes RJ RK := commutes_modelFund_of_commutes_map
    hp2 hfund hadm ψ hker hRJ (by simpa only [← hJmap, ← hKmap] using cJK)
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨RL, hRL, hLmap⟩ := hreal hL.1
    have cJL : Commutes J L := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp (hL.2 hb) a ⟨J, hJ, hJK, ha⟩
    have cModel' : Commutes RJ RL := commutes_modelFund_of_commutes_map
      hp2 hfund hadm ψ hker hRJ (by simpa only [← hJmap, ← hLmap] using cJL)
    have heq := eq_of_commutes_g2d4_modelFund hp2 hadm ht hRJ hRK hRL cModel cModel'
    rw [hLmap, ← heq, ← hKmap]
  · refine le_centralizingLayer ⟨hK.1, ?_⟩
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨L, hL, hLK, hb⟩
    have hc := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hL hK hLK
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hb) a ha).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22

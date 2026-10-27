module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3B1
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.RankThree.PartOne.S11c.OuterInner
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3ThinNNOut (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ¬ (Y.subgroupOf D.M).Normal → F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
    ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q → ∀ p ∈ D.sig, 5 ≤ p →
      ¬ p ∣ Nat.card (Outer (Bar2 Y)) → normalizer (X : Set G) ≤ D.M

theorem R847E3.exists_B₀_of_not_dvd_outer (hThin : PartTwo.ThinList13) {M : Subgroup G}
    (hK : CFSG.Open.IsKGroup ↥M) {Y : Subgroup G} (hY : Y ∈ calC M) (hthin : F08.Thin8 Y)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h3 : 3 ≤ CFSG.Open.pRank p M)
    (hout : ¬ p ∣ Nat.card (Outer (Bar2 Y))) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) (hrank : CFSG.Open.pRank q M ≤ 3) :
    ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hKY : CFSG.IsKGroup (Bar2 Y) :=
    uc22br4_isKGroup_catalog_of_open ((hK.of_le hY.1.le).quotient (CFSG.pCore 2 ↥Y))
  have hs : IsSimpleGroup (Bar2 Y) := (hThin (Bar2 Y) hKY hY.2.2 (PartTwo.s13_pCore_bar_eq_bot Y)
    fun r hr hr2 => PartTwo.s13_pRank_bar_le_one hthin hr hr2).1
  have hZ : center (Bar2 Y) = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (center (Bar2 Y)) inferInstance
      with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := PartTwo.s13_nonabelian_bar hY
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm hab
  obtain ⟨E, hEM, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h3
  have hEN : E ≤ normalizer (Y : Set G) :=
    uc22ine229_le_normalizer hY hp hp5 hq hq2 hXY hXc
      (by rw [hZ, Subgroup.card_bot]; exact hq.not_dvd_one) hrank hEM hEel
  set R : Subgroup (MulAut (Bar2 Y)) :=
    (E.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y) with hRdef
  have hRel : IsElemAbelian p R := (hEel.subgroupOf _).map _
  have hRinn : R ≤ (MulAut.conj : Bar2 Y →* MulAut (Bar2 Y)).range := fun α hα =>
    CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer hp hout α
      (hRel.2 α hα)
  have hquot : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 Y ⧸ center (Bar2 Y))) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)]
    exact (uc22s206c_pRank_le Y hp hp2).trans (hthin p hp hp2)
  have hR : Nat.card R ≤ p := by
    let ι := UCK.innerEquivQuot (Bar2 Y)
    let A : Subgroup (Bar2 Y ⧸ center (Bar2 Y)) :=
      (R.subgroupOf (MulAut.conj : Bar2 Y →* MulAut (Bar2 Y)).range).map ι.toMonoidHom
    have hAel : IsElemAbelian p A :=
      IsElemAbelian.map (IsElemAbelian.subgroupOf (E := R) hRel _) _
    have hAcard : Nat.card A = Nat.card R := by
      rw [Subgroup.card_map_of_injective ι.injective,
        Nat.card_congr (subgroupOfEquivOfLe hRinn).toEquiv]
    rw [← hAcard]
    exact UCK.card_le_of_sylow_isCyclic
      (fun S => RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hp2 hquot S) hAel
  obtain ⟨B₀, hB₀E, hB₀, hB₀c, hB₀Y⟩ :=
    R847E3.exists_kernel (k := 1) hY.1 hp hEN hEel hEc (by rw [pow_one]; exact hR)
  exact ⟨B₀, hB₀E.trans hEM, hB₀, hB₀c, hB₀Y⟩

theorem r847E3ThinNNOut_dataOfSetup (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13) (hS : Standing G)
    (S : Setup G) : R847E3ThinNNOut (dataOfSetup hS S) := by
  intro Y hY _ hthin X hXY q hq hq2 hXc p hp hp5 hout
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨hpP, -⟩ := (dataOfSetup hS S).sig_prime p hp
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  have hK : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hsp.1
  have hrank : CFSG.Open.pRank q S.M ≤ 3 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 S.M
      (dataOfSetup hS S).maxLocal.1).trans (le_of_eq hS.rank)
  obtain ⟨B₀, hB₀M, hB₀, hB₀c, hB₀Y⟩ := R847E3.exists_B₀_of_not_dvd_outer hThin hK hY hthin hpP
    hp5 (hSg.three_le p hp) hout hq hq2 hXY hXc hrank
  exact R847E3.normalizer_le_of_thin_five_of_cent hSE hSEZ hS S hp hp5 hY hthin hB₀M hB₀ hB₀c
    hB₀Y hq hq2 hXY hXc

end CFSG.LocalAnalysis.UniquenessCase.UC22

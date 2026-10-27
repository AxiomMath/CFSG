module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeTorality
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeCases
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeCenter
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreePure
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeReduce

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section EndNode

variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.exists_endNode (hE : EndNodeInput) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) (hn3 : 3 ∣ n) (h : Cfg ψ A As) (hF : ∃ a ∈ As, ¬ Induces ψ a)
    (hZ3 : Nat.card (Subgroup.center L') = 3) (hA6 : Nat.card A = 3 ^ 6) :
    ∃ a, GGIsEndNode A a ∧ GGCentEnd As a ∧ GGNonSmallRule 3 A a := by
  obtain ⟨t, htend, hns, hout⟩ := hE K n hn hK h3 hn3 L' ψ h.surj h.ker_le h.perfect hZ3 A h.hA hA6
    fun y hy => h.induces y hy
  have hind := h.induces_iff_mem hF
  have hcentA : GGCentEnd A t := htend.2.2.2
  have htfix : ∀ j ∈ LargeEvenLayer (ggFix t), t j = j :=
    (hcentA t htend.1).2 (Subgroup.mem_zpowers t)
  refine ⟨t, htend, fun a' ha' => ⟨fun hfix => ?_, fun hmem => ?_⟩, fun _ _ => hns⟩
  · by_contra hnot
    have hnA : a' ∉ A := fun haA => hnot ((hcentA a' haA).1 hfix)
    have hnind : ¬ Induces ψ a' := fun hi => hnA ((hind a' ha').1 hi)
    obtain ⟨j, hj, hne⟩ := hout a'
      (fun y hy => TableB.IsElemAbelian.comm h.hAs ha' (h.lt.le hy)) (h.hAs.2 a' ha') hnind
    exact hne (hfix j hj)
  · exact fixes_of_mem_zpowers htfix hmem

end EndNode

section Assembly

theorem ggTwE6DeltaInput3_of_split (hB1 : RankFiveInnInput) (hNine : TorusLiftNineInput)
    (hSix : TorusLiftSixInput) (hE : EndNodeInput) : GGTwE6DeltaInput3 := by
  intro K _ _ n hn hK h3 L' _ _ ψ hψ hker hperf A As hA hlt hAs hcard hAI hr h3le hadm hnone
  have h : Cfg ψ A As := ⟨hψ, hker, hperf, hA, hlt, hAs, hcard, hAI, hr, h3le, hadm, hnone⟩
  have h5 := h.five_le_card hn hK h3
  by_cases hI : ∀ a ∈ As, Induces ψ a
  · exfalso
    rcases h.card_center_dvd hn hK with hZ1 | hZ3
    · exact h.false_of_caseI_Rtype hn hK hI hZ1
    · obtain ⟨hA5, hAs6⟩ := h.card_of_caseI hn hK h3 h5 hI
      exact h.false_of_caseI_Utype hSix hn hK h3 hI hZ3 hA5 hAs6
  · have hF : ∃ a ∈ As, ¬ Induces ψ a := by
      by_contra hcon
      exact hI fun a ha => by_contra fun hna => hcon ⟨a, ha, hna⟩
    obtain ⟨a₀, ha₀, hna₀⟩ := hF
    have hn3 : 3 ∣ n := h.three_dvd_of_not_induces hn hK h3 ha₀ hna₀
    have h9 : 9 ∣ 2 ^ n + 1 := nine_dvd_of_three_dvd h3 hn3
    rcases h.card_center_dvd hn hK with hZ1 | hZ3
    · exact (h.false_of_caseF_Rtype hB1 hn hK h9 h5 hZ1).elim
    · rcases h.card_eq_five_or_six hn hK h3 with hA5 | hA6
      · exact (h.false_of_caseF_Utype_five hNine hn hK h3 h9 hZ3 hA5).elim
      · exact h.exists_endNode hE hn hK h3 hn3 ⟨a₀, ha₀, hna₀⟩ hZ3 hA6

end Assembly

end CFSG.StandardType.TwE6D3

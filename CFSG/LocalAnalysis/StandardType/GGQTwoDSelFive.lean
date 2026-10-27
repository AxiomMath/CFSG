module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDLGenFinal
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthCell
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShape
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Odd
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseU
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalU
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Edge
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan


theorem qtwoUnitRankTwo_of_cfg (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} {e' : Fin m ≃ ι} (hm : 5 ≤ m) (hm3 : ¬ 3 ∣ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hcell : qtwoOrthL.compl G L 𝒦)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrC : r ∈ ggCoxRefl M e)
    (hr'A : r' ∈ ggAutomizer L Bs) (hr'C : r' ∈ ggCoxRefl M e) (hne : r * r' ≠ r' * r) :
    ggRankTwo Bs r r' = ggRankTwoIn L Bs r r' := by
  obtain ⟨F0, _, _, _, ψ, ε, hbase⟩ :=
    ggQTwoDUnit_base_of_ne_six ggLabelRigidInput_holds hTBF hWI hcfg e' hm (by omega) hM hcell
  have hodd := qtwoDL1_odd_centralizer_of_ne hcfg.1 (ggQTwoDUnit_B_lt_Bs hcfg.1 hm hm3 hbase).ne
  have hle3 := qtwo_label_le_three e' hM
  obtain ⟨r₀, hr₀, hrefl₀, r₀', hr₀', hrefl₀', hne₀, hcard₀⟩ :=
    qtwoDL1_base_unit ggLNoncyclicInput_holds hcfg.1 hodd hbase.card_field hbase.hyp hbase.range
      hbase.diag (hbase.card_bs_eq (by omega))
  have hr₀C : r₀ ∈ ggCoxRefl M e := ggCoxRefl_of_cfg hcfg.1
    (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 hle3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀) hrefl₀
  have hr₀'C : r₀' ∈ ggCoxRefl M e := ggCoxRefl_of_cfg hcfg.1
    (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 hle3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀') hrefl₀'
  have hedge : ∃ i j : ι, M.M i j = 3 := by
    obtain ⟨j, hj⟩ := CFSG.ClassicalInvolution.PhanDn.QTwo.ggCoxeterMatrixD_exists_three
      (m := m) (by omega) ⟨0, by omega⟩
    refine ⟨e' ⟨0, by omega⟩, e' j, ?_⟩
    rw [hM, CoxeterMatrix.reindex_apply]
    simpa using hj
  have hcard := qtwoDL1_card_rankTwo_eq hcfg.2.2.2.1 hle3 hedge hr₀C hr₀'C hne₀ hrC hr'C hne
  apply qtwoDL1_rankTwo_eq_of_card_le
  rw [hcard]
  exact hcard₀.trans (qtwoDL1_local_unit hbase.card_field hbase.hyp hbase.range hbase.diag hrA
    hr'A (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hrC) (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr'C)
    hne)

theorem ggQTwoEdgeAmbientLInputOn_of_not_three_dvd {R : ℕ → Prop}
    (hR : ∀ m, R m → 5 ≤ m ∧ ¬ 3 ∣ m) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoEdgeAmbientLInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM r hrA hrC r' hr'A hr'C hne
  by_cases hcell : qtwoOrthL G L 𝒦
  · exact qtwoOrthRankTwo_of_cfg hcfg (by have := (hR m hm).1; omega) hM hcell hrA hrC hr'A hr'C
      hne
  · exact qtwoUnitRankTwo_of_cfg hTBF hWI hcfg (hR m hm).1 (hR m hm).2 hM hcell hrA hrC hr'A
      hr'C hne

theorem ggQTwoSelLInputOn_of_not_three_dvd {R : ℕ → Prop} (hR : ∀ m, R m → 5 ≤ m ∧ ¬ 3 ∣ m)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGQTwoSelLInputOn R :=
  ggQTwoSelLInputOn_of_rankTwoGen_L (fun m hm => by have := (hR m hm).1; omega)
    (ggQTwoEdgeAmbientLInputOn_of_not_three_dvd hR hTBF hWI)
    (ggQTwoLGenRankTwoInputOn_of_inputs
      (fun m hm => ⟨(hR m hm).1, by have := (hR m hm).2; omega⟩) ggLabelRigidInput_holds hTBF hWI)

theorem ggQTwoSelLInputOn_five (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoSelLInputOn fun m => m = 5 :=
  ggQTwoSelLInputOn_of_not_three_dvd (fun m hm => ⟨by omega, by omega⟩) hTBF hWI

end CFSG.StandardType.QTwo

end

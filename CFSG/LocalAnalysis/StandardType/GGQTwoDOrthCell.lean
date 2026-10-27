module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMember
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1BaseO
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Edge
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

section Cell

theorem qtwoOrthMemberFacts_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hcell : qtwoOrthL G L 𝒦) :
    QTwoOrthMemberFacts p Bs L := by
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hcfg.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
  obtain ⟨Φ, hF, -, -, hZ, -⟩ := qtwoOrthFrameCore_of_cfg hcfg hle3 hΛ hhas hn htag
  exact qtwoOrthMemberFacts_of_frameCore hBs Φ hF hZ

theorem qtwoOrthRankOne_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} {e' : Fin m ≃ ι}
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hcell : qtwoOrthL G L 𝒦)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrC : r ∈ ggCoxRefl M e) :
    ggRankOne Bs r = ggRankOneIn L Bs r ∧ Nat.card ↥(ggRankOne Bs r) = 6 := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    have hne : e'.symm i ≠ e'.symm j := fun h => hij (e'.symm.injective h)
    have h23 := CFSG.ClassicalInvolution.PhanDn.QTwo.ggCoxeterMatrixD_two_or_three _ _ hne
    rw [hM, CoxeterMatrix.reindex_apply]
    omega
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
  obtain ⟨Φ, hF, -, -, -, hlt⟩ := qtwoOrthFrameCore_of_cfg hcfg hle3 hΛ hhas hn htag
  have hodd := qtwoDL1_odd_centralizer_of_ne hcfg.1 hlt.ne
  exact qtwoDL1_rankOne_of_odd ggLNoncyclicInput_holds hcfg hM hodd (Or.inl rfl) hrA hrC

theorem qtwoOrthRankTwo_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} {e' : Fin m ≃ ι}
    (hm : 4 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e') (hcell : qtwoOrthL G L 𝒦)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs) (hrC : r ∈ ggCoxRefl M e)
    (hr'A : r' ∈ ggAutomizer L Bs) (hr'C : r' ∈ ggCoxRefl M e) (hne : r * r' ≠ r' * r) :
    ggRankTwo Bs r r' = ggRankTwoIn L Bs r r' := by
  have : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg.1).1⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    have hne : e'.symm i ≠ e'.symm j := fun h => hij (e'.symm.injective h)
    have h23 := CFSG.ClassicalInvolution.PhanDn.QTwo.ggCoxeterMatrixD_two_or_three _ _ hne
    rw [hM, CoxeterMatrix.reindex_apply]
    omega
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
  obtain ⟨Φ, hF, -, -, hZ, hlt⟩ := qtwoOrthFrameCore_of_cfg hcfg hle3 hΛ hhas hn htag
  have hodd := qtwoDL1_odd_centralizer_of_ne hcfg.1 hlt.ne
  obtain ⟨r₀, hr₀, hrefl₀, r₀', hr₀', hrefl₀', hne₀, hcard₀⟩ :=
    qtwoDL1_base_orth ggLNoncyclicInput_holds hcfg.1 hodd Φ hF hZ
  have hr₀C : r₀ ∈ ggCoxRefl M e := ggCoxRefl_of_cfg hcfg.1
    (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 hle3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀) hrefl₀
  have hr₀'C : r₀' ∈ ggCoxRefl M e := ggCoxRefl_of_cfg hcfg.1
    (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 hle3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀') hrefl₀'
  have hedge : ∃ i j : ι, M.M i j = 3 := by
    obtain ⟨j, hj⟩ := CFSG.ClassicalInvolution.PhanDn.QTwo.ggCoxeterMatrixD_exists_three
      (m := m) hm ⟨0, by omega⟩
    refine ⟨e' ⟨0, by omega⟩, e' j, ?_⟩
    rw [hM, CoxeterMatrix.reindex_apply]
    simpa using hj
  have hcard := qtwoDL1_card_rankTwo_eq hcfg.2.2.2.1 hle3 hedge hr₀C hr₀'C hne₀ hrC hr'C hne
  have hlocal : Nat.card ↥(ggRankTwoIn L Bs r r') = 216 :=
    (qtwoOrth_pair_card_core Φ hF hrA hr'A
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hrC)
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr'C) hne).2
  apply qtwoDL1_rankTwo_eq_of_card_le
  rw [hcard, hlocal]
  exact hcard₀

theorem qtwoMemberFacts_of_orthogonal_cfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} {e' : Fin m ≃ ι}
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hcell : qtwoOrthL G L 𝒦)
    (hEdge : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
      ∀ r' ∈ ggAutomizer L Bs, r' ∈ ggCoxRefl M e → r * r' ≠ r' * r →
        ggRankTwo Bs r r' = ggRankTwoIn L Bs r r') :
    QTwoMemberFacts Bs L M (ggAutomizerJoin L Bs 𝒦) e := by
  have hroute : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := hcfg.1
  obtain ⟨hp, _⟩ := ggRouteCfg_prime hroute
  have : Fact p.Prime := ⟨hp⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    have hne : e'.symm i ≠ e'.symm j := fun h => hij (e'.symm.injective h)
    have h23 := CFSG.ClassicalInvolution.PhanDn.QTwo.ggCoxeterMatrixD_two_or_three _ _ hne
    rw [hM, CoxeterMatrix.reindex_apply]
    omega
  have hMF := qtwoOrthMemberFacts_of_cfg hcfg hle3 hcell
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr hrC
    exact (qtwoOrthRankOne_of_cfg hcfg hM hcell hr hrC).1
  · intro r hr hrC r' hr' hr'C hcomm
    exact hEdge r hr hrC r' hr' hr'C hcomm
  · intro r hr hrC r' hr' hr'C hcomm _
    exact hMF.1 r hr (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hrC) r'
      hr' (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr'C) hcomm
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ h12 h23 h13 hne _
    exact hMF.2.1 r₁ h₁ (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₁) r₂ h₂
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₂) r₃ h₃
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₃) h12 h23 h13 hne
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ r₄ h₄ hr₄ h12 h34 h13 h14 h23 h24
    exact hMF.2.2 r₁ h₁ (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₁) r₂ h₂
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₂) r₃ h₃
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₃) r₄ h₄
      (ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr₄) h12 h34 h13 h14 h23 h24

theorem ggQTwoCellInputOn_orth_of_inputs {R : ℕ → Prop}
    (hEdge : GGQTwoEdgeAmbientInputOn R)
    (hFrame : GGQTwoFrameInputOn R) : GGQTwoCellInputOn R qtwoOrthL := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hcell
  refine ⟨L, ?_, ?_, le_ggG0_left p B x L D J⟩
  · exact qtwoMemberFacts_of_orthogonal_cfg hcfg hM hcell
      (hEdge G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl))
  · obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
    exact (hFrame G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM lab hΛ hhas hn htag).2

theorem ggQTwoCellInputOn_orth_of_four_le {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) : GGQTwoCellInputOn R qtwoOrthL := by
  have hFrame : GGQTwoFrameInputOn R :=
    ggQTwoFrameInput_of_inputs hR ggLabelRigidInput_holds hTBF hWI
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hcell
  refine ⟨L, ?_, ?_, le_ggG0_left p B x L D J⟩
  · exact qtwoMemberFacts_of_orthogonal_cfg hcfg hM hcell
      (fun r hr hrC r' hr' hr'C hne =>
        qtwoOrthRankTwo_of_cfg hcfg (hR m hm) hM hcell hr hrC hr' hr'C hne)
  · obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
    exact (hFrame G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM lab hΛ hhas hn htag).2

theorem ggQTwoCellInputOn_orth_fiveSix (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoCellInputOn (fun m => m = 5 ∨ m = 6) qtwoOrthL :=
  ggQTwoCellInputOn_orth_of_four_le (fun _ hm => by omega) hTBF hWI

theorem ggQTwoCellInput_orth_of_inputs (_hL1 : GGQTwoL1Input) (hEdge : GGQTwoEdgeAmbientInput)
    (hFrame : GGQTwoFrameInput) : GGQTwoCellInput qtwoOrthL :=
  ggQTwoCellInputOn_orth_of_inputs hEdge hFrame

end Cell

end CFSG.StandardType.QTwo

end

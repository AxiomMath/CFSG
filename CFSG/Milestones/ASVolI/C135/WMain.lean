module

public import CFSG.Quasithin.MS93.Burnside.C134BigProof
public import CFSG.Milestones.ASVolI.C135.WTwo
public import CFSG.Quasithin.MS93.MResOrd
import CFSG.Quasithin.MS93.Burnside.Mag568Main
public import CFSG.Quasithin.MS93.MRes46
public import CFSG.Quasithin.MS93.MResC13

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Pointwise

section Concl

variable {G : Type} [Group G]

@[expose] def burnsideC134w_ConclW (M T L : Subgroup G) : Prop :=
  MS93ConclAS M T L ∨ (Xq M ≤ Zq M L ⊔ Uq M T L ∧ burnsideC134w_MS93Case13W (Vq M L) T L)

end Concl

section Assembly

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideC134w_conclW_of_endConcl (h38 : S38) (h45 : burnsideC134w_S45W)
    (h46 : MRes.S46Two) (h512 : S512) (h7 : S7Two) (h : PUHyp M T L) (hL : MRes.NotSL3Big L)
    (hb : 2 < critDist (puAmalgam h.le)) (he : S34D.EndConcl T L) :
    burnsideC134w_ConclW M T L := by
  obtain ⟨M₁, T₁, h₁, hT₁T, hmin₁, hor⟩ := he
  have hV₁ : Vq M₁ L = Vq M L := h.vq_eq_vq h₁
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m, hm⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · have h5 := h7 G M T L M₁ T₁ h h₁ hT₁T hmin₁ hV₁ hb hb₁
    have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
      rcases h38 G M T L h hb with hSL | hSp
      · exact hSL.1.le
      · exact (case5_sp4U_false h h5 hSp).elim
    exact Or.inl (MS93ConclAS.of_case5 hX h5)
  have hgood := hor.resolve_left hb₁
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  rcases h38 G M₁ T₁ L h₁ hb₁' with hSL₁ | hSp₁
  swap
  · exact (h512 G M₁ T₁ L h₁ hmin₁ hb₁' (hgood.2 hSp₁)).elim
  have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
    rcases h38 G M T L h hb with hSL | hSp
    · exact hSL.1.le
    · exact (sl3U_sp4U_false h h₁ hSL₁ hSp).elim
  have hFull := hgood.1 hSL₁
  rcases (show critDist (puAmalgam h₁.le) = 4 ∨ 4 < critDist (puAmalgam h₁.le) by omega)
    with h4 | h4
  · have h11 := h46 G M₁ T₁ L h₁ hmin₁ h4 hFull hL
    rw [hV₁] at h11
    exact Or.inl (MS93ConclAS.of_case11 hX (h11.mono hT₁T))
  · have h13 := h45 G M₁ T₁ L h₁ hmin₁ h4 hFull
    rw [hV₁] at h13
    exact Or.inr ⟨hX, h13.mono hT₁T⟩

end Assembly

@[expose] def burnsideC134w_MS93ASOrdW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L → MRes.NotSL3Big L →
    MRes.NoSp4Quot L → burnsideC134w_ConclW M T L

theorem burnsideC134w_ms93ASOrdW_of (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18)
    (h38 : S38) (h45 : burnsideC134w_S45W) (h46 : MRes.S46Two) (h512 : S512) (h7 : S7Two)
    (hred : PUReduce) : burnsideC134w_MS93ASOrdW := by
  intro G _ _ M T L h hL hS
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact Or.inl (ms93ConclAS_of_critDist_eq_two h32 h36 h37 h18 h hb)
  · have hpos := h.critDist_pos
    obtain ⟨m, hm⟩ := h.critDist_even
    exact burnsideC134w_conclW_of_endConcl h38 h45 h46 h512 h7 h hL (by omega)
      (MRes.endConcl_of_noSp4 hred hL hS h)

section C134

variable {G : Type} [Group G] [Finite G]

theorem burnsideC134w_notCentralizerCore_of_case13W {G₀ R L : Subgroup G} (h : PUHyp G₀ R L)
    (hX : Xq G₀ ≤ Zq G₀ L ⊔ Uq G₀ R L) (h13 : burnsideC134w_MS93Case13W (Vq G₀ L) R L) :
    C134NotCentralizerCore G₀ R := by
  obtain ⟨n, F, _, _, α, hF, hα, hZeq, -, hU, -, hQj⟩ := h13
  have hmod := MRes.isModO2Surj_of_surjective h hF hα
  have hn : 1 ≤ n := one_le_of_card_eq_two_pow hF
  have hGZ : G₀ ≤ Subgroup.normalizer (centerOf (Vq G₀ L) : Set G) := le_normalizer_centerOf_Vq h
  have hGW : G₀ ≤ Subgroup.normalizer ((⁅centerOf (Vq G₀ L), L⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hGZ h.le_normalizer
  have hWZ : ⁅centerOf (Vq G₀ L), L⁆ ≤ centerOf (Vq G₀ L) :=
    commutator_le_left_of_le_normalizer (h.L_le.trans hGZ)
  refine notCentralizerCore_of_natural h hF hα hmod.2 hU (fun x hx => ?_) (fun T hT hRT => ?_)
  · have hxZ : x ∈ Zq G₀ L ⊔ centerOf (Vq G₀ L) :=
      sup_le_sup_left (Uq_le_centerOf_Vq h) _ (hX hx)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (Zq_le.trans hGZ)]
      at hxZ
    obtain ⟨c₁, hc₁, z, hz, rfl⟩ := hxZ
    have hz' : z ∈ (Vq G₀ L ⊓ Subgroup.centralizer (L : Set G)) ⊔ ⁅centerOf (Vq G₀ L), L⁆ :=
      hZeq ▸ hz
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((inf_le_left.trans (Vq_le h.L_le)).trans hGW)] at hz'
    obtain ⟨c₂, hc₂, u, hu, rfl⟩ := hz'
    exact ⟨c₁ * c₂, Subgroup.mul_mem _ (Subgroup.mem_inf.mp hc₁).2 (Subgroup.mem_inf.mp hc₂).2,
      u, hu, by group⟩
  · obtain ⟨X, hXpar, hidx, hXR⟩ := hQj T hT hRT
    obtain ⟨P, hP, -, hXP⟩ := id hXpar
    have hXL : X ≤ L := hXP ▸ (pCoreOf_le' P).trans hP.1.1
    refine ⟨X, hXpar, ?_, fun hle => ?_, hXR⟩
    · rw [Subgroup.inf_relIndex_left]
      have hne : (Subgroup.centralizer (X : Set G)).relIndex (centerOf (Vq G₀ L)) ≠ 0 := by
        rw [← Subgroup.inf_relIndex_left, hidx]
        positivity
      calc (Subgroup.centralizer (X : Set G)).relIndex ⁅centerOf (Vq G₀ L), L⁆
          ≤ (Subgroup.centralizer (X : Set G)).relIndex (centerOf (Vq G₀ L)) :=
            Subgroup.relIndex_le_of_le_right hWZ hne
        _ = 2 ^ n := by rw [← Subgroup.inf_relIndex_left, hidx]
    · have hZC : centerOf (Vq G₀ L) ≤ Subgroup.centralizer (X : Set G) := by
        rw [hZeq]
        exact sup_le (inf_le_right.trans (Subgroup.centralizer_le hXL)) hle
      have h1' : (centerOf (Vq G₀ L) ⊓ Subgroup.centralizer (X : Set G)).relIndex
          (centerOf (Vq G₀ L)) = 1 := by
        rw [inf_eq_left.mpr hZC, Subgroup.relIndex_self]
      rw [h1'] at hidx
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega

theorem burnsideC134w_case4W_of_case13W {G₀ R L : Subgroup G} (h : PUHyp G₀ R L)
    (hX : Xq G₀ ≤ Zq G₀ L ⊔ Uq G₀ R L) (h13 : burnsideC134w_MS93Case13W (Vq G₀ L) R L) :
    ASVolI.burnsideC135_Case4W G₀ R L := by
  have hNC := burnsideC134w_notCentralizerCore_of_case13W h hX h13
  obtain ⟨n, F, _, _, α, hF, hα, hZeq, hdisj, hU, hchief, -⟩ := h13
  exact ⟨⟨n, F, inferInstance, inferInstance, α, hF, MRes.isModO2Surj_of_surjective h hF hα,
    hZeq, hdisj, hU⟩, hNC, hchief⟩

theorem burnsideC134w_caseCorr_of_conclAS
    {G₀ R L : Subgroup G}
    (hMS : IsMSPair G₀ R) (hL : L ∈ cComp G₀) (hG : (G₀ : Set G) = (L : Set G) * (R : Set G))
    (h : PUHyp G₀ R L) {n : ℕ} {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(StatedSL 3 F)}
    (hF : Fintype.card F = 2 ^ n) (hα : IsModO2Surj L α) (hc : MS93ConclAS G₀ R L) :
    ∃ i : ℕ, IsC134CaseCorr i G₀ R L := by
  rcases hc with h2 | h3 | h4 | ⟨hX5, h5⟩ | h6 | h8 | h10 | ⟨hX11, h11⟩ | ⟨hX13, h13⟩
  · exact (not_case2_of_sl3 h h2 hF hα).elim
  · exact (not_case3_of_sl3 h h3 hF hα).elim
  · exact ⟨1, isSL3Block_of_case4 h h4⟩
  · refine ⟨2, ?_, c134NotCentralizer5_holds G G₀ R L hMS hL hG h hX5 h5⟩
    obtain ⟨n', F', _, _, α', hF', hmod, hn'⟩ := isModO2Surj_of_case5 h h5
    exact ⟨n', F', inferInstance, inferInstance, α', hF', hmod, hn'⟩
  · exact (not_case6_of_sl3 h h6 hF hα).elim
  · exact ⟨5, isC134Case5_of_case8 hMS hL hG h h8⟩
  · exact (not_case10_of_sl3 h h10 hF hα).elim
  · refine ⟨3, ?_, c134NotCentralizer11_holds G G₀ R L hMS hL hG h hX11 h11⟩
    obtain ⟨n', F', _, _, α', hF', hα', h1, h2, -⟩ := h11
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case11_data h hα' h1 h2, h1, h2⟩
  · refine ⟨4, ?_, c134NotCentralizer13_holds G G₀ R L hMS hL hG h hX13 h13⟩
    obtain ⟨n', F', _, _, α', hF', hα', hcard, hE, hZeq, hdisj, hU, hΦ, hC, hVC, -⟩ := h13
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case13_data h hα' hZeq hU hΦ hC hVC, isE2_c134CQ_of_case13 hcard hE, hZeq,
      hdisj, hU, hΦ, hC, hVC⟩

@[expose] def burnsideC134w_CaseWeak (i : ℕ) (G₀ R L : Subgroup G) : Prop :=
  (i ≠ 4 ∧ IsC134CaseCorr i G₀ R L) ∨ (i = 4 ∧ ASVolI.burnsideC135_Case4W G₀ R L)

theorem burnsideC134w_caseWeak_of_corr {G₀ R L : Subgroup G} (hLX : L ≤ G₀)
    (hXL : G₀ ≤ Subgroup.normalizer (L : Set G)) {i : ℕ} (hi : IsC134CaseCorr i G₀ R L) :
    burnsideC134w_CaseWeak i G₀ R L := by
  by_cases hi4 : i = 4
  · subst hi4
    exact Or.inr ⟨rfl, ASVolI.burnsideC135_case4_weak hLX hXL hi⟩
  · exact Or.inl ⟨hi4, hi⟩

end C134

@[expose] def burnsideC134w_AS_C_1_34_corrOneWeak : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α) →
      ∃ i : ℕ, burnsideC134w_CaseWeak i G₀ R L

theorem burnsideC134w_corrOneWeak_of_ms93ASOrdW_of_simple
    (hS : RankTwoLieSimple)
    (hms : burnsideC134w_MS93ASOrdW) : burnsideC134w_AS_C_1_34_corrOneWeak := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨F, _, _, α, hF2, hα⟩ := hsl3
  have hF : Fintype.card F = 2 ^ 1 := by rw [hF2, pow_one]
  have h := puHyp_of_msPair_of_simple hS hMS hL hG
  rcases hms G G₀ R L h (MRes.notSL3Big_of_isModO2Surj_two hF2 hα)
      (MRes.noSp4Quot_of_isModO2Surj_two hF2 hα) with hc | ⟨hX13, h13⟩
  · obtain ⟨i, hi⟩ := burnsideC134w_caseCorr_of_conclAS hMS hL hG h hF hα hc
    exact ⟨i, burnsideC134w_caseWeak_of_corr h.L_le h.le_normalizer hi⟩
  · exact ⟨4, Or.inr ⟨rfl, burnsideC134w_case4W_of_case13W h hX13 h13⟩⟩

section Holds

set_option linter.unusedSectionVars false


theorem burnsideC134w_ms93ASOrdW_holds
    : burnsideC134w_MS93ASOrdW :=
  have h441 := s441_holds
  have h44 :=
    s44_frontier h441 (S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds h441)
  burnsideC134w_ms93ASOrdW_of s32_holds (s36_of_g2 s38G2_holds) s37_holds s18_holds
    (s38_of_g2 s38G2_holds)
    (burnsideC134w_s45W_of s43_holds h44 ms14AS_holds sqtkQuot_holds S45J.s45Q2a_holds)
    (MRes.s46Two_of s32_holds (s39_of s32_holds) (s42_of s32_holds) s43_holds ms14AS_holds
      sqtkQuot_holds)
    s512_holds (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds) puReduce_holds

theorem burnsideC134w_corrOneWeak
    : burnsideC134w_AS_C_1_34_corrOneWeak :=
  burnsideC134w_corrOneWeak_of_ms93ASOrdW_of_simple rankTwoLieSimple_holds
    burnsideC134w_ms93ASOrdW_holds

theorem burnsideC134w_c134W
    (hsl : S4L.NoNonlinSLGt4) : ASVolI.burnsideC135_C134W := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨n, F, iF, fF, α, hF, hα⟩ := hsl3
  have hLX : L ≤ G₀ := MS93.le_of_coe_eq_mul_left hG
  have hXL : G₀ ≤ Subgroup.normalizer (L : Set G) := by
    have h' := MS93.le_normalizer_oddGen G₀
    rwa [← MS93.isMSPair_eq_oddGen hMS hL hG] at h'
  by_cases hn : 2 ≤ n
  · obtain ⟨i, hi⟩ := burnsideC134w_corrBig hsl G G₀ R L hMS hL hG ⟨n, F, iF, fF, α, hn, hF, hα⟩
    exact ⟨i, burnsideC134w_caseWeak_of_corr hLX hXL hi⟩
  · have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    have hn1 : n = 1 := by
      rcases n with _ | _ | n
      · rw [hF, pow_zero] at h1
        exact absurd h1 (lt_irrefl 1)
      · rfl
      · omega
    have hF2 : Fintype.card F = 2 := by rw [hF, hn1, pow_one]
    obtain ⟨i, hi⟩ := burnsideC134w_corrOneWeak G G₀ R L hMS hL hG ⟨F, iF, fF, α, hF2, hα⟩
    exact ⟨i, hi⟩

theorem burnsideC134w_c134W_holds
    : ASVolI.burnsideC135_C134W :=
  burnsideC134w_c134W S4L.burnsideMag568_noNonlinSLGt4

end Holds

end CFSG.Quasithin.MS93

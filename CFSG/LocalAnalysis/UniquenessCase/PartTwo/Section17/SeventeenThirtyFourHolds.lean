module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtySixAN3F
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexWreathHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexFHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem htr_of_R17_36aAt {D : Data G} {V₀ V : Subgroup G} (h : R17_36aAt D V₀ V) :
    ∀ (L : Subgroup G) (n : ℕ) (_c : Ctx17_33 D V₀ V L n), ∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
  intro L n c g hg
  refine ⟨1, D.T.one_mem, ?_⟩
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hN := uc22p21j_normal_of_conjClosure_eq hLM (h L n c)
  have hgN : g ∈ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN hg
  have h1 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    ext x
    simp
  have h2 : L.map (MulAut.conj g).toMonoidHom = L := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx
        simpa only [inv_inv] using h3
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  rw [h1, h2]

theorem seventeen_thirtysix_a_of_ne_bot
    (D : Data G) (V₀ V : Subgroup G) (hV0 : V₀ ≠ ⊥)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV) (hSg : SigmaStd D)
    (hCen : UCK.U3Center) (hSyl : UCK.U3Syl) :
    R17_36aAt D V₀ V :=
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  have hBorel : K_U3CartanRank := Inputs1719.k_U3CartanRank_holds
  have hK : K_SU3EightBorelNine := Inputs1719.k_SU3EightBorelNine_holds
  have hK9 : K_SU3EightTorusE9 := Inputs1719.k_SU3EightTorusE9_holds
  seventeen_thirtysix_a_of_subgaps D V₀ V (fun _ _ _ h0 => absurd h0 hV0) h1 hSg hK3 hCen hSyl
    hBorel
    (fun L n => gap17_36a_n3_two_p_of_inputs D V₀ V L n hK hCen hK3 hSg
      (gap17_36a_n3_two_Q_of_inputs D V₀ V L n hSg hCen hK9))
    (fun L n => gap17_36a_n3_three_torus_of_inputs D V₀ V L n hK hCen hK3)

theorem hbBound_of_ne_bot
    (D : Data G) {V₀ V : Subgroup G} (hV0 : V₀ ≠ ⊥) (h416 : Inputs1719.W4Lem4_16)
    (h45 : W3Lem45_2Chief) (h869 : F08.R869 D) (h127 : R127 D) (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (h36 : R17_36aAt D V₀ V) : HbBound D V₀ V :=
  hbBound_of_hbBoundA
    (hbBound_holds (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416)
      (k_U3Index_of_normal_and_F Inputs1719.k_U3IndexNormal_holds
        S17.k_U3IndexF_holds h45) D V₀ V)
    (fun _ _ c => barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC
      (not_thin_of_isSU3 hSyl c.shape))
    (htr_of_R17_36aAt h36)
    (fun _ _ c => (fixV_dichotomy_of_not_thin D h869 h127 h640 hFF c.hyp125 c.mem_calC
      (not_thin_of_isSU3 hSyl c.shape)).resolve_right fun h => hV0 h.1)

@[expose] def Gap17_34_bBoundVZeroTrivial (D : Data G) (V₀ V : Subgroup G) : Prop :=
  V₀ = ⊥ → HbBound D V₀ V

section Certified


theorem seventeen_thirtyfour_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) {V₀ V : Subgroup G} (h117 : C117 D V₀ V)
    (hSyl : UCK.U3Syl) (h45 : W3Lem45_2Chief)
    (h416 : Inputs1719.W4Lem4_16) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV) (hSg : SigmaStd D)
    (hCen : UCK.U3Center) (hgap : Gap17_34_bBoundVZeroTrivial D V₀ V) :
    R17_34At D V₀ V := by
  refine seventeen_thirtyfour D hx h61 h127 h1114 h162 hTor h1482 h126 h111 h869 h117 hSyl
    (k_U3Index_of_normal_and_F Inputs1719.k_U3IndexNormal_holds
      S17.k_U3IndexF_holds h45) ?_
  by_cases hV0 : V₀ = ⊥
  · exact hgap hV0
  · exact hbBound_of_ne_bot D hV0 h416 h45 h869 h127 h640 hFF h117 hSyl
      (seventeen_thirtysix_a_of_ne_bot D V₀ V hV0 h1 hSg hCen hSyl)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

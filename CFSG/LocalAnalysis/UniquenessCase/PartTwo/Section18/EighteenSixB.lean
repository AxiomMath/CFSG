module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixExcl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem isSp4_bar2_of_isSp4_barSub {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {f : ℕ}
    (hSp : IsSp4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) f) :
    IsSp4 (Bar2 (UC22.conjClosure D.M L)) f := by
  have hs : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  rw [hXL] at hSp ⊢
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hSp

theorem isG2_bar2_of_isG2_barSub {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {f : ℕ}
    (hG2 : IsG2 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) f) :
    IsG2 (Bar2 (UC22.conjClosure D.M L)) f := by
  have hs : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) :=
    (CFSG.LieType.Simplicity.fam_g2_simplicity
      ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 2 f
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide))).2
  obtain ⟨hXL, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  rw [hXL] at hG2 ⊢
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hG2

theorem r18_6b (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hW4 : Inputs1719.W4Lem14_6Sec18)
    (h1733 : S17.R17_33_3At D V₀ V) (h1742 : S17.R17_42At D V₀ V)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h : Hyp18 D V₀ V p L)
    (hm : MBarGT D.M V₀ V 3) (h7b : R18_7bAt D V₀ V p L h) :
    P18_6_2 D V₀ V p L h ∨ P18_6_3e D V₀ V p L h ∨ P18_6_4 D V₀ V p L h ∨
      P18_6_5 D V₀ V p L h ∨ P18_6_6 D V₀ V p L h := by
  set n := S17.nOf L with hn
  clear_value n
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hUL : UniqueMax D.M L := by
    rcases h17_66_1 p h.hp L h.hL (UC22.conjClosure D.M L) rfl h.hX with hh | hh
    · exact hh
    · exact absurd hh h18_4
  have hV0card : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hpf.elemAbelian₀).1 h.small
  have hLb : barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_card_le_two D h127 h.hyp125 h.hL.1 hUL hV0card
  have hKgroup : CFSG.Open.IsKGroup ↥(Mbar D.M V₀ V h.hyp125.isElemAbelian) :=
    isKGroup_mbar D h.hyp125.isElemAbelian hMs
  have hK : CFSG.IsKGroup ↥(Mbar D.M V₀ V h.hyp125.isElemAbelian) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKgroup
  have hO2 : O2Trivial (Mbar D.M V₀ V h.hyp125.isElemAbelian) :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp125 hP hN h2
  have hYne : Mbar D.M V₀ V h.hyp125.isElemAbelian ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hbot ▸
      (barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb).1))
  have hbasic : IsBasicModule (Mbar D.M V₀ V h.hyp125.isElemAbelian) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h.hyp125 hYne
  have hcomp : IsComponentOf (barSub V₀ V h.hyp125.isElemAbelian L)
      (Mbar D.M V₀ V h.hyp125.isElemAbelian) :=
    barSub_mem_compBar_of_ne_bot h.hyp125 h.hL.1 hLb
  have hXg : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) =
      ⨆ g ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian,
        (barSub V₀ V h.hyp125.isElemAbelian L).map (MulAut.conj g).toMonoidHom := by
    rw [barSub_conjClosure_eq_iSup h, iSup_subtype']
  have hm' : 3 < E3.mParam (Mbar D.M V₀ V h.hyp125.isElemAbelian) := by
    have h1 : 3 < mBar D.M V₀ V h.hyp125.isElemAbelian :=
      (h.hyp125.mBarGT_iff_lt_mBar 3).1 hm
    simpa [mBar] using h1
  have hle : E3.mParam (Mbar D.M V₀ V h.hyp125.isElemAbelian) ≤
      max (bParam (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L))
        (Mbar D.M V₀ V h.hyp125.isElemAbelian)) n + 2 := by
    have h1 : ¬ ((max (bBar (UC22.conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian)
        (S17.nOf L) + 2 : ℕ) < mBar D.M V₀ V h.hyp125.isElemAbelian) :=
      fun hlt => h7b ((h.hyp125.mBarGT_iff_lt_mBar _).2 hlt)
    have h2 : mBar D.M V₀ V h.hyp125.isElemAbelian ≤
        max (bBar (UC22.conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian)
          (S17.nOf L) + 2 := by omega
    rw [hn]
    simpa [mBar, bBar] using h2
  have hshape := shape18_6 h h1742 h1733 h18_4
  have hcase1 := w4Hyp18_6_cases h hLb hshape
  rw [← hn] at hcase1
  have hcase2 := fixV_or_commPset_of_hyp18 D h640 hFF h hUL hLb
  have hW4c := hW4 (Vtil V₀ V h.hyp125.isElemAbelian)
    (s15_Infra_vtil_sq_eq_one V₀ V h.hyp125.isElemAbelian)
    (Mbar D.M V₀ V h.hyp125.isElemAbelian)
    (barSub V₀ V h.hyp125.isElemAbelian L)
    (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n
    hK hO2 hbasic hcomp hXg hcase1 hm' hle hcase2
  rcases hW4c with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    exact Or.inl ⟨n, Or.inl ⟨isSp4_bar2_of_isSp4_barSub h h1.1, h1.2⟩⟩
  ·
    exact Or.inl ⟨n, Or.inr (Or.inl ⟨isG2_bar2_of_isG2_barSub h h2.1, h2.2⟩)⟩
  ·
    exact Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨h3.1, h3.2⟩))⟩
  ·
    exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨h4.1, h4.2⟩)))⟩
  ·
    exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5.1, h5.2⟩))))⟩
  ·
    exact Or.inl ⟨n,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h6.1, h6.2.1, h6.2.2⟩)))))⟩
  ·
    exact Or.inl ⟨n,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h7.1, h7.2⟩)))))⟩
  ·
    rcases h8 with h8a | h8b | h8c | h8d
    · exact Or.inr (Or.inl ⟨n, Or.inl
        ⟨isSp4_bar2_of_isSp4_barSub h h8a.1, h8a.2⟩⟩)
    · exact Or.inr (Or.inl ⟨n, Or.inr (Or.inl ⟨h8b.1, h8b.2⟩)⟩)
    · exact Or.inr (Or.inl ⟨n, Or.inr (Or.inr ⟨h8c.1, h8c.2.1, h8c.2.2⟩)⟩)
    · obtain ⟨h2, hSU, K, hKf, hKfin, π, hKcard, hSum⟩ := h8d
      subst h2
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hSU, K, hKf, hKfin, π, hKcard, hSum⟩)))
  ·
    rcases h9 with h9a | h9b
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h9a.1, h9a.2⟩)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨h9b.1, h9b.2⟩)))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (p18_6_5_of_w4_alt4 h hLb h10))))
  ·
    exact absurd (Or.inl h11) (not_w4_alt5to7 D hx h61 h127 h hshape hLb)
  ·
    exact absurd (Or.inr (Or.inl h12)) (not_w4_alt5to7 D hx h61 h127 h hshape hLb)
  ·
    exact absurd (Or.inr (Or.inr h13)) (not_w4_alt5to7 D hx h61 h127 h hshape hLb)

theorem r18_6bAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hW4 : Inputs1719.W4Lem14_6Sec18)
    (h1733 : S17.R17_33_3At D V₀ V) (h1742 : S17.R17_42At D V₀ V)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h : Hyp18 D V₀ V p L) :
    R18_6bAt D V₀ V p L h :=
  fun hm h7b => r18_6b D V₀ V p L hx h61 h127 h1214 h640 hFF hW4
    h1733 h1742 h17_66_1 h18_4 h hm h7b

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

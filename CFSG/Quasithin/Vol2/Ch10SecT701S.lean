module

public import CFSG.Quasithin.Background.F918J4
public import CFSG.Quasithin.Background.F918K1
public import CFSG.Quasithin.Background.F918K5
public import CFSG.Quasithin.Vol2.Ch10SecA1011ISec

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

namespace T701S

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem not_le_normalizer_of_lt (hlt : L < fsuL0 T L) :
    ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hT =>
  hlt.ne (le_antisymm (le_conjClosure L T) (conjClosure_le fun _ hg z hz =>
    (Subgroup.mem_normalizer_iff.mp (hT hg) z).mp hz))

theorem hyp10_of (hfsu : FSU G T L I) (hlt : L < fsuL0 T L) (h3 : Concl326Three T L I) :
    Ch10.Hyp10 G T L I :=
  ⟨hfsu, not_le_normalizer_of_lt hlt, hlt, h3⟩

theorem shape_of_one
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h45 : AsB45) (hF : Facts10_1) (hX : Insp5aNonShape)
    (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I) :
    IsShapeGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨-, -, -, -, -, ⟨hUab, hqhat⟩, -⟩ := hyp.three
  have hisec := isec_of_one h37 h38 h322 hyp hUI
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hcomm := commutator_fsuUL_eq h37 h38 hyp hUI
  have hne : ⁅fsuUL T L I, L⁆ ≠ ⊥ := by
    rw [hcomm, hUI]
    exact hyp.fsu.irrPlus.2.1
  have hCU := inf_centralizer_fsuUL_eq h37 h38 h322 hyp hne
  have := hyp.fsu.simple
  have hcore := qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke
  have hS : SQTKGroup ↥(autOn L (fsuUL T L I)) :=
    InternalSec.sqtkGroup_autOn hLU
      (InternalSec.sqtkGroup_of_localSQTK hcore.1 (pCoreOf_ne_bot_of_faithful hyp.fsu.faithful))
      (hCU ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  have hA := a38Types_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  set e := autOnEquivQuotOf hLU hCU
  have : IsSimpleGroup ↥(autOn L (fsuUL T L I)) := e.isSimpleGroup
  have hq : qhatOf (autOn ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G)) (fsuUL T L I)) ≤
      ((2 : ℚ) : WithTop ℚ) := by
    rw [← autOn_sup_eq_autOn_inf h37 h38 hyp]
    exact_mod_cast hqhat
  exact (insp5a_rows h45 hF hX hisec.elem' hisec.qsec hS hq (a38Types_congr e.symm hA)).1
    |>.of_mulEquiv e.symm

theorem shape_of_two
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) (hcard : Nat.card ↥I = 2 ^ 3) {s : G}
    (hU : fsuUL T L I = I ⊔ CFSG.conjugate I s) : IsShapeGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨hab, hel, -⟩ := hyp.three
  have hIU : I ≤ fsuUL T L I := hU ▸ le_sup_left
  obtain ⟨hLI, hcomm⟩ := le_normalizer_and_commutator_ne_bot h37 h38 hyp hIU
  have hC := inf_centralizer_le_pCoreOf h37 h38 hyp hLI hcomm
  have hIab : IsMulCommutative ↥I := isMulCommutative_of_le (le_fsuVM T L I)
  have h2 : ∀ w : ↥I, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hel.2 _ (le_fsuVM T L I w.2))
  have hAut : Nat.card (MulAut ↥I) = 168 := by
    rw [card_mulAut_of_sq_eq_one h2 hcard, card_GL_three_two]
  have hdvd1 := card_quot_dvd_card_autOn hLI hC
  have hdvd2 : Nat.card ↥(autOn L I) ∣ 168 := hAut ▸ Subgroup.card_subgroup_dvd_card _
  by_contra hns
  have hN := nsGroup_of_a38Types (a38Types_of_not_normal h37 h38 hyp.fsu.simple
    hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal) hns
  have hle := Nat.le_of_dvd (by norm_num) (hdvd1.trans hdvd2)
  have := hN.card.ge
  omega

end T701S

theorem stmt7_0_1_shape_of
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h45 : AsB45) (hF : Facts10_1)
    (hX : Insp5aNonShape) : Stmt7_0_1_shape := by
  intro G _ _ T L I hfsu hlt h3
  have hyp := T701S.hyp10_of hfsu hlt h3
  obtain ⟨_, -, -, -, -, -, hc⟩ := h3
  rcases hc with ⟨hUI, -⟩ | ⟨-, -, hcard, s, -, -, -, hU, -⟩ | ⟨⟨e⟩, -, -⟩
  · exact T701S.shape_of_one h37 h38 h322 h45 hF hX hyp hUI
  · exact T701S.shape_of_two h37 h38 hyp hcard hU
  · have := Vol2Native.A312L.Seven.slThree_isSimple
    exact Or.inr (Or.inr (nonempty_quot_equiv_of_autOn h37 h38 hyp e))

end CFSG.Quasithin.Vol2.Ch10.SecA

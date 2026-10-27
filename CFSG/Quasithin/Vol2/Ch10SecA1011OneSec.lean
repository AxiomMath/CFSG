module

public import CFSG.Quasithin.Vol2.Ch10SecA1011One
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Vol2.Ch10SecA1011ISec

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

abbrev yOne (T L : Subgroup G) : Subgroup G :=
  (fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (L : Set G)

noncomputable abbrev ySec (T L I : Subgroup G) [IsMulCommutative ↥(fsuUL T L I)] :
    Subgroup (MulAut (Sec ⊤ (Ch10.cV1 T L I))) :=
  autSec (autOn (yOne T L) (fsuUL T L I)) ⊤ (Ch10.cV1 T L I)

noncomputable abbrev lSec (T L I : Subgroup G) [IsMulCommutative ↥(fsuUL T L I)] :
    Subgroup (MulAut (Sec ⊤ (Ch10.cV1 T L I))) :=
  autSec (autOn L (fsuUL T L I)) ⊤ (Ch10.cV1 T L I)

structure OneSec (T L I : Subgroup G) [IsMulCommutative ↥(fsuUL T L I)] : Prop where
  stab : autOn L (fsuUL T L I) ≤ stabSub (Ch10.cV1 T L I)
  faithful : autOn L (fsuUL T L I) ⊓ centSec ⊤ (Ch10.cV1 T L I) = ⊥
  b4 : B4Hyp (ySec T L I) (lSec T L I)
  sq : ∀ v : Sec ⊤ (Ch10.cV1 T L I), v ^ 2 = 1
  equivL : Nonempty (↥(autOn L (fsuUL T L I)) ≃* ↥L ⧸ CFSG.pCore 2 ↥L)
  simpleL : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)
  shapeL : IsShapeGroup (↥L ⧸ CFSG.pCore 2 ↥L)

variable {T L I : Subgroup G}

theorem oneSec_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape) (hyp : Ch10.Hyp10 G T L I)
    (hUI : fsuUL T L I = I) [IsMulCommutative ↥(fsuUL T L I)] : OneSec T L I := by
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
  have hq := hisec.qsec
  have := hyp.fsu.simple
  have hcore := qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke
  have hS : SQTKGroup ↥(autOn L (fsuUL T L I)) :=
    InternalSec.sqtkGroup_autOn hLU
      (InternalSec.sqtkGroup_of_localSQTK hcore.1 (pCoreOf_ne_bot_of_faithful hyp.fsu.faithful))
      (hCU ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  exact ⟨hq.le.trans hq.stab, hq.faithful, hisec.b4Hyp hS, sec_sq_eq_one hisec.elem' ⊤ _,
    ⟨autOnEquivQuotOf hLU hCU⟩, isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple
      hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal,
    isShapeGroup_of_shape701 (hshape G T L I hyp.fsu hyp.lt hyp.three)⟩

namespace OneSec

variable [IsMulCommutative ↥(fsuUL T L I)] (h : OneSec T L I)

include h

noncomputable def secEquiv : ↥(lSec T L I) ≃* ↥(autOn L (fsuUL T L I)) :=
  (B5.secEquiv (autOn L (fsuUL T L I)) (InternalSec.le_stabSub_top _) h.stab h.faithful).symm

theorem equiv : Nonempty (↥(lSec T L I) ≃* ↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := h.equivL
  exact ⟨h.secEquiv.trans e⟩

theorem simple : IsSimpleGroup ↥(lSec T L I) := by
  obtain ⟨e⟩ := h.equiv
  have := h.simpleL
  exact e.isSimpleGroup

theorem shape : IsShapeGroup ↥(lSec T L I) := by
  obtain ⟨e⟩ := h.equiv
  exact h.shapeL.of_mulEquiv e

end OneSec

theorem qhatOf_ySec_le
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) (hUI : fsuUL T L I = I)
    [IsMulCommutative ↥(fsuUL T L I)] :
    qhatOf (ySec T L I) ≤ ((2 : ℚ) : WithTop ℚ) := by
  obtain ⟨-, -, -, -, -, ⟨hU, hqhat⟩, -⟩ := hyp.three
  refine (isec_of_one h37 h38 h322 hyp hUI).qhatOf_sec_le.trans ?_
  rw [← autOn_sup_eq_autOn_inf h37 h38 hyp]
  exact_mod_cast hqhat

end CFSG.Quasithin.Vol2.Ch10.SecA

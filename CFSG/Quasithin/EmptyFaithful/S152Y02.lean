module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S142Basic
public import CFSG.Quasithin.EmptyFaithful.S152Y01

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

structure Data (T Mc M : Subgroup G) : Prop where
  qtfe : quasithinQTFE14Cat G T Mc
  mf : IsMf T Mc M
  h1515 : Lemma1515Concl T Mc M
  h1521 : Lemma15201Concl T Mc M

theorem JhatOn_le' (M V : Subgroup G) : JhatOn M V ≤ autOn M V := by
  unfold JhatOn
  split_ifs with hV
  · exact @Jhat_le ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V)
  · exact bot_le

@[expose] noncomputable def y0Of (T Mc M : Subgroup G) : Subgroup G := oTwoUpper (m0Of T Mc M)

section HFree

variable (T Mc M : Subgroup G)

theorem m0Of_le : m0Of T Mc M ≤ M := preOn_le _ _ _

theorem mBar0_le : mBar0 T Mc M ≤ autOn M (V154 T Mc M) := JhatOn_le' _ _

theorem y0Of_le : y0Of T Mc M ≤ M := (oTwoUpper_le _).trans (m0Of_le T Mc M)

theorem rc_isPGroup : IsPGroup 2 (rcOf Mc M) := pCoreOf_isPGroup 2 _

theorem y0Of_sup_T_le_normalizer_yOf :
    y0Of T Mc M ⊔ T ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  (le_normalizer_conjClosure _ _).trans (normalizer_le_normalizer_oTwoUpper _)

theorem T_le_normalizer_yOf : T ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  le_sup_right.trans (y0Of_sup_T_le_normalizer_yOf T Mc M)

theorem y0Of_le_normalizer_yOf : y0Of T Mc M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  le_sup_left.trans (y0Of_sup_T_le_normalizer_yOf T Mc M)

theorem autOn_m0Of : autOn (m0Of T Mc M) (V154 T Mc M) = mBar0 T Mc M :=
  autOn_preOn (mBar0_le T Mc M)

end HFree

namespace Data

variable {T Mc M : Subgroup G} (h : Data T Mc M)

include h

theorem inM : InM T M := h.mf.1.1

theorem T_le : T ≤ M := h.inM.2

theorem T_le_Mc : T ≤ Mc := h.qtfe.t_le_mc

theorem ne : Mc ≠ M := fun e => h.mf.2.1 e.symm

theorem hV : IsElemAbelian 2 (V154 T Mc M) := h.h1515.reduced.2.2.1

theorem hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := h.h1515.reduced.2.1

theorem card_V : Nat.card (V154 T Mc M) = 16 := h.h1521.card

theorem hyp : Hyp14117 T Mc M Mc (V154 T Mc M) where
  inM := h.inM
  twoReduced := h.h1515.reduced
  ne_bot := by
    intro hb
    have := h.card_V
    rw [hb, Subgroup.card_bot] at this
    omega
  inM₁ := ⟨h.qtfe.mc_max, h.qtfe.t_le_mc⟩
  ne := h.ne
  cases := Or.inr rfl

theorem le_normalizer_m0Of : M ≤ Subgroup.normalizer (m0Of T Mc M : Set G) :=
  le_normalizer_preOn h.hMV fun _ hg _ hy => JhatOn_normalized hg hy

theorem le_normalizer_y0Of : M ≤ Subgroup.normalizer (y0Of T Mc M : Set G) :=
  h.le_normalizer_m0Of.trans (normalizer_le_normalizer_oTwoUpper _)

theorem autOn_y0Of :
    autOn (y0Of T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) := by
  have := A4.oTwoUpper_autOn (V := V154 T Mc M) ((m0Of_le T Mc M).trans h.hMV)
  rw [autOn_m0Of T Mc M] at this
  exact this.symm

theorem rc_le_T : rcOf Mc M ≤ T := h.hyp.pCoreOf_le_sylow h.qtfe

theorem rc_le_M : rcOf Mc M ≤ M := h.rc_le_T.trans h.T_le

theorem T_le_normalizer_rc : T ≤ Subgroup.normalizer (rcOf Mc M : Set G) :=
  h.hyp.le_inf.trans (le_normalizer_pCoreOf 2 (Mc ⊓ M))

theorem T_le_normalizer_y0Of : T ≤ Subgroup.normalizer (y0Of T Mc M : Set G) :=
  h.T_le.trans h.le_normalizer_y0Of

theorem rc_le_normalizer_y0Of : rcOf Mc M ≤ Subgroup.normalizer (y0Of T Mc M : Set G) :=
  h.rc_le_T.trans h.T_le_normalizer_y0Of

theorem yOf_eq :
    yOf152 T Mc M = oTwoUpper (⁅y0Of T Mc M, rcOf Mc M⁆ ⊔ rcOf Mc M) :=
  congrArg oTwoUpper (conjClosure_sup_eq_commutator_sup (B := y0Of T Mc M)
    h.T_le_normalizer_y0Of h.T_le_normalizer_rc)

theorem yOf_le_commutator : yOf152 T Mc M ≤ ⁅y0Of T Mc M, rcOf Mc M⁆ := by
  rw [h.yOf_eq]
  exact oTwoUpper_commutator_sup_le (rc_isPGroup Mc M) h.rc_le_normalizer_y0Of

theorem commutator_le_y0Of : ⁅y0Of T Mc M, rcOf Mc M⁆ ≤ y0Of T Mc M :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp h.rc_le_normalizer_y0Of

theorem yOf_le_y0Of : yOf152 T Mc M ≤ y0Of T Mc M :=
  h.yOf_le_commutator.trans h.commutator_le_y0Of

theorem yOf_le_M : yOf152 T Mc M ≤ M := h.yOf_le_y0Of.trans (y0Of_le T Mc M)

theorem inf_le_normalizer_yOf : M ⊓ Mc ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := by
  intro a ha
  have hR : a ∈ Subgroup.normalizer (rcOf Mc M : Set G) := le_normalizer_pCoreOf 2 (Mc ⊓ M)
    ⟨ha.2, ha.1⟩
  have hY₀ : a ∈ Subgroup.normalizer (y0Of T Mc M : Set G) := h.le_normalizer_y0Of ha.1
  have hC : a ∈ Subgroup.normalizer (⁅y0Of T Mc M, rcOf Mc M⁆ : Subgroup G) :=
    A4.mem_normalizer_commutator hY₀ hR
  have hW : a ∈ Subgroup.normalizer ((⁅y0Of T Mc M, rcOf Mc M⁆ ⊔ rcOf Mc M : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hC, hR⟩
  rw [h.yOf_eq]
  exact normalizer_le_normalizer_oTwoUpper _ hW

theorem normalizer_Z_le_Mc :
    Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) ≤ Mc := by
  have hZp : IsPGroup 2 (quasithinOmegaOneCenter T) :=
    h.qtfe.sylow.1.to_le (quasithinOmegaOneCenter_le_center T |>.trans inf_le_left)
  obtain ⟨M'', hM'', hNM''⟩ := exists_maxTwoLocal_ge
    (L := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    ⟨quasithinOmegaOneCenter T, h.qtfe.omegaOneCenter_ne_bot, hZp, rfl⟩
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M'' :=
    (Subgroup.centralizer_le_normalizer _).trans hNM''
  rw [← h.qtfe.mc_unique M'' hM'' hCZ]
  exact hNM''

theorem normalizer_T_le_Mc : Subgroup.normalizer (T : Set G) ≤ Mc :=
  (normalizer_le_normalizer_quasithinOmegaOneCenter T).trans h.normalizer_Z_le_Mc

end Data

end S152Y

end CFSG.Quasithin

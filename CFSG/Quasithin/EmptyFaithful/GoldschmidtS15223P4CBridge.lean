module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CVoc
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.EmptyFaithful.T1515dE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.InternalSec

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem inf_normalizer_thompsonJ_le_cgsIn {I S : Subgroup G} (hT2 : IsPGroup 2 S) (hT1 : S ≠ ⊥) :
    I ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ cgsIn I (baum S) := by
  have hJb : thompsonJ S ≤ baum S := S1414.thompsonJ_le_baum S
  have hchar : ((thompsonJ S).subgroupOf (baum S)).Characteristic := by
    have heq : thompsonJ (baum S) = thompsonJ S := B6.thompsonJ_eq_of_le hJb inf_le_left
    have := S1414.characteristic_thompsonJ (baum S)
    rwa [heq] at this
  exact le_iSup_of_le (thompsonJ S) (le_iSup_of_le hJb
    (le_iSup_of_le (S1414.thompsonJ_ne_bot hT2 hT1) (le_iSup_of_le hchar le_rfl)))

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem zS_le_S : zSOf T Mc M B₀ ≤ sOf152 T Mc M B₀ :=
  d.c.inputs.h14.zS_eq.le.trans (omegaOneCenterOf_le_self _)

theorem S_ne_bot : sOf152 T Mc M B₀ ≠ ⊥ := by
  intro h
  have h1 : zSOf T Mc M B₀ = ⊥ := le_bot_iff.mp (h ▸ d.zS_le_S)
  have h4 := (card_zS152 d.c.b0 d.c.inputs).1
  rw [h1, Subgroup.card_bot] at h4
  omega

theorem not_le_normalizer_thompsonJ :
    ¬ X ≤ Subgroup.normalizer (thompsonJ (sOf152 T Mc M B₀) : Set G) := by
  intro h
  apply d.c.not_le
  intro x hx
  have h1 : x ∈ cgsIn I (baum (sOf152 T Mc M B₀)) :=
    inf_normalizer_thompsonJ_le_cgsIn (hT2 := d.c.setting.qtfe.sylow.1.to_le S_le_T152)
      d.S_ne_bot ⟨d.c.X_le_I hx, h hx⟩
  rw [← baum_eq152 d.c.inputs] at h1
  exact cgs_le152 d.c.inputs h1

theorem isPSL_quot :
    IsPSL 4 2 1 (↥X ⧸ CFSG.pCore 2 ↥X) ∨ IsPSL 5 2 1 (↥X ⧸ CFSG.pCore 2 ↥X) := by
  rcases d.ln with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl (LRed4.isPSL_two_of_statedSL' (by norm_num) e)
  · obtain ⟨e⟩ := h
    exact Or.inr (LRed4.isPSL_two_of_statedSL' (by norm_num) e)

theorem isSimple_quot : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := by
  rcases d.isPSL_quot with h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1 h).2

theorem sylow_sup : IsSylowTwoOf (sOf152 T Mc M B₀) (X ⊔ sOf152 T Mc M B₀) :=
  A4.isSylowTwoOf_mono d.c.sylow le_sup_right
    (sup_le d.c.X_le_I (S_le_I152 d.c.inputs))

theorem isTwoReduced_W :
    IsElemAbelian 2 (uOf1527 (zSOf T Mc M B₀) X) ∧
      IsTwoReducedIn (X ⊔ sOf152 T Mc M B₀) (uOf1527 (zSOf T Mc M B₀) X) :=
  isTwoReducedIn_conjClosure_sup1527d d.sylow_sup d.S_le_normalizer_X d.c.charTwoX
    d.c.inputs.h14.zS_eq.le

theorem not_le_centralizer_W (hF : ¬ X ≤ Mc) :
    ¬ X ≤ Subgroup.centralizer (uOf1527 (zSOf T Mc M B₀) X : Set G) := by
  intro hc
  apply hF
  intro x hx
  exact (centralizer_zS_le_inf152 d.c.inputs
    (Subgroup.centralizer_le (le_conjClosure _ X) (hc hx))).1

theorem lemma15127Concl_of (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (hF : ¬ X ≤ Mc) : Lemma15127Concl (zSOf T Mc M B₀) X := by
  have hXI : X ≤ I := d.c.X_le_I
  have hSN : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (X : Set G) := d.S_le_normalizer_X
  obtain ⟨hUe, hred⟩ := d.isTwoReduced_W
  have : IsMulCommutative ↥(uOf1527 (zSOf T Mc M B₀) X) := hUe.1
  have hLU := d.not_le_centralizer_W hF
  have hSQ : SQTKGroup ↥X := IsSQTKIn.mono d.c.hyp.sqtk hXI
  have hsimple := d.isSimple_quot
  have hJ : ⁅X, thompsonJ (sOf152 T Mc M B₀)⁆ = X :=
    commutator_thompsonJ_eq1527d rfl d.sylow_sup hSN (perfect_of_mem_cComp d.c.comp) hsimple le_rfl
      d.not_le_normalizer_thompsonJ
  have hLY : X ≤ X ⊔ sOf152 T Mc M B₀ := le_sup_left
  have hYL : X ⊔ sOf152 T Mc M B₀ ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hSN
  have hY2 : ∀ y ∈ X ⊔ sOf152 T Mc M B₀, ∃ e : ℕ, y ^ 2 ^ e ∈ X :=
    InternalSec.two_of_sup d.sylow_sup.2.1 hSN
  have hB := b51Hyp_1527d d.sylow_sup hLY hYL hY2 hUe hred d.c.quasi hsimple hSQ hLU hJ.symm
  have hLN : X ≤ Subgroup.normalizer (uOf1527 (zSOf T Mc M B₀) X : Set G) := hLY.trans hred.2.1
  have hO2 : pCoreOf 2 (autOn (X ⊔ sOf152 T Mc M B₀) (uOf1527 (zSOf T Mc M B₀) X)) = ⊥ :=
    Setup.pCoreOf_autOn_eq_bot hred
  have hO2L : pCoreOf 2 (autOn X (uOf1527 (zSOf T Mc M B₀) X)) = ⊥ :=
    pCoreOf_autOn_L_eq_bot1527d hLY hYL hO2
  have hker : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (uOf1527 (zSOf T Mc M B₀) X : Set G)) :=
    isPGroup_ker_of_simple hLN hsimple hO2L hLU
  obtain ⟨e⟩ := autOn_equiv_quotient1527d hLN hO2L hker
  have hK : IsPSL 4 2 1 ↥(autOn X (uOf1527 (zSOf T Mc M B₀) X)) ∨
      IsPSL 5 2 1 ↥(autOn X (uOf1527 (zSOf T Mc M B₀) X)) :=
    d.isPSL_quot.imp (isPSL_congr1527d e.symm) (isPSL_congr1527d e.symm)
  refine ⟨hUe, ?_⟩
  have hV2 : ∀ v : ↥(uOf1527 (zSOf T Mc M B₀) X), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hUe.2 v v.2)
  have := @alt15127_of_b51 h51 hI16 hA8 ↥(uOf1527 (zSOf T Mc M B₀) X) (commGroupOfElemAbelian hUe)
    _ hV2 _ _ hB hK
  rw [commV_autOn_eq1527d hLN] at this
  exact this

end CData

end C

end S15223P4

end CFSG.Quasithin

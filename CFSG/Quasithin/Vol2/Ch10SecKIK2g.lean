module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2f
public import CFSG.Quasithin.Vol2.Ch10SecQ4A12
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312SL2Native
public import CFSG.Quasithin.Vol2.Ch10SecCFacts2
public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Quasithin.Vol2.Ch10SecKIK2b
public import CFSG.Quasithin.Vol2.Ch10SecKIK2d
public import CFSG.Quasithin.Vol2.Ch10SecKIK4a
public import CFSG.Quasithin.Vol2.Ch10SecQ4A11

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  push Not at hab
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hab⟩⟩
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ Subgroup.center Q)
      (f := QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.center Q) inferInstance

variable {Γ : Type} [Group Γ] [Finite Γ] {H R J L V : Subgroup Γ} {hV : IsElemAbelian 2 V}

theorem s5_basic (hc : S5Core H R J L V hV) :
    J ≤ H ∧ J ≤ Subgroup.normalizer (V : Set Γ) ∧
      pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ) ∧ (∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) ∧
      ¬ J ≤ Subgroup.centralizer (V : Set Γ) := by
  obtain ⟨-, -, hRsyl, hJcomp, hHJ, hJR, -, hred, -, -, -, -, hLJ, -, -, hLV, -⟩ := hc
  have hJH : J ≤ H := le_of_mem_cComp hJcomp
  refine ⟨hJH, hJH.trans hred.2.1, pCoreOf_le_centralizer hred hJH hHJ, ?_,
    fun h => hLV (hLJ.trans h)⟩
  rw [← hJR]
  exact InternalSec.two_of_sup hRsyl.2.1 (hRsyl.1.trans hHJ)

theorem lbar_mem_lFamily (hc : S5Core H R J L V hV) :
    IsSylowTwoOf (((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) ⊤ ∧
      modO2Image J L ∈
        lFamily (((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) := by
  obtain ⟨-, -, hRsyl, hJcomp, -, -, -, -, -, -, -, hLfam, hLJ, -⟩ := hc
  refine ⟨C10E4.isSylowTwoOf_quot hRsyl hJcomp, ?_⟩
  have hJsyl : IsSylowTwoOf (R ⊓ J) J :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hJcomp) hRsyl
  have hLfam' : L ∈ lFamily (R ⊓ J) :=
    cComp_mem_of_le (show L ∈ cComp (L ⊔ R) from hLfam) le_sup_left
      (sup_le_sup_left inf_le_left L)
  exact modO2Image_mem_lFamily hJsyl hLJ hLfam'

theorem isQuasisimple_quot (h36 : A36ForSQTK) (h56 : AsB56) (hc : S5Core H R J L V hV) :
    CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := by
  obtain ⟨hJH, hJN, hO, h2, -⟩ := s5_basic hc
  obtain ⟨hTs, hB⟩ := lbar_mem_lFamily hc
  obtain ⟨hSQH, -, hRsyl, hJcomp, hHJ, -, -, hred, -, hJq', hJRV, -, hLJ, -, -, -, hne⟩ := hc
  have hJq := isQuasisimple_of_open hJq'
  have hlist := b56List_autI h56 hV hSQH hRsyl hred hJH hHJ h2 hJq hJRV
  have hYc := C10E4.sqtkHypCat_quot hJH (SQTKGroup.isSQTKCat hSQH)
  have h36Y := h36 _ (sqtkHyp_of_cat hYc)
  have hT := C10E4.top_mem_cComp_quot hJcomp
  by_contra hnq
  have hnq' : ¬ CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) := fun h =>
    hnq ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr Subgroup.topEquiv).mp h)
  rcases A312.nonquasi_of_lFamily Vol2Native.a312SL2Fact hTs hT le_top hB (h36Y ⊤ hT) hnq' with
    ⟨-, hsup, -⟩ | ⟨-, ⟨p, hp, hp5, hp8, hpSL⟩, -⟩
  · apply hne
    set Y := ↥J ⧸ CFSG.pCore 2 ↥J
    set OL : Subgroup Y := (CFSG.oddCore ↥(⊤ : Subgroup Y)).map (⊤ : Subgroup Y).subtype
    have hsurj : Function.Surjective (⊤ : Subgroup Y).subtype := fun y => ⟨⟨y, trivial⟩, rfl⟩
    have : OL.Normal := Subgroup.Normal.map inferInstance _ hsurj
    have : Group.IsSolvable ↥(CFSG.oddCore ↥(⊤ : Subgroup Y)) := A312.oddCore_isSolvable _
    have hNs : Group.IsSolvable ↥OL := Group.isSolvable_of_surjective
      ((⊤ : Subgroup Y).subtype.subgroupMap_surjective (CFSG.oddCore ↥(⊤ : Subgroup Y)))
    exact autI_eq_of_sup hV hJN hO hJq hLJ hNs hsup.symm
  · exact false_of_sl2_quot (piJ hV hJN hO) (piJ_surjective hV hJN hO) hJq hlist hp hp8 hp5 hpSL

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

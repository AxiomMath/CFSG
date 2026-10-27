module

public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.EmptyFaithful.T1515dE
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.InternalSec
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem lemma15127_core1527d (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h18 : Lemma15118Concl T Mc M Z₁) (hL : IsL1519 Mc Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) (h25 : Lemma15125Concl T Z₁ V₁ L)
    (h26 : Lemma15126Concl L) (hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M)
    (hLM : ¬ L ≤ M) : Lemma15127Concl Z₂ L := by
  have hq := hC.qtfe
  have hM := hC.mf
  have hS := hC.setting
  set S := s1516 T Z₁ with hSdef
  have hLG1 : L ≤ g1_1516 Z₁ := le_of_mem_cComp hL.comp
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    have h1 : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
      rw [h25.one]
      exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_oPrimeResidualOf1516 3 _)
    exact (s1516_le_g1 T Z₁).trans h1
  have hSsyl : IsSylowTwoOf S (L ⊔ S) :=
    A4.isSylowTwoOf_mono h18.four le_sup_right (sup_le hLG1 (s1516_le_g1 T Z₁))
  have hF : CharTwo L := h26.1
  have hsmall : Ce15Small T Mc M := ce15Small_of_four_or_six h24.one
  have hnot7 : ¬ Ce15Seven T Mc M := not_seven_of_four_or_six h24.one
  obtain ⟨hdiag1, hdiag2⟩ := hS.diagonal hsmall hnot7
  have hZ2V : Z₂ ≤ V154 T Mc M := hS.z2_le_V
  have hVe : IsElemAbelian 2 (V154 T Mc M) := hS.V_isElemAbelian hq hM
  have hZ2e : IsElemAbelian 2 Z₂ := isElemAbelian_mono151 hZ2V hVe
  have hZ2T : Z₂ ≤ T := hZ2V.trans (hS.V_le_T hq hM)
  have hZ2S : Z₂ ≤ S := by
    intro z hz
    rw [hSdef, hdiag2]
    refine ⟨hZ2T hz, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have := hZ2e.1
    exact congrArg Subtype.val (mul_comm' (⟨h, hh⟩ : Z₂) ⟨z, hz⟩)
  have hSZ2 : S ≤ Subgroup.centralizer (Z₂ : Set G) := by
    rw [hSdef, hdiag2]
    exact inf_le_right
  have hZ : Z₂ ≤ quasithinOmegaOneCenter S := by
    intro z hz
    refine Subgroup.subset_closure ⟨⟨hZ2S hz, ?_⟩, hZ2e.2 z hz⟩
    exact Subgroup.mem_centralizer_iff.2 fun s hs =>
      (Subgroup.mem_centralizer_iff.mp (hSZ2 hs) z hz).symm
  obtain ⟨hUe, hred⟩ := isTwoReducedIn_conjClosure_sup1527d hSsyl hSN hF hZ
  have : IsMulCommutative ↥(conjClosure Z₂ L) := hUe.1
  have hLU : ¬ L ≤ Subgroup.centralizer (conjClosure Z₂ L : Set G) := by
    intro hc
    apply hL.not_le
    intro x hx
    have hx2 : x ∈ Subgroup.centralizer (Z₂ : Set G) :=
      Subgroup.centralizer_le (le_conjClosure Z₂ L) (hc hx)
    have hx3 : x ∈ g1_1516 Z₁ ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [hdiag1]
      exact ⟨hLG1 hx, hx2⟩
    exact ⟨hLG1 hx, hq.centralizer_le_mc hx3.2⟩
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hS.pCore_g1_ne_bot hq hM
  have hsqtk : IsSQTKIn (g1_1516 Z₁) :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc,
      kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc⟩
  have hSQ : SQTKGroup ↥L := hsqtk.mono hLG1
  have hPSL : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := h26.2
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hPSL with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1 h).2
  have hq' : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hL.quasi
  have hJ : ⁅L, thompsonJ S⁆ = L :=
    commutator_thompsonJ_eq1527d rfl hSsyl hSN (perfect_of_mem_cComp hL.comp) hsimple hNJ hLM
  have hLY : L ≤ L ⊔ S := le_sup_left
  have hYL : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSN
  have hY2 : ∀ y ∈ L ⊔ S, ∃ e : ℕ, y ^ 2 ^ e ∈ L := InternalSec.two_of_sup hSsyl.2.1 hSN
  have hB := b51Hyp_1527d hSsyl hLY hYL hY2 hUe hred hq' hsimple hSQ hLU hJ.symm
  have hLN : L ≤ Subgroup.normalizer (conjClosure Z₂ L : Set G) := hLY.trans hred.2.1
  have hO2 : pCoreOf 2 (autOn (L ⊔ S) (conjClosure Z₂ L)) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2L : pCoreOf 2 (autOn L (conjClosure Z₂ L)) = ⊥ :=
    pCoreOf_autOn_L_eq_bot1527d hLY hYL hO2
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (conjClosure Z₂ L : Set G)) :=
    isPGroup_ker_of_simple hLN hsimple hO2L hLU
  obtain ⟨e⟩ := autOn_equiv_quotient1527d hLN hO2L hker
  have hK : IsPSL 4 2 1 ↥(autOn L (conjClosure Z₂ L)) ∨ IsPSL 5 2 1 ↥(autOn L (conjClosure Z₂ L)) :=
    hPSL.imp (isPSL_congr1527d e.symm) (isPSL_congr1527d e.symm)
  refine ⟨hUe, ?_⟩
  have hV2 : ∀ v : ↥(conjClosure Z₂ L), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hUe.2 v v.2)
  have := @alt15127_of_b51 h51 hI16 hA8 ↥(conjClosure Z₂ L) (commGroupOfElemAbelian hUe) _ hV2 _ _
    hB hK
  rw [commV_autOn_eq1527d hLN] at this
  exact this

theorem lemma15127InputU_of (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (h1416 : StageLemma1416) (h15 : StageLemma1515CE) : Lemma15127InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26
  have hq := hC.qtfe
  have hM := hC.mf
  have hpc : pCoreOf 2 (g1_1516 Z₁) ≠ ⊥ := hC.setting.pCore_g1_ne_bot hq hM
  have hL20 : IsL1520 T Mc Z₁ L := hL.isL1520 h18.four hpc
  have hLM : ¬ L ≤ M :=
    lemma_15_1_20_one (h1416 G T Mc hq).1 hM (h15 G T Mc M hq hM hC.ce) hL20
  have hS1 : s1516 T Z₁ ≠ ⊥ := fun h =>
    hpc (le_bot_iff.1 (h ▸ pCoreOf_le_of_isSylowTwoOf h18.four))
  have hNJ : Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS h18.four.2.1 hS1).trans h17.cgs
  exact lemma15127_core1527d h51 hI16 hA8 hC h18 hL h24 h25 h26 hNJ hLM

end CFSG.Quasithin

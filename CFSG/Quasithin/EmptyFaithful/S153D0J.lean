module

public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153Plus

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem VZ_le_Sgp153 (h : Hyp15310 G T Mc M V₁ V₂ Yp t) : VZ T M ≤ Sgp153 T V₁ :=
  le_inf h.hyp.VZ_le_T fun _ hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun _ hw =>
      B2F.isElemAbelian_comm h.hyp.elemAbelian (h.decomp.le₁ hw) hv)

theorem le_of_thompsonJ_le_of_centralizes (h11 : StageLemma14111)
    (h : Hyp15310 G T Mc M V₁ V₂ Yp t) {I : Subgroup G} (hsyl : IsSylowTwoOf (Sgp153 T V₁) I)
    (hA : thompsonJ T ≤ Subgroup.centralizer (VZ T M : Set G)) (hJM : thompsonJ I ≤ M) :
    I ≤ M := by
  have hSp : IsPGroup 2 (Sgp153 T V₁) := h.hyp.qtfe.sylow.1.to_le inf_le_left
  have hS1 : Sgp153 T V₁ ≠ ⊥ := by
    intro hbot
    have hV : VZ T M = ⊥ := le_bot_iff.mp (hbot ▸ VZ_le_Sgp153 h)
    have h16 := h.hyp.card_VZ
    rw [hV, Subgroup.card_bot] at h16
    omega
  have hJS : thompsonJ (Sgp153 T V₁) ≤ thompsonJ I := thompsonJ_le_thompsonJ_of_isSylowTwoOf hsyl
  have hCGS : CGS (baum T) ≤ M := (h.hyp.lemma_14_1_2_of_le hA).2.2.2
  have hbaum : baum T = baum (Sgp153 T V₁) := (Hyp153.lemma_15_3_6 h11 h.hyp h.decomp).1
  have hN : Subgroup.normalizer (thompsonJ (Sgp153 T V₁) : Set G) ≤ M :=
    (S1414.normalizer_thompsonJ_le_CGS hSp hS1).trans (hbaum ▸ hCGS)
  have hIN : I ≤ Subgroup.normalizer (thompsonJ I : Set G) :=
    Subgroup.le_normalizer.trans (GammaExtra.normalizer_le_normalizer_thompsonJ I)
  intro g hg
  obtain ⟨n, hn, y, hy, rfl⟩ := S1414.frattini_decomp hsyl (thompsonJ_le_self I) hIN hJS g hg
  exact M.mul_mem (hJM hn) (hN hy.2)

end S153D

end CFSG.Quasithin

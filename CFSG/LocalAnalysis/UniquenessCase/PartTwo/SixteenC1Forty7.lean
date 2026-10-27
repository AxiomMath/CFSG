module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47D
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Hv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1ChoiceDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_eTwo_le_cTilde (D : Data G) (hkit : OmegaKit) (h43 : R16_43_1 D) (h45 : R16_45 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) (hne : V₀ ≠ ⊥) {z : G}
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z))
    (hC : V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) ≤
      pCoreOf 2 (centralizer ({z} : Set G)))
    (hgap : ∀ h ∈ centralizer ({z} : Set G), V ≤ conjSubgroup D.M h →
      ¬ conjSubgroup V h ≤ D.M →
      conjSubgroup (V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G))
        h ≤ F11.CTilde D.M V₀ V) :
    eTwo D V₀ z ≤ F11.CTilde D.M V₀ V := by
  rw [eTwo, hConjClosure]
  apply iSup_le
  intro h
  exact s16c1_conj_le_cTilde D hkit h43 h45 hS hc hne hSyl hcard hC h.2 (hgap h h.2)

theorem r16_47_ne_of_gap (D : Data G) (hkit : OmegaKit) (h43 : R16_43_1 D) (h45 : R16_45 D)
    (hg : R16_47_ne_gap D) : R16_47_ne D := by
  intro V₀ V L hV hS hc hL hU4 hne x hx hSyl h47 hch
  obtain ⟨hg1, hg2⟩ := hg
  have hC := hg1 V₀ V L hV hS hc hL hU4 hne x hx hSyl h47 hch
  have hz : x.val ∈ V := x.val_mem
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hcard := s16c1_card_V_eq_two_mul_uOne hV hz h47
  have hEC : eTwo D V₀ x.val ≤ F11.CTilde D.M V₀ V :=
    s16c1_eTwo_le_cTilde D hkit h43 h45 hS hc hne hSyl hcard hC
      (fun h hh h1 h2 => hg2 V₀ V L hV hS hc hL hU4 hne x hx hSyl h47 hch hC h hh h1 h2)
  exact ⟨s16c1_phi_eTwo D hP.elemAbelian₀ hSyl hC,
    s16c1_ti_uTwo D (s16c1_ti_V₀ hS hne),
    s16c1_comm_V_eTwo_le_uTwo D hV hz hP.le_normalizer hP.le_normalizer₀ hEC⟩

theorem r16_47z_of (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) (h41 : R16_41 D) (h42 : R16_42 D) (h43 : R16_43_1 D) (h45 : R16_45 D)
    (h45b : R16_45b D) (hg : R16_47_ne_gap D) (h47ch : R16_47ch D) : R16_47z D := by
  intro V₀ V L hV hS hc hL hU4
  obtain ⟨x, hx, h47, hch⟩ := h47ch V₀ V L hV hS hc hL hU4
  refine ⟨x, hx, h47, ?_⟩
  by_cases hbot : V₀ = ⊥
  · subst hbot
    exact r16_47a_bot_of D hSg h1219 hkit h41 h42 h43 h45b hS hc hx h47
  · obtain ⟨-, hSyl, -⟩ := h45b V₀ V L hV hS hc x hx
    exact ⟨fun h => absurd h hbot, fun _ =>
      r16_47_ne_of_gap D hkit h43 h45 hg V₀ V L hV hS hc hL hU4 hbot x hx hSyl h47 hch⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

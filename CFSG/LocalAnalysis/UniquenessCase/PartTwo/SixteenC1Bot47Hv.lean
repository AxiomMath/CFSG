module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47HvA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47HvB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47HvC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSetupB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_not_comm_le_zpowers (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hkit : OmegaKit) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L) (hr : (4 : ℕ∞) < rMV D.M V)
    (h43 : R16_43_1 D) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hV64 : Nat.card ↥V = 64) (hU32 : Nat.card ↥(uOne V z) = 32) :
    ¬ ⁅V, eOne V z⁆ ≤ Subgroup.zpowers z := by
  intro hVE
  have hcent := s16c1_uOne_conj_le_centralizer D hkit hS hc h43 hz hz1 hSyl hV64 hU32 hVE
  have hle := s16c1_conjV_le_M D hV hV64 hr hU32 hcent
  have hcomm := s16c1_comm_V_conjV D hSg h1219 hkit hS hc hr h43 hz hz1 hle
  have hVP := s16c1_V_le_pCoreOf_of_comm hV hz hcomm
  have hVU : V ≤ uOne V z := le_inf le_rfl hVP
  have hcard := Subgroup.card_le_of_le hVU
  omega

theorem s16c1_hv (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) (hr : (4 : ℕ∞) < rMV D.M V) (h41 : R16_41 D)
    (h43 : R16_43_1 D) {x : IntMod V hV} (hx1 : x.val ≠ 1)
    (hsing : ∀ Q : Vtil (⊥ : Subgroup G) V hV → ZMod 2, IsMinusQuadF2 Q →
      QuadInvariant Q (lBar ⊥ V hV L) → Q (mkTil ⊥ V hV x) = 0)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)))
    (h47 : Concl1647 V x.val) :
    uOne V x.val ≤ ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val := by
  have hV64 := s16c1_card_V_of_case D hc
  have hz : x.val ∈ V := x.val_mem
  have hU32 := s16c1_card_uOne hV hz hV64 h47
  have hMV : D.M ≤ normalizer (V : Set G) :=
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hP : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ normalizer (V : Set G) :=
    (s16c1_pCoreOf_le_M D hSyl).trans hMV
  have hNU : ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val ≤ uOne V x.val :=
    s16c1_comm_V_eOne_sup_le hV hz hP
  rcases s16c1_card_N_cases D hkit hS hc h41 hx1 hsing hSyl hV64 h47 with h2 | h32
  · exfalso
    have hzN : Subgroup.zpowers x.val ≤ ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val := le_sup_right
    have hcardz : Nat.card ↥(Subgroup.zpowers x.val) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hV.2 x.val hz) hx1
    have hEq : Subgroup.zpowers x.val = ⁅V, eOne V x.val⁆ ⊔ Subgroup.zpowers x.val :=
      Subgroup.eq_of_le_of_card_ge hzN (by rw [hcardz, h2])
    exact s16c1_not_comm_le_zpowers D hSg h1219 hkit hS hc hr h43 hz hx1 hSyl hV64 hU32
      (le_sup_left.trans hEq.ge)
  · exact (Subgroup.eq_of_le_of_card_ge hNU (by rw [h32, hU32])).ge

theorem r16_47a_bot_of (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) (h41 : R16_41 D) (h42 : R16_42 D) (h43 : R16_43_1 D) (h45b : R16_45b D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (h47 : Concl1647 V x.val) : Concl1647a D ⊥ V x.val := by
  obtain ⟨hsing, hSyl, -, -, -⟩ := h45b ⊥ V L hV hS hc x hx
  have hr : (4 : ℕ∞) < rMV D.M V := (h42 ⊥ V L hV hS hc).2.2 rfl
  have hz : x.val ∈ V := x.val_mem
  have hMV : D.M ≤ normalizer (V : Set G) :=
    hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hcore := s16c1_core_bot D hSg h1219 hkit hS hc hr hz hx.ne_one
  have hv := s16c1_hv D hSg h1219 hkit hS hc hr h41 h43 hx.ne_one hsing hSyl h47
  exact ⟨fun _ => s16c1_concl1647a_bot_of D hV hz hMV hSyl hcore hv, fun h => absurd rfl h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

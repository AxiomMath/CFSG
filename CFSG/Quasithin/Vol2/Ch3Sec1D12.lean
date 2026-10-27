module

public import CFSG.Quasithin.Vol2.Ch3Sec1Aux
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section D11

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

omit [Finite G] in
theorem noNormal_of_not_exists
    (h : ¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)) :
    ∀ N : Subgroup G, N ≤ pCoreOf 2 M₀ → (N.subgroupOf (M₀ ⊔ H)).Normal → N = ⊥ := by
  intro N hN hnorm
  by_contra hne
  apply h
  refine ⟨N, hne, hN, ?_⟩
  have hNK : N ≤ M₀ ⊔ H := (hN.trans (pCoreOf_le 2 M₀)).trans le_sup_left
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hnorm

theorem Hyp315Base.d11Hyp (hT : quasithinIsSylowTwo T) (h : Hyp315Base T M M₀ H V) (hV0 : V ≠ ⊥)
    (hno : ∀ N : Subgroup G, N ≤ pCoreOf 2 M₀ → (N.subgroupOf (M₀ ⊔ H)).Normal → N = ⊥) :
    D11Hyp M₀ H T V (H ⊓ M) :=
  ⟨isSylowTwoOf_of_isSylowTwo hT h.T_le, isSylowTwoOf_of_isSylowTwo hT h.hStar.1.1, h.reduced,
    hV0, h.isUniqueMaxOver hT, h.centralizer, hno⟩

end D11

section FFInt

variable {G : Type*} [Group G] [Finite G]

theorem isFFInt_iff_qInt_le_one (X V : Subgroup G) (hV : IsElemAbelian 2 V) :
    IsFFInt X V hV ↔ qInt X V hV ≤ 1 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [pow_two] using hV.2 v v.2)
  exact (B1_4_5 hV2 (autOn X V)).out 1 3

end FFInt

section D12

variable {G : Type*} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

namespace D11Hyp

theorem V_le_T (hD : D11Hyp G₁ G₂ T V M₂) : V ≤ T :=
  (A4.le_pCoreOf_of_isTwoReducedIn hD.reduced).trans (hD.centralizer ▸ inf_le_left)

theorem pCoreOf_le_T (hD : D11Hyp G₁ G₂ T V M₂) : pCoreOf 2 G₁ ≤ T :=
  hD.centralizer ▸ inf_le_left

theorem T_ne_bot (hD : D11Hyp G₁ G₂ T V M₂) : T ≠ ⊥ :=
  fun h => hD.nontrivial (le_bot_iff.mp (h ▸ hD.V_le_T))

variable [Finite G]

theorem thompsonJ_le (hD : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V hD.reduced.2.2.1) :
    thompsonJ T ≤ pCoreOf 2 G₁ := by
  refine iSup₂_le fun A hA => ?_
  rw [hD.centralizer]
  refine le_inf hA.1 ?_
  by_contra hAC
  exact hnff (isFFModule_autOn hD.reduced.2.2.1 hD.V_le_T hD.reduced.2.1
    (hA.1.trans hD.sylow₁.1) hA hAC)

theorem thompsonJ_eq (hD : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V hD.reduced.2.2.1) :
    thompsonJ T = thompsonJ (pCoreOf 2 G₁) :=
  (B6.thompsonJ_eq_of_le (hD.thompsonJ_le hnff) hD.pCoreOf_le_T).symm

theorem not_thompsonJ_le_pCoreOf (hD : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V hD.reduced.2.2.1) :
    ¬ thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₂ := by
  intro hle
  have hJT := hD.thompsonJ_eq hnff
  have hR₂T : pCoreOf 2 G₂ ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hD.sylow₂
  have hJ₂ : thompsonJ (pCoreOf 2 G₂) = thompsonJ T :=
    B6.thompsonJ_eq_of_le (hJT ▸ hle) hR₂T
  have h2 : G₂ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJ₂]
    exact (le_normalizer_pCoreOf 2 G₂).trans (normalizer_le_normalizer_thompsonJ _)
  have h1 : G₁ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [hJT]
    exact (le_normalizer_pCoreOf 2 G₁).trans (normalizer_le_normalizer_thompsonJ _)
  have hJR : thompsonJ T ≤ pCoreOf 2 G₁ := hD.thompsonJ_le hnff
  have hnorm : ((thompsonJ T).subgroupOf (G₁ ⊔ G₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hJR.trans ((pCoreOf_le 2 G₁).trans le_sup_left))).mpr (sup_le h1 h2)
  exact thompsonJ_ne_bot_of_isPGroup hD.sylow₁.2.1 hD.T_ne_bot (hD.no_normal _ hJR hnorm)

theorem minParabolic (hD : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V hD.reduced.2.2.1) :
    MinParabolic G₂ T M₂ := by
  refine ⟨hD.sylow₂, ?_, hD.unique_max⟩
  intro hN
  have hRT : pCoreOf 2 G₂ = T :=
    le_antisymm (B6.pCoreOf_two_le_of_isSylowTwoOf hD.sylow₂)
      (le_pCoreOf_of_le_normalizer 2 hD.sylow₂.1 hN hD.sylow₂.2.1)
  apply hD.not_thompsonJ_le_pCoreOf hnff
  rw [hRT]
  exact (B6.thompsonJ_le _).trans hD.pCoreOf_le_T

end D11Hyp

end D12

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R35
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.WeakClosure81.FourteenUncond

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem Hyp125.inCalV0_or {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    InCalV0 D.M V₀ V ∨ (V₀ = ⊥ ∧ InCalV D.M V) := by
  rcases h.1 with ⟨hW, h0⟩ | ⟨h0, -, -⟩
  · exact Or.inr ⟨h0, hW.1.1.1⟩
  · exact Or.inl h0

theorem hyp64_of_hyp125 {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {n : ℕ} {g : G}
    (hO : InCalOStar n D.M V₀ V g) : Hyp64 n D.M V₀ V g := by
  rcases h.inCalV0_or with h0 | ⟨h0, hVV⟩
  · exact ⟨h0.2.1.2.2.2, h0.2.2.1, normalizer_eq_of_inCalV D h0.2.1, h0.1.2.2.1,
      fun _ => h0.2.2.2.1, fun _ => normalizer_eq_of_inCalV D h0.1, hO⟩
  · subst h0
    refine ⟨hVV.2.2.2, bot_le, normalizer_eq_of_inCalV D hVV, ?_,
      fun h => absurd rfl h, fun h => absurd rfl h, hO⟩
    rw [Subgroup.normalizer_eq_top]
    exact le_top

theorem mQuot_UOf_le {M V₀ V : Subgroup G} {g : G} {n : ℕ} (hO : InCalOStar n M V₀ V g) :
    E3.mQuot V (UOf M V g) ≤ n := by
  unfold UOf
  rw [mQuot_inf_left]
  exact hO.1.1.2.1

section Certified

theorem barSub_BOf_mem_aSet_two (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D)
    (hext : DataExt D) (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {m : ℕ} (hm : Case1633 D V₀ V hV L m) {n : ℕ} (hn : n + 2 ≤ 2 * m)
    {g : G} (hO : InCalOStar n D.M V₀ V g) :
    barSub V₀ V hV (BOf D.M V g) ≠ ⊥ ∧
      barSub V₀ V hV (BOf D.M V g) ∈ E3.aSet 2 (Mbar D.M V₀ V hV) := by
  have hH16 : Hyp16 D V₀ V := hS.setting.hyp16
  have h64 : Hyp64 n D.M V₀ V g := hyp64_of_hyp125 hH16.hyp125 hO
  have hA1 : barSub V₀ V hV (BOf D.M V g) ≠ ⊥ := barSub_BOf_ne_bot_uncond h64
  refine ⟨hA1, ?_⟩
  obtain ⟨hδ, hr⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
  set B : Subgroup G := BOf D.M V g with hBdef
  have hi' : E3.mQuot (conjSubgroup V g) B ≤ n := by
    have h1 : E3.mQuot (conjSubgroup V g) B = E3.mQuot (conjSubgroup V g) D.M := by
      unfold E3.mQuot
      rw [hBdef, BOf, inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    exact hO.1.2.2.1
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) D.M :=
    ⟨inf_le_right, g, inf_le_left, rfl⟩
  have hrk : ((2 + E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + E3.mQuot (conjSubgroup V g) B + mSub V₀ ≤
      2 * m + mSub V₀)) hr
  have hδ2 : ((2 + E3.mQuot (conjSubgroup V g) B : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + E3.mQuot (conjSubgroup V g) B ≤ 2 * m)) hδ
  exact barSub_mem_calABar_of_gammaSet D hSg h1219 h21 h22 hH16 hrk hδ2 hBγ hA1

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

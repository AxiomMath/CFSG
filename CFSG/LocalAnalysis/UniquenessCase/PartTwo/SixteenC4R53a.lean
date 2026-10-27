module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_r53a (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {i k : ℕ} {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M)
    {g : G} (hAg : A ≤ conjSubgroup V g)
    (hr : ((k + i + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V) (hVg : ¬ V ≤ conjSubgroup D.M g) :
    k ≤ E3.mQuot (barSub V₀ V hV A) ⊥ := by
  by_contra hlt
  have hlt' : E3.mQuot (barSub V₀ V hV A) ⊥ < k := not_le.1 hlt
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hAM : A ≤ D.M := hA.1
  have hAst : A ≤ stabTil V₀ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  set B₀ : Subgroup G := preBarSub A V₀ V hV ⊥ with hB₀def
  have hB₀A : B₀ ≤ A := inf_le_left
  have hB₀M : B₀ ≤ D.M := hB₀A.trans hAM
  have hB₀g : B₀ ≤ conjSubgroup V g := hB₀A.trans hAg
  have hbarB₀ : barSub V₀ V hV B₀ = ⊥ := by
    rw [hB₀def, barSub_preBarSub]
    exact bot_inf_eq _
  have hAB₀ : E3.mQuot A B₀ = E3.mQuot (barSub V₀ V hV A) ⊥ := by
    rw [hB₀def, ← mQuot_barSub_preBarSub_gen hV hAst bot_le]
  have hmq : E3.mQuot (conjSubgroup V g) A = i := mQuot_eq_of_mem_gammaSet hA hAg
  have hjm : E3.mQuot (conjSubgroup V g) B₀ = i + E3.mQuot (barSub V₀ V hV A) ⊥ := by
    rw [E3.mQuot_add hB₀A hAg, hAB₀, hmq]
    omega
  have hB₀Γ : B₀ ∈ E3.gammaSet V (i + E3.mQuot (barSub V₀ V hV A) ⊥) D.M :=
    ⟨hB₀M, g, hB₀g, hjm⟩
  have hi : ((i + E3.mQuot (barSub V₀ V hV A) ⊥ + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le
      (by exact_mod_cast (by omega : i + E3.mQuot (barSub V₀ V hV A) ⊥ + mSub V₀ <
        k + i + mSub V₀)) hr
  obtain ⟨-, hc2, hc3⟩ := sixteen_twentyThree_one D h22 hS.setting.hyp16 hB₀Γ hB₀g hi
  have hVc : V ≤ centralizer (B₀ : Set G) := fun v hv => hc2 v hv fun a ha => by
    have hstab : a ∈ stabTil V₀ V := hAst (hB₀A ha)
    have hact : actTil V₀ V hV ⟨a, hstab⟩ ∈ barSub V₀ V hV B₀ :=
      actTil_mem_barSub V₀ V hV ha hstab
    rw [hbarB₀, Subgroup.mem_bot] at hact
    have hcomm : a * v * a⁻¹ * v⁻¹ ∈ V₀ :=
      (actTil_eq_one_iff V₀ V hV ⟨a, hstab⟩).1 hact v hv
    have hav : ⁅a, v⁆ ∈ V₀ := by rwa [commutatorElement_def]
    rw [← commutatorElement_inv]
    exact V₀.inv_mem hav
  exact hVg (le_trans (le_inf le_rfl hVc) hc3)

theorem s16c4_preTil_fixV_le (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {i : ℕ} {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) {g : G} (hAg : A ≤ conjSubgroup V g)
    {Q : Subgroup (MulAut (Vtil V₀ V hV))} (hQ : Q ≤ barSub V₀ V hV A)
    (hi : ((i + E3.mQuot (barSub V₀ V hV A) Q + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) :
    preTil V₀ V hV (fixV Q) ≤ conjSubgroup D.M g := by
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hAM : A ≤ D.M := hA.1
  have hAst : A ≤ stabTil V₀ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  set B : Subgroup G := preBarSub A V₀ V hV Q with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBM : B ≤ D.M := hBA.trans hAM
  have hBg : B ≤ conjSubgroup V g := hBA.trans hAg
  have hBst : B ≤ stabTil V₀ V := hBA.trans hAst
  have hbarB : barSub V₀ V hV B = Q := by
    rw [hBdef, barSub_preBarSub]
    exact inf_eq_left.2 hQ
  have hAB : E3.mQuot A B = E3.mQuot (barSub V₀ V hV A) Q := by
    rw [hBdef, ← mQuot_barSub_preBarSub_gen hV hAst hQ]
  have hmq : E3.mQuot (conjSubgroup V g) A = i := mQuot_eq_of_mem_gammaSet hA hAg
  have hjm : E3.mQuot (conjSubgroup V g) B = i + E3.mQuot (barSub V₀ V hV A) Q := by
    rw [E3.mQuot_add hBA hAg, hAB, hmq]
    omega
  have hBΓ : B ∈ E3.gammaSet V (i + E3.mQuot (barSub V₀ V hV A) Q) D.M :=
    ⟨hBM, g, hBg, hjm⟩
  obtain ⟨-, hc2, hc3⟩ := sixteen_twentyThree_one D h22 hS.setting.hyp16 hBΓ hBg hi
  have hpre := preCTilde_eq_inf_centralizer_of (V₀ := V₀) (V := V) (D := B) hV hBst hc2
  have hU : preTil V₀ V hV (fixV Q) = preCTilde V₀ V B hV := by
    unfold preCTilde
    rw [hbarB]
  rw [hU, hpre]
  exact hc3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

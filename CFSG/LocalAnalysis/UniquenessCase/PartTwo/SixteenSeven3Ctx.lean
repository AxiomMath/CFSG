module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Hyper
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLemmaP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_inCalV1_of_bot {D : Data G} {V : Subgroup G} (h : Hyp125 D ⊥ V) :
    InCalV1 D.M D.T V := by
  rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  · exact hW.1.1
  · exact absurd rfl h0.1.1

theorem s16c167_one_lt_sParam (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (h : Hyp125 D ⊥ V) (hm : 1 < mBar D.M ⊥ V h.isElemAbelian) :
    1 < E3.sParam h.isElemAbelian := by
  have hV := h.inCalV
  have h8 : 8 ≤ Nat.card V := by
    rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
    · exact hW.1.2.1
    · exact absurd rfl h0.1.1
  have hr : ((1 : ℕ) : ℕ∞) < E3.rParam V := by
    have := TwelveTen.one_lt_rMV D hx h61 hV (by omega)
    rwa [rMV_eq_rParam_of_inCalV D hV] at this
  have hm' : 1 < E3.mParam (autI hV.2.2.2 ⊤) :=
    (TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hV 1).1 ((h.mBarGT_iff_lt_mBar 1).2 hm)
  exact E3.lt_sParam_of_lt h.isElemAbelian hr hm'

theorem s16c167_sParam_eq_mBar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h111 : W3Thm111 G) {V : Subgroup G} (h16 : Hyp16 D ⊥ V)
    (hm : 1 < mBar D.M ⊥ V h16.hyp125.isElemAbelian) :
    E3.sParam h16.hyp125.isElemAbelian = mBar D.M ⊥ V h16.hyp125.isElemAbelian := by
  have h := h16.hyp125
  have hV := h.inCalV
  have hiff : ∀ n : ℕ, n < mBar D.M ⊥ V h.isElemAbelian ↔ n < E3.mParam (autI hV.2.2.2 ⊤) :=
    fun n => (h.mBarGT_iff_lt_mBar n).symm.trans
      (TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hV n)
  have h2 : mBar D.M ⊥ V h.isElemAbelian = E3.mParam (autI hV.2.2.2 ⊤) :=
    le_antisymm (not_lt.1 fun hlt => lt_irrefl _ ((hiff _).1 hlt))
      (not_lt.1 fun hlt => lt_irrefl _ ((hiff _).2 hlt))
  have hle : E3.sParam h.isElemAbelian ≤ mBar D.M ⊥ V h.isElemAbelian := by
    rw [h2]
    exact E3.sParam_le_mParam h.isElemAbelian
  have h3 : mBar D.M ⊥ V h.isElemAbelian ≤ 3 := by
    have := h16.not_gt
    rw [h.mBarGT_iff_lt_mBar] at this
    omega
  refine le_antisymm hle ?_
  rcases (show mBar D.M ⊥ V h.isElemAbelian = 2 ∨ mBar D.M ⊥ V h.isElemAbelian = 3 by omega) with
    h4 | h4
  · rw [h4]
    have := s16c167_one_lt_sParam D hx h61 h hm
    omega
  · have hm2 : MBarGT D.M ⊥ V 2 := (h.mBarGT_iff_lt_mBar 2).2 (by omega)
    have := TwelveShort.lt_sParam_of_mBarGT D h111 (s16c167_inCalV1_of_bot h) hm2 hm2
    rw [h4]
    omega

theorem s16c167_barSub_mem_calABar_of_le {M V₁ V A : Subgroup G} {m : ℕ}
    (hV : IsElemAbelian 2 V) (h1 : V₁ = ⊥) (hAM : A ≤ M) (hAst : A ≤ stabTil V₁ V)
    (hAel : IsElemAbelian 2 A) (hA1 : barSub V₁ V hV A ≠ ⊥)
    (hall : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B < m →
      V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G)) :
    barSub V₁ V hV A ∈ calABar m M V₁ V hV := by
  subst h1
  refine ⟨barSub_mono ⊥ V hV hAM, hA1, isElemAbelian2_barSub hV hAel, ?_⟩
  intro C hC hlt
  have hBA : preBarSub A ⊥ V hV C ≤ A := inf_le_left
  have hBst : preBarSub A ⊥ V hV C ≤ stabTil ⊥ V := hBA.trans hAst
  have hbarB : barSub ⊥ V hV (preBarSub A ⊥ V hV C) = C := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hC
  have hmB : E3.mQuot A (preBarSub A ⊥ V hV C) = E3.mQuot (barSub ⊥ V hV A) C :=
    (mQuot_barSub_preBarSub_gen hV hAst hC).symm
  generalize hBdef : preBarSub A ⊥ V hV C = B at hBA hBst hbarB hmB
  have hltB : E3.mQuot A B < m := by rw [hmB]; exact hlt
  have hpre : preCTilde ⊥ V B hV = preCTilde ⊥ V A hV := by
    rw [preCTilde_bot_eq hV hBst, preCTilde_bot_eq hV hAst]
    exact hall B hBA hltB
  exact (congrArg fixV hbarB).symm.trans (fixV_barSub_eq_of_preCTilde_eq hV hpre)

theorem s16c167_calABar_nonempty_of_le_conj (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h111 : W3Thm111 G) {V : Subgroup G} (h16 : Hyp16 D ⊥ V)
    (hm : 1 < mBar D.M ⊥ V h16.hyp125.isElemAbelian) {g : G}
    (hVM : V ≤ conjSubgroup D.M g) (hVg : ¬ conjSubgroup V g ≤ D.M) :
    (calABar (mBar D.M ⊥ V h16.hyp125.isElemAbelian) D.M ⊥ V
      h16.hyp125.isElemAbelian).Nonempty := by
  have h := h16.hyp125
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hXM : conjSubgroup V g⁻¹ ≤ D.M := by
    have := E3.conjSubgroup_mono_left g⁻¹ hVM
    rwa [E3.conjSubgroup_conj_inv] at this
  have hMst : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hXst : conjSubgroup V g⁻¹ ≤ stabTil ⊥ V := hXM.trans hMst
  have hXel : IsElemAbelian 2 (conjSubgroup V g⁻¹) := E3.isElemAbelian_conjSubgroup hV g⁻¹
  have hX1 : barSub ⊥ V hV (conjSubgroup V g⁻¹) ≠ ⊥ := by
    intro hbot
    apply hVg
    have hcomm : ∀ x ∈ conjSubgroup V g⁻¹, ∀ v ∈ V, x * v * x⁻¹ = v := by
      intro x hx v hv
      have hmem := actTil_mem_barSub ⊥ V hV hx (hXst hx)
      rw [hbot, Subgroup.mem_bot] at hmem
      have := (actTil_eq_one_iff ⊥ V hV ⟨x, hXst hx⟩).1 hmem v hv
      rw [Subgroup.mem_bot] at this
      exact mul_inv_eq_one.1 this
    have hC : conjSubgroup V g ≤ centralizer (V : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hw' : g * w * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hw
      have hxX : g * v * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
        rw [mem_conjSubgroup_iff]
        have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
        rw [e]
        exact hv
      have := hcomm (g * v * g⁻¹) hxX (g * w * g⁻¹) hw'
      have e : v * w = w * v := by
        have h1 : g * v * g⁻¹ * (g * w * g⁻¹) * (g * v * g⁻¹)⁻¹ = g * w * g⁻¹ := this
        have h2 : g * (v * w * v⁻¹) * g⁻¹ = g * w * g⁻¹ := by
          rw [← h1]; group
        have h3 : v * w * v⁻¹ = w := by
          simpa only [mul_left_inj, mul_right_inj] using h2
        calc v * w = v * w * v⁻¹ * v := by group
          _ = w * v := by rw [h3]
      exact e
    exact hC.trans (centralizer_le_of_inCalV D h.inCalV)
  have hall : ∀ B : Subgroup G, B ≤ conjSubgroup V g⁻¹ →
      E3.mQuot (conjSubgroup V g⁻¹) B < mBar D.M ⊥ V hV →
      V ⊓ centralizer (B : Set G) =
        V ⊓ centralizer ((conjSubgroup V g⁻¹ : Subgroup G) : Set G) := by
    intro B hB hlt
    have hs : E3.mQuot (conjSubgroup V g⁻¹) B < E3.sParam hXel := by
      rw [E3.sParam_conj hV g⁻¹ hXel,
        s16c167_sParam_eq_mBar D hx h61 h111 h16 hm]
      exact hlt
    exact (E3.e3_6 hXel hB le_rfl hs (B2F.isPGroup_of_isElemAbelian hV)).1.symm
  exact ⟨_, s16c167_barSub_mem_calABar_of_le hV rfl hXM hXst hXel hX1 hall⟩

@[expose] def Insp1613U (D : Data G) (V : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≠ ⊥ ∧ U ≤ V ⊓ centralizer (E3.wClos V D.k D.T : Set G) ∧
    ∃ p ∈ D.sig, ∃ X : Subgroup G, X ≤ D.M ⊓ normalizer (U : Set G) ∧ IsPGroup p X ∧
      ¬ IsCyclic X

theorem s16c167_false_of_insp1613U (D : Data G) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV2 : IsPGroup 2 V) (hVT : V ≤ D.T)
    (h12 : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M) (hU : Insp1613U D V) : False := by
  obtain ⟨U, hU0, hUV, p, hp, X, hX, hXp, hXc⟩ := hU
  have hU2 : IsPGroup 2 U := IsPGroup.to_le hV2 (hUV.trans inf_le_left)
  have hN : normalizer (U : Set G) ≤ D.M :=
    normalizer_le_of_noncyclic D h61 hp (hX.trans inf_le_left) hXp hXc hU0 hU2
      (hX.trans inf_le_right)
  refine h12 ?_
  have hUC : U ≤ E3.cClos V D.k D.T :=
    le_inf ((hUV.trans inf_le_left).trans hVT) (hUV.trans inf_le_right)
  exact (Subgroup.centralizer_le hUC).trans
    ((Subgroup.centralizer_le_normalizer (U : Set G)).trans hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

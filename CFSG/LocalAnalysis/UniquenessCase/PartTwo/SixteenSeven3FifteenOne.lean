module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c167_preBarSub_bot_eq {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ stabTil ⊥ V) : preBarSub A ⊥ V hV ⊥ = A ⊓ centralizer (V : Set G) := by
  ext g
  rw [mem_preBarSub, Subgroup.mem_inf]
  constructor
  · rintro ⟨hgA, h, hg1⟩
    refine ⟨hgA, ?_⟩
    rw [Subgroup.mem_bot] at hg1
    have h1 := (actTil_eq_one_iff ⊥ V hV ⟨g, h⟩).1 hg1
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h2 : g * v * g⁻¹ * v⁻¹ = 1 := by simpa using h1 v hv
    have h3 : g * v * g⁻¹ = v := mul_inv_eq_one.1 h2
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  · rintro ⟨hgA, hgc⟩
    refine ⟨hgA, hA hgA, ?_⟩
    rw [Subgroup.mem_bot, actTil_eq_one_iff]
    intro v hv
    have h1 : v * g = g * v := Subgroup.mem_centralizer_iff.1 hgc v hv
    rw [Subgroup.mem_bot, ← h1]
    group

theorem s16c167_rk_barSub_eq_mQuot {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ stabTil ⊥ V) :
    rk ↥(barSub ⊥ V hV A) = E3.mQuot A (A ⊓ centralizer (V : Set G)) := by
  have h1 : rk ↥(barSub ⊥ V hV A) = E3.mQuot (barSub ⊥ V hV A) ⊥ := by
    unfold E3.mQuot rk
    rw [Subgroup.relIndex_bot_left]
  rw [h1, mQuot_barSub_preBarSub_gen hV hA bot_le, s16c167_preBarSub_bot_eq hV hA]

theorem s16c167_le_conj_of_rk_le (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V)
    {A : Subgroup G} (hAM : A ≤ D.M) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hmQ : E3.mQuot (conjSubgroup V g) A = D.k) (hrk : rk ↥(barSub ⊥ V hV A) ≤ 2) :
    E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer (V : Set G)) ≤ D.k + 2 ∧
      V ≤ conjSubgroup D.M g := by
  have hh : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hP := hh.pairFacts
  have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hCA : A ⊓ centralizer (V : Set G) ≤ A := inf_le_left
  have hCV : A ⊓ centralizer (V : Set G) ≤ conjSubgroup V g ⊓ centralizer (V : Set G) :=
    inf_le_inf_right _ hAg
  have hm : E3.mQuot (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) ≤ D.k + 2 := by
    rw [E3.mQuot_add hCA hAg, hmQ, ← s16c167_rk_barSub_eq_mQuot hV hAst]
    omega
  refine ⟨(E3.mQuot_mono hCV).trans hm, ?_⟩
  have hnorm : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hh.inCalV
  have hlt : (E3.mQuot (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) : ℕ∞) <
      rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
    rw [rMV_conj hnorm g]
    exact lt_of_le_of_lt (by exact_mod_cast hm) h14
  have hcent := centralizer_le_of_mQuot_lt_rMV (inf_le_left.trans hAg) hlt
  intro v hv
  apply hcent
  rw [Subgroup.mem_centralizer_iff]
  intro c hc'
  exact (Subgroup.mem_centralizer_iff.1 hc'.2 v hv).symm

theorem s16c167_conj_le_of_mQuot_le (D : Data G) {V : Subgroup G}
    (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V) {g : G}
    (h : E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) ≤ D.k + 2) :
    conjSubgroup V g ≤ D.M := by
  have hlt : (E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) : ℕ∞) < rMV D.M V :=
    lt_of_le_of_lt (by exact_mod_cast h) h14
  have hcent := centralizer_le_of_mQuot_lt_rMV (inf_le_left) hlt
  intro w hw
  apply hcent
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.1 hu.2 w hw).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

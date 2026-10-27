module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Forty7aCommon
public import CFSG.LocalAnalysis.WeakClosure81.SixNine
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_mem_cTilde_of_calOStar (D : Data G) {V₀ V : Subgroup G} (hV : InCalV D.M V)
    (hV₀ : InCalV D.M V₀) {h : G} (hO : conjSubgroup V h ∈ calOStar 1 D.M V₀ V) {x : G}
    (hx : x ∈ conjSubgroup V₀ h) (hxM : x ∈ D.M) : x ∈ F11.CTilde D.M V₀ V := by
  obtain ⟨g', hg', hstar⟩ := hO
  obtain ⟨-, _, -, -, -, -, hcomm, -, -⟩ := hstar
  have hconj : conjSubgroup V (g' * h⁻¹) = V := by
    rw [← conjSubgroup_conjSubgroup, ← hg', E3.conjSubgroup_conj_inv]
  have hgh : g' * h⁻¹ ∈ D.M := by
    rw [← normalizer_eq_of_inCalV D hV]
    exact (conjSubgroup_eq_iff_mem_normalizer).1 hconj
  have hV₀gh : conjSubgroup V₀ (g' * h⁻¹) = V₀ :=
    (conjSubgroup_eq_iff_mem_normalizer).2 (hV₀.2.2.1 hgh)
  have hV₀g' : conjSubgroup V₀ g' = conjSubgroup V₀ h := by
    have hg'eq : g' = (g' * h⁻¹) * h := by group
    rw [hg'eq, ← conjSubgroup_conjSubgroup, hV₀gh]
  have hc : CentralizesMod V₀ V x := by
    intro v hv
    have hmem : ⁅x, v⁆ ∈ V₀ := by
      have h1 : ⁅x, v⁆ ∈ ⁅conjSubgroup V₀ h, V⁆ :=
        Subgroup.commutator_mem_commutator hx hv
      rw [← hV₀g'] at h1
      exact hcomm h1
    rwa [commutatorElement_def] at hmem
  exact (CFSG.LocalAnalysis.WeakClosure81.mem_cTilde_iff_centralizes hV.2.2.2 hV.2.2.1
    hV₀.2.2.1).2 ⟨hxM, hc⟩

private theorem s16c1_mQuot_uOne_eq_one {V : Subgroup G} (hV : IsElemAbelian 2 V) {z : G}
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z)) :
    E3.mQuot V (uOne V z) = 1 := by
  have hV2 : IsPGroup 2 V := fun y => ⟨1, Subtype.ext (by simpa using hV.2 y y.2)⟩
  have hcard' : Nat.card ↥V = 2 ^ E3.mQuot V (uOne V z) * Nat.card ↥(uOne V z) :=
    E3.card_eq_two_pow_mul (U := uOne V z) hV2 (inf_le_left : uOne V z ≤ V)
  have hmul : 2 ^ E3.mQuot V (uOne V z) * Nat.card ↥(uOne V z) =
      2 * Nat.card ↥(uOne V z) := by
    rw [← hcard']; exact hcard
  have h2 : 2 ^ E3.mQuot V (uOne V z) = 2 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  exact Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h2)

theorem s16c1_inCalO_one {D : Data G} {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {z h : G}
    (hQM : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.M)
    (hh : h ∈ centralizer ({z} : Set G))
    (hcard : Nat.card ↥V = 2 * Nat.card ↥(uOne V z))
    (hVM : ¬ conjSubgroup V h ≤ D.M) (hMV : ¬ V ≤ conjSubgroup D.M h)
    (h1 : V₀ ⊓ conjSubgroup D.M h ≠ ⊥) (h2 : conjSubgroup V₀ h ⊓ D.M ≠ ⊥) :
    InCalO 1 D.M V₀ V h := by
  have hone : E3.mQuot V (uOne V z) = 1 := s16c1_mQuot_uOne_eq_one hV hcard
  have hUconj : uOne V z ≤ conjSubgroup D.M h := by
    have hstep : uOne V z ≤ conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) h :=
      (show uOne V z ≤ pCoreOf 2 (centralizer ({z} : Set G)) from inf_le_right).trans
        (le_of_eq (s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hh).symm)
    exact hstep.trans (E3.conjSubgroup_mono_left h hQM)
  have hA : E3.mQuot V (conjSubgroup D.M h) ≤ 1 := by
    have hmono : E3.mQuot V (V ⊓ conjSubgroup D.M h) ≤ E3.mQuot V (uOne V z) :=
      E3.mQuot_mono (le_inf inf_le_left hUconj)
    have heq : E3.mQuot V (conjSubgroup D.M h) = E3.mQuot V (V ⊓ conjSubgroup D.M h) :=
      (CFSG.LocalAnalysis.WeakClosure81.mQuot_inf_left V (conjSubgroup D.M h)).symm
    rw [heq]
    exact hmono.trans (le_of_eq hone)
  have hUhM : conjSubgroup (uOne V z) h ≤ D.M := by
    have hstep : conjSubgroup (uOne V z) h ≤ pCoreOf 2 (centralizer ({z} : Set G)) :=
      (E3.conjSubgroup_mono_left h
        (show uOne V z ≤ pCoreOf 2 (centralizer ({z} : Set G)) from inf_le_right)).trans
        (le_of_eq (s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hh))
    exact hstep.trans hQM
  have hB : E3.mQuot (conjSubgroup V h) D.M ≤ 1 := by
    have hmono : E3.mQuot (conjSubgroup V h) D.M ≤
        E3.mQuot (conjSubgroup V h) (conjSubgroup (uOne V z) h) :=
      E3.mQuot_mono hUhM
    rw [E3.mQuot_conjSubgroup] at hmono
    exact hmono.trans (le_of_eq hone)
  exact ⟨⟨hVM, hA, fun _ => h1⟩, ⟨hMV, hB, fun _ => h2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Sylow1411X

variable {G : Type} [Group G] [Finite G]

theorem not_transOn_of_hj
    {A L : Subgroup G} {b : G} (h' : Sec14Std G A b L)
    (h142 : ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers b : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A (lB A)) (Subgroup.centralizer {b}))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    ¬ TransOn A (lB A) (xA A) (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨U₁, hU₁, U₂, hU₂, hne, -, hXU⟩ := exists_scriptQPiStar_two_of_j2 h' h142 hJ
  have hD := h'.toSec13Data
  have hLb : L ≤ Subgroup.centralizer ({b} : Set G) := hD.le_centralizer
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hD.le_normalizer
  have h3L : 3 ∣ Nat.card L :=
    three_dvd_card_of_types148 (h'.chosen136.2 b hD.zpowers_mem_omegaA L hD.mem_lA).1
  have hCN : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h' h3L
  have key : ∀ U ∈ scriptQPiStar A (lB A) L (piOf 2),
      ∃ V ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({b} : Set G)) (piOf 2), V ⊓ L = U := by
    intro U hU
    obtain ⟨V, hUV, hV⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (Subgroup.centralizer ({b} : Set G)) (piOf 2))) (a := U)
      ⟨⟨hU.prop.1.1, hU.prop.1.2.trans hLb⟩, hU.prop.2⟩
    have hle : U ≤ V ⊓ L := le_inf hUV hU.prop.1.2
    have hVL : V ⊓ L ∈ scriptQPi A (lB A) L (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hV.prop.1.1 inf_le_left (le_normalizer_inf hV.prop.1.1.1.2.2 hAL),
        inf_le_right⟩, fun q hq => hV.prop.2 q (hq.trans (Subgroup.card_dvd_of_le inf_le_left))⟩
    exact ⟨V, hV, le_antisymm (hU.2 hVL hle) hle⟩
  obtain ⟨V₁, hV₁, hV₁L⟩ := key U₁ hU₁
  obtain ⟨V₂, hV₂, hV₂L⟩ := key U₂ hU₂
  intro htr
  obtain ⟨x, hx, hxV⟩ := htr V₂ hV₂ V₁ hV₁
  have hLx : L.map (MulAut.conj x).toMonoidHom = L :=
    Late.map_conj_eq_of_mem_normalizer (hCN (Subgroup.mem_inf.mp hx).2)
  have hUx : U₂.map (MulAut.conj x).toMonoidHom = U₂ :=
    Late.map_conj_eq_of_mem_normalizer (hXU (Subgroup.mem_inf.mp hx).1)
  apply hne
  calc U₁ = V₁ ⊓ L := hV₁L.symm
    _ = V₂.map (MulAut.conj x).toMonoidHom ⊓ L.map (MulAut.conj x).toMonoidHom := by
      rw [hxV, hLx]
    _ = (V₂ ⊓ L).map (MulAut.conj x).toMonoidHom :=
      (Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective).symm
    _ = U₂ := by rw [hV₂L, hUx]

theorem isEmpty_j2_of_transOn
    (h142All : Item142AllS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hloc : ∀ a : G, Subgroup.zpowers a ∈ omegaA A →
      TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G)))
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨fun φ => ?_⟩
  have hb' : Sec14Std G A b Lb := Proof1413.sec14Std_at hR.toSec14Std hb hLb
  exact not_transOn_of_hj hb' (fun Q hQ => (h142All G A b Lb hb' Q hQ).1) ⟨φ⟩ (hloc b hb)

end Sylow1411X

end CFSG.RankThree.PartTwo.Sec14

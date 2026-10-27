module

public import CFSG.RankThree.PartTwo.Sec17.Item1712Proof
public import CFSG.RankThree.PartTwo.Sec17.Item177Proof
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

theorem Sec17Std.le_y0_of_alternating_ten {G : Type} [Group G] [Finite G] {A : Subgroup G}
    {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hA10 : Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10))) : A ≤ Y₀ := by
  obtain ⟨φ⟩ := hA10
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hmax : ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B →
      B = E := fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB
  exact Step163Alt.le_of_alternating_ten hmax h.toSec13Data.isElemAbelian h.le_normalizer_y0
    h.mem_y0Star.prop.2.2 φ

theorem claim1715A_of : Claim1715A :=
  fun _ _ _ _ _ _ _ h hA10 _ _ => h.le_y0_of_alternating_ten hA10

namespace Proof1712

variable {G : Type} [Group G] [Finite G]

theorem exists_fourGroupsMinus_le_of_le_commutator {A V W : Subgroup G} {a : G}
    (hA : IsE27 A) (haA : a ∈ A) (hV : CFSG.Assembly.IsElemAbelian 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hWV : W ≤ ⁅V, Subgroup.zpowers a⁆) (hW : W ≠ ⊥) :
    ∃ U ∈ fourGroupsMinus A, U ≤ W ∧ U = ⁅U, Subgroup.zpowers a⁆ := by
  have ha3 : a ^ 3 = 1 := hA.1.2 a haA
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hV
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have haV : a ∈ Subgroup.normalizer (V : Set G) := hAV haA
  have hVaV : ⁅V, Subgroup.zpowers a⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr haV)
  have hWab : CFSG.Assembly.IsElemAbelian 2 W := Sec5.isElemAbelian_of_le hV (hWV.trans hVaV)
  have hWeq : W = ⁅W, Subgroup.zpowers a⁆ :=
    eq_commutator_of_le_commutator ha3 hV2 hVab haV (hAW haA) hWV
  have hWA : ⁅W, A⁆ ≠ ⊥ := by
    intro hbot
    apply hW
    rw [hWeq, eq_bot_iff, ← hbot]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr haA)
  obtain ⟨U, hU, hUW⟩ := Proof177.exists_mem_fourGroupsMinus_le hA hWab hAW hWA
  exact ⟨U, hU, hUW,
    eq_commutator_of_le_commutator ha3 hV2 hVab haV (hU.1.1.2.2 haA) (hUW.trans hWV)⟩

end Proof1712

@[expose] noncomputable def Step1712SevenY0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ V : Subgroup G,
      Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 V) V →
      omegaA A = {Subgroup.zpowers c} → ⁅V, Y₀⁆ ≠ ⊥ → ⁅V, Subgroup.zpowers c⁆ ≠ ⊥ →
        ⁅V, Subgroup.zpowers c⁆ ⊓ Y₀ = ⊥ →
          ∃ U ∈ fourGroups A, U ≤ ⁅V, Subgroup.zpowers c⁆ ∧ U ∈ scriptQ A (lB A)

end CFSG.RankThree.PartTwo.Sec17

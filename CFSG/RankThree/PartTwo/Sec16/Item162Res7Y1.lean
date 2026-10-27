module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res7A7Free
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7PushA7
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7A7Setup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Res162Seven

namespace Conf683

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G}
  {b : G} {Lb : Subgroup G}

theorem c_mem (h : Conf683 A c L Y₁ Y₂ S b Lb) : c ∈ A :=
  (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).1

theorem b_mem (h : Conf683 A c L Y₁ Y₂ S b Lb) : b ∈ A :=
  (zpowers_mem_omegaA_iff.mp h.omega_b).1

theorem c_ne_one (h : Conf683 A c L Y₁ Y₂ S b Lb) : c ≠ 1 := by
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.sec15R.toSec13Data.zpowers_mem_omegaA).2.1
  intro h1
  rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
  norm_num at hc3

theorem b_ne_one (h : Conf683 A c L Y₁ Y₂ S b Lb) : b ≠ 1 := by
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 :=
    (zpowers_mem_omegaA_iff.mp h.omega_b).2.1
  intro h1
  rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb3
  norm_num at hb3

theorem isElemAbelian_A (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    CFSG.Assembly.IsElemAbelian 3 A :=
  h.sec15R.toSec14Std.chosen136.1.1

theorem card_A (h : Conf683 A c L Y₁ Y₂ S b Lb) : Nat.card A = 27 := by
  rcases h.sec15R.toSec14Std.hypS_or_hypT with hS | hT
  · exact (Late.isE27_of_mem_partTwoE hS.1).2
  · exact (Late.isE27_of_mem_partTwoE hT.1).2

theorem mem_of_pow_three_centralizes (h : Conf683 A c L Y₁ Y₂ S b Lb) {x : G}
    (hx3 : x ^ 3 = 1) (hx : A ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ A := by
  have hsup : CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_zpowers (isElemAbelian_A h) hx3 fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mp (hx he)
  have heq : A ⊔ Subgroup.zpowers x = A :=
    h.sec15R.toSec14Std.chosen136.1.2.1 _ hsup le_sup_left
  have hmem : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [heq] at hmem

theorem le_normalizer₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    A ≤ Subgroup.normalizer (Y₁ : Set G) :=
  h.maxCE.1.mem₁.prop.1.1.2

theorem le_normalizer₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    A ≤ Subgroup.normalizer (Y₂ : Set G) :=
  h.maxCE.1.mem₂.prop.1.1.2

theorem isPGroup_S₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) : IsPGroup 2 S :=
  isPGroup_of_mem_scriptQPi Nat.prime_two h.maxCE.1.s₁.prop

theorem commutator_c (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∀ y ∈ Y₁, c * y * c⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₁ := by
  have hmem : c ∈ Late.sectionCentralizer A Y₁ (CFSG.Open.pCoreOf 2 Y₁) := by
    rw [sc₁ h]
    exact Subgroup.mem_zpowers c
  exact fun y hy => hmem.2 y hy

theorem commutator_b (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∀ y ∈ Y₂, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₂ := by
  have hmem : b ∈ Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) := by
    rw [h.sc₂]
    exact Subgroup.mem_zpowers b
  exact fun y hy => hmem.2 y hy

theorem pCoreOf_sup_le₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) ≤ S :=
  pCoreOf_sup_le_of_centralizes h.sec15R.toSec14Std h.item146 h.concl142
    (le_normalizer₁ h) h.maxCE.1.s₁ (commutator_c h) (pCoreOf_le₁ h)

theorem commutator_c_mem (h : Conf683 A c L Y₁ Y₂ S b Lb) {x : G}
    (hx : x ∈ Y₁ ⊔ S) : c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) := by
  have hZ : Subgroup.center (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁) = ⊥ :=
    (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨Classical.choice h.a7₁⟩).2.1
  refine commutator_mem_pCoreOf_sup (isPGroup_S₁ h) h.maxCE.1.s₁.prop.1.2 hZ ?_ ?_ ?_ hx
  · exact le_normalizer₁ h (c_mem h)
  · exact h.maxCE.1.s₁.prop.1.1.1.2.2 (c_mem h)
  · exact commutator_c h

theorem card_inf₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Nat.card (A ⊓ Y₁ : Subgroup G) = 9 ∧ c ∉ Y₁ ∧
      (A ⊓ Y₁) ⊔ Subgroup.zpowers c = A :=
  card_inf_eq_nine_of_a7 (isElemAbelian_A h) (card_A h)
    (fun x hx3 hx => mem_of_pow_three_centralizes h hx3 hx)
    (le_normalizer₁ h) (Classical.choice h.a7₁) (K := Y₁) (k := c) (sc₁ h) (c_ne_one h)

theorem card_inf₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Nat.card (A ⊓ Y₂ : Subgroup G) = 9 ∧ b ∉ Y₂ ∧
      (A ⊓ Y₂) ⊔ Subgroup.zpowers b = A :=
  card_inf_eq_nine_of_a7 (isElemAbelian_A h) (card_A h)
    (fun x hx3 hx => mem_of_pow_three_centralizes h hx3 hx)
    (le_normalizer₂ h) (Classical.choice h.a7₂) (K := Y₂) (k := b) h.sc₂ (b_ne_one h)

theorem push₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Y₁ ⊔ S = Y₁ ⊔ CFSG.Open.pCoreOf 2 (Y₁ ⊔ S) ∧
      Nat.card S = 4 * Nat.card (CFSG.Open.pCoreOf 2 (Y₁ ⊔ S)) ∧
      Nonempty (↥(Y₁ ⊔ S) ⧸ CFSG.pCore 2 ↥(Y₁ ⊔ S) ≃* alternatingGroup (Fin 7)) :=
  ⟨sup_eq_sup_pCoreOf_of_a7 h.sec15R.toSec14Std h.item146 h.concl142 (le_normalizer₁ h)
      h.maxCE.1.s₁ (Classical.choice h.a7₁) (commutator_c h) (pCoreOf_le₁ h)
      (card_inf₁ h).1 (card_inf₁ h).2.2,
    card_eq_four_mul_of_a7 h.sec15R.toSec14Std h.item146 h.concl142 (le_normalizer₁ h)
      h.maxCE.1.s₁ (Classical.choice h.a7₁) (commutator_c h) (pCoreOf_le₁ h)
      (card_inf₁ h).1 (card_inf₁ h).2.2,
    nonempty_quotient_equiv_of_a7 h.sec15R.toSec14Std h.item146 h.concl142 (le_normalizer₁ h)
      h.maxCE.1.s₁ (Classical.choice h.a7₁) (commutator_c h) (pCoreOf_le₁ h)
      (card_inf₁ h).1 (card_inf₁ h).2.2⟩

theorem exists_map_S₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∃ g : Equiv.Perm (Fin 7), (S.subgroupOf (Subgroup.normalizer (Y₁ : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₁ (Classical.choice h.a7₁)) =
        CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom :=
  exists_map_eq_map_vTwo_of_a7 h.sec15R.toSec14Std h.item146 h.concl142 (le_normalizer₁ h)
    h.maxCE.1.s₁ (Classical.choice h.a7₁) (commutator_c h) (pCoreOf_le₁ h)
    (card_inf₁ h).1 (card_inf₁ h).2.2

theorem exists_map_S₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    ∃ g : Equiv.Perm (Fin 7), (S.subgroupOf (Subgroup.normalizer (Y₂ : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep Y₂ (Classical.choice h.a7₂)) =
        CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom :=
  exists_map_eq_map_vTwo_of_a7 (h.sec15R_b).toSec14Std h.item146 h.concl142 (le_normalizer₂ h)
    h.maxCE.1.s₂ (Classical.choice h.a7₂) (commutator_b h) (pCoreOf_le₂ h)
    (card_inf₂ h).1 (card_inf₂ h).2.2

theorem card_V (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Nat.card S = 4 * Nat.card (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) ∧
      Nat.card (S ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = 4 := by
  set V : Subgroup G := S ⊓ Subgroup.centralizer ({b} : Set G)
  set R : Subgroup G := CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)
  have hS4 : Nat.card S = 4 * Nat.card R :=
    card_eq_four_mul_of_a7 (h.sec15R_b).toSec14Std h.item146 h.concl142 (le_normalizer₂ h)
      h.maxCE.1.s₂ (Classical.choice h.a7₂) (commutator_b h) (pCoreOf_le₂ h)
      (card_inf₂ h).1 (card_inf₂ h).2.2
  have hdisj : Disjoint R V := by
    rw [disjoint_iff_inf_le, inf_comm]
    exact (V_inf_R h).le
  have hnormal : V ≤ Subgroup.normalizer (R : Set G) :=
    (inf_le_left.trans (le_sup_right : S ≤ Y₂ ⊔ S)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₂ ⊔ S))
  have hcard : Nat.card S = Nat.card R * Nat.card V := by
    have hsup : S = V ⊔ R := (sup_V_eq h).symm
    rw [hsup, sup_comm]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R V hnormal hdisj
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have h1 : Nat.card R * Nat.card V = Nat.card R * 4 := by
    rw [← hcard, hS4, Nat.mul_comm]
  exact ⟨hS4, Nat.mul_left_cancel hRpos h1⟩

end Conf683

end Res162Seven

end CFSG.RankThree.PartTwo.Sec16

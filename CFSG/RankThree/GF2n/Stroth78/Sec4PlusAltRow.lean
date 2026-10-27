module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltPoint
public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltOrbit

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusAltCoh
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusWeakClosure
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusPerfect
import CFSG.GroupTheory.Transfer.YoshidaParityFour
import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

section Hub


theorem not_lieModel_psl_four_of_card_ZQ_eq_four
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4)
    (hL : CFSG.Blueprint.LieModel ↥(Xsub S a) .PSL 4 2 1)
    (hbG : ∃ b ∈ ZQ z, b ∉ Subgroup.zpowers z ∧ b ∈ _root_.commutator G) : False := by
  classical
  obtain ⟨b, hbZ, hbz, hbG'⟩ := hbG
  obtain ⟨hw, hC, Ψ, P, Pd, hΨs, hΨi, hA, hP, htop⟩ :=
    exists_pointMaps_of_lieModel_psl4 S h h217 h34 hw4 hZ hL
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).mp hL
  have hperf := commutator_Xsub_eq_of_threeFourPlus S h h217 h34
  have hX1 := rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four S h h217 h34 hZ
  have hLle : Nat.card ↥(Lbar S a) ≤ 16 := by
    have h1 := (card_Lbar_numerics_of_mulEquiv_alt8 S h h217 h34 hZ e).2.2.2.1
    have h2 : Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) = 1 := by
      rw [hC, inf_bot_eq]
      exact Subgroup.card_bot
    omega
  obtain ⟨hFinf, hFsup⟩ := FsubH_inf_ZQ_eq_and_sup_eq S a hZ hX1 (rhoX S a) (rhoX_apply S a) Ψ
    hΨs hΨi hP htop
  obtain ⟨H₁, hH₁H, hH₁idx, hbH₁, hDH₁⟩ := exists_index_two_not_mem_of_pointMaps S h hw hZ hX1
    hperf hC hLle e hFinf hFsup hbZ hbz
  obtain ⟨r, hrL0, hrX⟩ := exists_mem_L0_not_mem_XsubHat S h hZ hX1
  have hrH : r ∈ H z := (Subgroup.mem_inf.mp hrL0).2
  have hrXb : (QuotientGroup.mk (⟨r, hrH⟩ : ↥(H z)) : Hbar z) ∉ Xsub S a := fun hmem =>
    hrX ((mem_XsubHat_iff S a).mpr ⟨hrH, hmem⟩)
  obtain ⟨ι, hι⟩ := exists_mulEquiv_perm_eight S a e hC ⟨_, hrXb⟩
  have hodd : Odd (H z).index := by
    obtain ⟨P0⟩ : Nonempty (Sylow 2 ↥(H z)) := inferInstance
    have h1 := odd_index_map_subtype_of_card_ZQ_eq_four S h hZ P0
    have hle : (P0 : Subgroup ↥(H z)).map (H z).subtype ≤ H z := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    exact Odd.of_dvd_nat h1 (Subgroup.index_dvd_of_le hle)
  obtain ⟨y, hyb, hyH₁, hy4⟩ := CFSG.GroupTheory.exists_isConj_mem_not_four_dvd_relIndex
    (sq_eq_one_of_mem_ZQ S hbZ) hbG' hH₁H hH₁idx hodd
    (relIndex_centralizer_le_two_of_mem_ZQ S hZ hbZ)
  exact false_of_isConj_mem_index_two S h hw hZ
    (fun t ht htc => eq_of_mem_ZQ_of_isConj_of_card_ZQ_eq_four S h hZ ht htc) hΨs
    (rhoX_apply S a) hA hP htop hC e ι hι hrL0 hrX hFinf hFsup hbZ hbz hH₁H hbH₁ hDH₁ hyb hyH₁
    hy4

end Hub

end CFSG.RankThree.GF2n.Stroth78

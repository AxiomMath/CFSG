module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs

import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.LocalAnalysis.UniquenessCase.UC1K327Core

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

private lemma isPGroup_sup_zpowers_of_mem_centralizer {X : Type} [Group X] [Finite X]
    {A : Subgroup X} {x : X} (hA : IsPGroup 3 A)
    (hx : x ∈ Subgroup.centralizer (A : Set X)) (h3 : orderOf x = 3) :
    IsPGroup 3 (A ⊔ Subgroup.zpowers x : Subgroup X) := by
  have hx3group : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3]; norm_num)
  have hA_le_norm : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
    have hAcent : A ≤ Subgroup.centralizer ({x} : Set X) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx) a ha
    have hcent_eq : Subgroup.centralizer ({x} : Set X) =
        Subgroup.centralizer (Subgroup.zpowers x : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent_eq] at hAcent
    exact hAcent.trans (Subgroup.centralizer_le_normalizer _)
  exact hA.to_sup_of_normal_right' hx3group hA_le_norm

private lemma centralizer_eq_of_card_eq_81_of_card_center_eq_three {Y : Type} [Group Y]
    [Finite Y] {A : Subgroup Y} (hAcomm : IsMulCommutative ↥A)
    (hcard : Nat.card Y = 81) (hcenter : Nat.card (Subgroup.center Y) = 3)
    (hAcard : Nat.card A = 27) : Subgroup.centralizer (A : Set Y) = A := by
  classical
  haveI : IsMulCommutative ↥A := hAcomm
  let C : Subgroup Y := Subgroup.centralizer (A : Set Y)
  have hAC : A ≤ C := Subgroup.le_centralizer A
  have hAindex : A.index = 3 := by
    have h := Subgroup.index_mul_card A
    rw [hAcard, hcard] at h
    omega
  have hprime : Nat.Prime A.index := by rw [hAindex]; norm_num
  have hcoatom : IsCoatom A := Subgroup.isCoatom_of_index_prime hprime
  have hCor : C = A ∨ C = ⊤ := by
    rcases eq_or_lt_of_le hAC with h | hlt
    · exact Or.inl h.symm
    · exact Or.inr ((hcoatom.lt_iff).mp hlt)
  rcases hCor with hCA | hCtop
  · exact hCA
  · exfalso
    have hAcenter : A ≤ Subgroup.center Y := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro y
      have hyC : y ∈ C := by rw [hCtop]; exact Subgroup.mem_top y
      exact (Subgroup.mem_centralizer_iff.mp hyC a ha).symm
    have hcardle : Nat.card A ≤ Nat.card (Subgroup.center Y) :=
      Subgroup.card_le_of_le hAcenter
    rw [hAcard, hcenter] at hcardle
    omega

private lemma card_center_eq_of_isSylowOf {X : Type} [Group X] [Finite X] {P Q : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤) :
    Nat.card Q = Nat.card P ∧
      Nat.card (Subgroup.center Q) = Nat.card (Subgroup.center P) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, -, hconj⟩ := hP.exists_mem_conj hQ
  let f : X ≃* X := MulAut.conj k⁻¹
  have hmap : Subgroup.map (f : X →* X) Q = P := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      have := (hconj q).mp hq
      simpa [f, MulAut.conj_apply] using this
    · intro hy
      refine ⟨MulAut.conj k y, ?_, ?_⟩
      · show MulAut.conj k y ∈ Q
        rw [hconj]
        have h : k⁻¹ * MulAut.conj k y * k = y := by
          simp only [MulAut.conj_apply]
          group
        rw [h]
        exact hy
      · show (MulAut.conj k⁻¹ : X → X) (MulAut.conj k y) = y
        simp only [MulAut.conj_apply, inv_inv]
        group
  let e : Q ≃* P :=
    (Subgroup.equivMapOfInjective Q (f : X →* X) f.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hcenter : Subgroup.map (e : Q →* P) (Subgroup.center Q) = Subgroup.center P :=
    Subgroup.map_center_eq e
  refine ⟨Nat.card_congr e.toEquiv, ?_⟩
  calc Nat.card (Subgroup.center Q)
      = Nat.card (Subgroup.map (e : Q →* P) (Subgroup.center Q)) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ = Nat.card (Subgroup.center P) := by rw [hcenter]

private lemma card_and_center_card_of_mulEquiv_ZWr_one {Y : Type} [Group Y]
    (e : Y ≃* ZWr 1) : Nat.card Y = 81 ∧ Nat.card (Subgroup.center Y) = 3 := by
  have h := zwr_card_center_Zwr (n := 1) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, h.1]
    norm_num
  · calc Nat.card (Subgroup.center Y)
        = Nat.card (Subgroup.map (e : Y →* ZWr 1) (Subgroup.center Y)) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ = Nat.card (Subgroup.center (ZWr 1)) := by rw [Subgroup.map_center_eq e]
      _ = 3 := by
          rw [h.2.2]
          norm_num

theorem mem_of_mem_centralizer_of_hyp327 {X : Type} [Group X] [Finite X] {P A : Subgroup X}
    (hX : Hyp327 X P A) {x : X} (hx : x ∈ Subgroup.centralizer (A : Set X))
    (h3 : orderOf x = 3) : x ∈ A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAsup := isPGroup_sup_zpowers_of_mem_centralizer hX.elem.isPGroup hx h3
  obtain ⟨Q, hQle⟩ := hAsup.exists_le_sylow
  have hAQ : A ≤ (Q : Subgroup X) := fun a ha => hQle (Subgroup.mem_sup_left ha)
  have hxQ : x ∈ (Q : Subgroup X) :=
    hQle (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup X) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  rcases hX.shape with hAP | hne
  · have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A ⊤ := hAP.symm ▸ hX.sylow
    have hQeq : (Q : Subgroup X) = A := hAsyl.eq_of_le hAQ le_top Q.isPGroup'
    exact hQeq ▸ hxQ
  · obtain ⟨eP⟩ := hne
    obtain ⟨hcardP, hcenterP⟩ := card_and_center_card_of_mulEquiv_ZWr_one eP
    obtain ⟨hcardQ, hcenterQ⟩ := card_center_eq_of_isSylowOf hX.sylow hQsyl
    have hcardQ81 : Nat.card (Q : Subgroup X) = 81 := hcardQ.trans hcardP
    have hcenterQ3 : Nat.card (Subgroup.center (Q : Subgroup X)) = 3 :=
      hcenterQ.trans hcenterP
    let Aq : Subgroup (Q : Subgroup X) := A.subgroupOf (Q : Subgroup X)
    have hAqcard : Nat.card Aq = 27 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAQ).toEquiv, hX.card]
    have hAqcomm : IsMulCommutative ↥Aq := by
      refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      apply Subtype.ext
      have h := hX.elem.1.is_comm.comm
        ⟨(a : X), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b : X), Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using h
    have hcent := centralizer_eq_of_card_eq_81_of_card_center_eq_three
      hAqcomm hcardQ81 hcenterQ3 hAqcard
    have hxQcent : (⟨x, hxQ⟩ : ↥(Q : Subgroup X)) ∈
        Subgroup.centralizer (Aq : Set ↥(Q : Subgroup X)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx) (a : X) (Subgroup.mem_subgroupOf.mp ha)
    rw [hcent] at hxQcent
    exact Subgroup.mem_subgroupOf.mp hxQcent

theorem eq_bot_of_hyp327_of_layer_eq_bot {X : Type} [Group X] [Finite X] {P A : Subgroup X}
    (hX : Hyp327 X P A) (h3' : CFSG.pPrimeCore 3 X = ⊥)
    (hE : CFSG.layer X = ⊥) {W : Subgroup X} (hW : A ≤ Subgroup.normalizer (W : Set X))
    (hcop : Nat.Coprime (Nat.card W) 3) : W = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcon : CFSG.ABGLocalTools.IsPConstrained 3 X := by
    have hchar : CFSG.IsCharacteristicP 3 X :=
      CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X 3 h3' hE
    rw [CFSG.ABGLocalTools.IsPConstrained,
      CFSG.Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := X) (p := 3) h3']
    intro P' hP'
    have hPeq : CFSG.pCore 3 X = P' :=
      hP'.eq_of_le hP'.le le_rfl (CFSG.pCore_isPGroup (p := 3) (G := X))
    rw [← hPeq]
    exact hchar
  have hcon' : CFSG.PConstrainedGroup (G := X) 3 :=
    (CFSG.ABGLocalTools.isPConstrained_iff_pConstrainedGroup (p := 3) (H := X)).mp hcon
  have hWinf : W ⊓ A = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_of_coprime hX.elem.isPGroup hcop.symm
  have hWle : W ≤ CFSG.pPrimeCore 3 X :=
    CFSG.thompson_bender_signalizer_lemma (G := X) (p := 3) (by norm_num) hcon'
      hX.elem.isPGroup
      (fun x hx hx3 => mem_of_mem_centralizer_of_hyp327 hX hx hx3) hW hWinf
  rw [h3'] at hWle
  exact le_bot_iff.mp hWle

@[expose] def KFactE27SignalizerLayer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ → CFSG.layer X ≠ ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W = ⊥

theorem kFactE27Signalizer_of_layer (h : KFactE27SignalizerLayer) : KFactE27Signalizer := by
  intro X _ _ P A hK hX hP h3' hcent W hW hcop
  by_cases hE : CFSG.layer X = ⊥
  · exact eq_bot_of_hyp327_of_layer_eq_bot hX h3' hE hW hcop
  · exact h X P A hK hX hP h3' hE hcent W hW hcop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

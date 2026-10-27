module

public import CFSG.RankThree.GF2n.Tim78S412Cen
import CFSG.RankThree.GF2n.Tim78S4Closing

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement

namespace Hyp4

variable {G : Type} [Group G] [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Root


theorem commutator_inv_left_of_mem_Q {u a : G} (hu : u ∈ Q) (ha : a ∈ Q) :
    ⁅u⁻¹, a⁆ = ⁅u, a⁆⁻¹ := by
  have := H.commutator_mul_left_of_mem_Q hu (Q.inv_mem hu) ha
  rw [mul_inv_cancel, commutatorElement_one_left] at this
  exact eq_inv_of_mul_eq_one_left this.symm

section Mutual

variable (hmut : MutualPFull M B P g)
include hmut

theorem core_centP_comm (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {c c' : G}
    (hc : c ∈ centP B P g) (hc' : c' ∈ centP B P g) : c * c' = c' * c :=
  comm_of_mul_self_eq_one (H.pair_centP_sq hmut hCen hU hc) (H.pair_centP_sq hmut hCen hU hc')
    (H.pair_centP_sq hmut hCen hU ((centP B P g).mul_mem hc hc'))

theorem core_cen_mem_B (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {h : G}
    (hhP : conjSubgroup h B ≤ P) (hEB : conjSubgroup h B ≠ B)
    (hfac : ∀ p ∈ P, ∃ e ∈ conjSubgroup h B, ∃ c ∈ centP B P g, p = e * c) {c e : G}
    (hc : c ∈ centP B P g) (he : e ∈ conjSubgroup h B) (he1 : e ≠ 1) (hce : c * e = e * c) :
    c ∈ B := by
  have hcP : c ∈ P := (mem_centP.mp hc).1
  have hcE : ∀ v ∈ conjSubgroup h B, c * v = v * c := H.comm_of_comm_conj hhP hEB hcP he he1 hce
  refine H.center_P_le_B c hcP fun p hp => ?_
  obtain ⟨e', he', c', hc', rfl⟩ := hfac p hp
  calc c * (e' * c') = (c * e') * c' := by group
    _ = (e' * c) * c' := by rw [hcE e' he']
    _ = e' * (c * c') := by group
    _ = e' * (c' * c) := by rw [H.core_centP_comm hmut hCen hU hc hc']
    _ = (e' * c') * c := by group

theorem core_dichotomy {k : G} (hkP : conjSubgroup k B ≤ P) (hkB : conjSubgroup k B ≠ B) {x : G}
    (hxS : x ∈ conjSubgroup k B) (hx1 : x ≠ 1) (hxC : x ∈ centP B P g) :
    conjSubgroup k B ≤ centP B P g := by
  intro s hs
  refine mem_centP.mpr ⟨hkP hs, fun a ha => ?_⟩
  have haMk : a ∈ conjSubgroup k M :=
    H.centralizer_le_conj hxS hx1 (Subgroup.mem_centralizer_singleton_iff.mpr
      ((mem_centP.mp hxC).2 a ha).symm)
  have haN : a ∈ Subgroup.normalizer (conjSubgroup k B : Set G) := by
    rw [H.normalizer_conj_eq]
    exact haMk
  have h1 : ⁅a, s⁆ ∈ conjSubgroup k B := by
    rw [commutatorElement_def]
    exact (conjSubgroup k B).mul_mem ((Subgroup.mem_normalizer_iff.mp haN s).mp hs)
      ((conjSubgroup k B).inv_mem hs)
  have h2 : ⁅a, s⁆ ∈ B := hmut.outer.pfull a ha s (hkP hs)
  have h3 : ⁅a, s⁆ ∈ B ⊓ conjSubgroup k B := ⟨h2, h1⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hkB, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3.symm

theorem core_exists_member_C (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {h : G}
    (hhP : conjSubgroup h B ≤ P) (hEB : conjSubgroup h B ≠ B)
    (hfac : ∀ p ∈ P, ∃ e ∈ conjSubgroup h B, ∃ c ∈ centP B P g, p = e * c) :
    ∃ k : G, conjSubgroup k B ≤ P ∧ conjSubgroup k B ≠ B ∧ conjSubgroup k B ≤ centP B P g := by
  by_contra hno
  push Not at hno
  have hPle : P ≤ conjSubgroup h B ⊔ B := by
    rw [H.hP]
    refine iSup₂_le fun k hk => ?_
    by_cases hkB : conjSubgroup k B = B
    · rw [hkB]
      exact le_sup_right
    · intro x hx
      have hkP : conjSubgroup k B ≤ P := H.conj_le_P hk
      have hSC : ∀ z ∈ conjSubgroup k B, z ∈ centP B P g → z = 1 := by
        intro z hz hzC
        by_contra hz1
        exact hno k hkP hkB (H.core_dichotomy hmut hkP hkB hz hz1 hzC)
      obtain ⟨e, he, c, hc, rfl⟩ := hfac x (hkP hx)
      by_cases he1 : e = 1
      · subst he1
        rw [one_mul] at hx ⊢
        rw [hSC c hx hc]
        exact one_mem _
      · have hx2 : (e * c) * (e * c) = 1 := H.conj_sq hx
        have hec : e * c = c * e :=
          comm_of_mul_self_eq_one (H.conj_sq he) (H.pair_centP_sq hmut hCen hU hc) hx2
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right
          (H.core_cen_mem_B hmut hCen hU hhP hEB hfac hc he he1 hec.symm))
  have hcommP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    comm_sup_of_comm (fun a ha b hb => H.conj_comm ha hb) (fun a ha b hb => H.B_comm ha hb)
      (fun a ha b hb => (H.center_Q hb (H.P_le_Q (hhP ha))).symm) a (hPle ha) b (hPle hb)
  have hPB : P ≤ B := fun p hp => H.center_P_le_B p hp fun p' hp' => hcommP p hp p' hp'
  exact not_lt_of_ge hPB H.B_lt_P

theorem core_match (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {h k : G}
    (hhP : conjSubgroup h B ≤ P) (hEB : conjSubgroup h B ≠ B)
    (hfac : ∀ p ∈ P, ∃ e ∈ conjSubgroup h B, ∃ c ∈ centP B P g, p = e * c)
    (hkP : conjSubgroup k B ≤ P) (hkB : conjSubgroup k B ≠ B)
    (hkC : conjSubgroup k B ≤ centP B P g) {e₀ : G} (he₀ : e₀ ∈ conjSubgroup h B)
    (he₀1 : e₀ ≠ 1) {y : G} (hy : y ∈ conjSubgroup g B) :
    ∃ s ∈ conjSubgroup k B, ⁅s, e₀⁆ = ⁅y, e₀⁆ := by
  classical
  have he₀Q : e₀ ∈ Q := H.P_le_Q (hhP he₀)
  have hcomm : ∀ u ∈ P, ∀ u' ∈ P, ⁅u * u', e₀⁆ = ⁅u', e₀⁆ * ⁅u, e₀⁆ := fun u hu u' hu' =>
    H.commutator_mul_left_of_mem_Q (H.P_le_Q hu) (H.P_le_Q hu') he₀Q
  let f : conjSubgroup k B → B := fun s =>
    ⟨⁅(s : G), e₀⁆, H.commutator_mem (H.P_le_Q (hkP s.2)) he₀Q⟩
  have hf : Function.Injective f := by
    intro s s' hss'
    have h1 : ⁅(s : G), e₀⁆ = ⁅(s' : G), e₀⁆ := congrArg Subtype.val hss'
    have hinv : ⁅(s : G)⁻¹, e₀⁆ = ⁅(s : G), e₀⁆⁻¹ :=
      H.commutator_inv_left_of_mem_Q (H.P_le_Q (hkP s.2)) he₀Q
    have h2 : ⁅(s : G)⁻¹ * (s' : G), e₀⁆ = 1 := by
      rw [hcomm _ (P.inv_mem (hkP s.2)) _ (hkP s'.2), hinv, ← h1]
      exact mul_inv_cancel _
    have hmem : (s : G)⁻¹ * (s' : G) ∈ conjSubgroup k B :=
      (conjSubgroup k B).mul_mem ((conjSubgroup k B).inv_mem s.2) s'.2
    have h3 : (s : G)⁻¹ * (s' : G) ∈ B := H.core_cen_mem_B hmut hCen hU hhP hEB hfac (hkC hmem)
      he₀ he₀1 (commutatorElement_eq_one_iff_mul_comm.mp h2)
    have h4 : (s : G)⁻¹ * (s' : G) ∈ B ⊓ conjSubgroup k B := ⟨h3, hmem⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hkB, Subgroup.mem_bot, inv_mul_eq_one] at h4
    exact Subtype.ext h4
  have hcard : Nat.card B ≤ Nat.card (conjSubgroup k B) := (card_conjSubgroup k B).symm.le
  have hbij := hf.bijective_of_nat_card_le hcard
  obtain ⟨s, hs⟩ := hbij.2 ⟨⁅y, e₀⁆, hmut.outer.pfull y hy e₀ (hhP he₀)⟩
  exact ⟨s, s.2, congrArg Subtype.val hs⟩

theorem mutual_false (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) : False := by
  have hg := hmut.outer
  obtain ⟨y, hy, hy1⟩ := H.exists_ne_one_mem_conj g
  obtain ⟨h, hhP, e₀, he₀, hne⟩ := H.outer_exists_member hg hCen hU hy hy1
  obtain ⟨-, hfac⟩ := H.outer_exists_mul_cent hg hhP hy hy1 hCen hU he₀ hne
  have he₀1 : e₀ ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hEB : conjSubgroup h B ≠ B := by
    intro hEB
    rw [hEB] at he₀
    exact hne (H.outer_comm_B hg e₀ he₀ y hy)
  obtain ⟨k, hkP, hkB, hkC⟩ := H.core_exists_member_C hmut hCen hU hhP hEB hfac
  obtain ⟨s, hs, hse⟩ := H.core_match hmut hCen hU hhP hEB hfac hkP hkB hkC he₀ he₀1 hy
  have hsC : (s : G)⁻¹ ∈ centP B P g := hkC ((conjSubgroup k B).inv_mem hs)
  have hsQ : (s : G)⁻¹ ∈ Q := H.P_le_Q (mem_centP.mp hsC).1
  have hzform : ∀ e ∈ conjSubgroup h B, ⁅(s : G)⁻¹ * y, e⁆ = ⁅y, e⁆ * ⁅(s : G), e⁆⁻¹ := by
    intro e he
    have hb₁ : ⁅y, e⁆ ∈ B := hg.pfull y hy e (hhP he)
    have e1 : ⁅(s : G)⁻¹ * y, e⁆ = (s : G)⁻¹ * ⁅y, e⁆ * s * ⁅(s : G)⁻¹, e⁆ := by
      simp only [commutatorElement_def]; group
    have e2 : (s : G)⁻¹ * ⁅y, e⁆ * s = ⁅y, e⁆ := by
      rw [← H.center_Q hb₁ hsQ]
      group
    rw [e1, e2, H.commutator_inv_left_of_mem_Q (H.P_le_Q (hkP hs)) (H.P_le_Q (hhP he))]
  have hz0 : ⁅(s : G)⁻¹ * y, e₀⁆ = 1 := by
    rw [hzform e₀ he₀, hse]
    exact mul_inv_cancel _
  have hzN : (s : G)⁻¹ * y ∈ Subgroup.normalizer (conjSubgroup h B : Set G) := by
    rw [H.normalizer_conj_eq]
    exact H.centralizer_le_conj he₀ he₀1 (Subgroup.mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hz0))
  have hzE : ∀ e ∈ conjSubgroup h B, (s : G)⁻¹ * y * e = e * ((s : G)⁻¹ * y) := by
    intro e he
    have h1 : ⁅(s : G)⁻¹ * y, e⁆ ∈ conjSubgroup h B := by
      rw [commutatorElement_def]
      exact (conjSubgroup h B).mul_mem ((Subgroup.mem_normalizer_iff.mp hzN e).mp he)
        ((conjSubgroup h B).inv_mem he)
    have h2 : ⁅(s : G)⁻¹ * y, e⁆ ∈ B := by
      rw [hzform e he]
      exact B.mul_mem (hg.pfull y hy e (hhP he)) (B.inv_mem
        (H.commutator_mem (H.P_le_Q (hkP hs)) (H.P_le_Q (hhP he))))
    have h3 : ⁅(s : G)⁻¹ * y, e⁆ ∈ B ⊓ conjSubgroup h B := ⟨h2, h1⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hEB, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hzcent : ∀ p ∈ P, p * ((s : G)⁻¹ * y) = ((s : G)⁻¹ * y) * p := by
    intro p hp
    obtain ⟨e, he, c, hc, rfl⟩ := hfac p hp
    have hzc : c * ((s : G)⁻¹ * y) = ((s : G)⁻¹ * y) * c := by
      calc c * ((s : G)⁻¹ * y) = (c * (s : G)⁻¹) * y := by group
        _ = ((s : G)⁻¹ * c) * y := by rw [H.core_centP_comm hmut hCen hU hc hsC]
        _ = (s : G)⁻¹ * (c * y) := by group
        _ = (s : G)⁻¹ * (y * c) := by rw [(mem_centP.mp hc).2 y hy]
        _ = ((s : G)⁻¹ * y) * c := by group
    calc e * c * ((s : G)⁻¹ * y) = e * (c * ((s : G)⁻¹ * y)) := by group
      _ = e * (((s : G)⁻¹ * y) * c) := by rw [hzc]
      _ = (e * ((s : G)⁻¹ * y)) * c := by group
      _ = (((s : G)⁻¹ * y) * e) * c := by rw [hzE e he]
      _ = ((s : G)⁻¹ * y) * (e * c) := by group
  have hzQ : (s : G)⁻¹ * y ∉ Q := by
    intro hzQ
    apply H.outer_not_mem_Q hCen hU hg.notLeP hy hy1
    have := Q.mul_mem (H.P_le_Q (hkP hs)) hzQ
    rwa [mul_inv_cancel_left] at this
  have hzD : (s : G)⁻¹ * y ∈ classD B := by
    by_cases hs1 : (s : G) = 1
    · rw [hs1, inv_one, one_mul]
      exact mem_classD_of_mem_conjSubgroup hy hy1
    · have hsD : (s : G)⁻¹ ∈ classD B :=
        mem_classD_of_mem_conjSubgroup ((conjSubgroup k B).inv_mem hs) (inv_ne_one.mpr hs1)
      have hyne : (s : G)⁻¹ ≠ y := by
        intro h'
        have hyP : y ∈ P := h' ▸ hkP ((conjSubgroup k B).inv_mem hs)
        have : y ∈ conjSubgroup g B ⊓ P := ⟨hy, hyP⟩
        rw [H.outer_inf_P hg hCen hU, Subgroup.mem_bot] at this
        exact hy1 this
      exact (H.tim78_4_10 hCen hU hRT h48).2 _ hsD y (mem_classD_of_mem_conjSubgroup hy hy1)
        ((mem_centP.mp hsC).2 y hy) hyne
  obtain ⟨k', b', hb', hb'1, hzk⟩ := hzD
  have hzK : (s : G)⁻¹ * y ∈ conjSubgroup k' B := by
    rw [mem_conjSubgroup, hzk, show k'⁻¹ * (k' * b' * k'⁻¹) * k' = b' by group]
    exact hb'
  have hz1 : (s : G)⁻¹ * y ≠ 1 := by
    intro h1
    apply hb'1
    calc b' = k'⁻¹ * ((s : G)⁻¹ * y) * k' := by rw [hzk]; group
      _ = 1 := by rw [h1]; group
  exact H.not_centralizes_P hCen hU hzK hz1 hzQ hzcent

end Mutual

theorem noPFull (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) : NoPFull M B P := by
  intro g hgM hgP hpf
  exact H.mutual_false (H.mutual_of_outer hCen hU hRT h48 ⟨hgM, hgP, hpf⟩) hCen hU hRT h48

theorem tim78_4_12 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) :
    ¬ ∃ x ∈ classD B, x ∈ M ∧ x ∉ Q ∧ ∀ p ∈ P, ⁅x, p⁆ ∈ B :=
  H.step412_of_noPFull hCen hU hRT h48 (H.noPFull hCen hU hRT h48)

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

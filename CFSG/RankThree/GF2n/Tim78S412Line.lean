module

public import CFSG.RankThree.GF2n.Tim78S412Reduce
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

structure OuterPFull (M B P : Subgroup G) (g : G) : Prop where
  leM : conjSubgroup g B ≤ M
  notLeP : ¬ conjSubgroup g B ≤ P
  pfull : PFull B P g

@[expose] def centP (B P : Subgroup G) (g : G) : Subgroup G :=
  P ⊓ Subgroup.centralizer (conjSubgroup g B : Set G)

theorem mem_centP {B P : Subgroup G} {g c : G} :
    c ∈ centP B P g ↔ c ∈ P ∧ ∀ a ∈ conjSubgroup g B, c * a = a * c := by
  unfold centP
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr Iff.rfl ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
  (hg : OuterPFull M B P g)
include H hg

section Root

theorem outer_ne_B : conjSubgroup g B ≠ B := fun h => hg.notLeP (by rw [h]; exact H.B_le_P)

theorem outer_inf_B : B ⊓ conjSubgroup g B = ⊥ :=
  inf_conjSubgroup_eq_bot_of_isTI H.ti (H.outer_ne_B hg)

theorem outer_comm_B : ∀ b ∈ B, ∀ a ∈ conjSubgroup g B, b * a = a * b :=
  H.commute_of_conj_le_M hg.leM

theorem outer_inf_P (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    conjSubgroup g B ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  exact H.outer_not_mem_Q hCen hU hg.notLeP hx.1 hx1 (H.P_le_Q hx.2)

theorem outer_comm_of_mem_normalizer (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) {p : G} (hp : p ∈ P)
    (hpA : p ∈ Subgroup.normalizer (conjSubgroup g B : Set G)) :
    ∀ a ∈ conjSubgroup g B, p * a = a * p := by
  intro a ha
  have h1 : ⁅p, a⁆ ∈ conjSubgroup g B := by
    rw [commutatorElement_def]
    exact (conjSubgroup g B).mul_mem ((Subgroup.mem_normalizer_iff.mp hpA a).mp ha)
      ((conjSubgroup g B).inv_mem ha)
  have h2 : ⁅p, a⁆ ∈ P := by
    have e : ⁅p, a⁆ = p * (a * p⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem hp ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P (hg.leM ha)) p⁻¹).mp
      (P.inv_mem hp))
  have h3 : ⁅p, a⁆ ∈ conjSubgroup g B ⊓ P := ⟨h1, h2⟩
  rw [H.outer_inf_P hg hCen hU, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
  exact h3

theorem outer_comm_of_comm_one (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {p y : G} (hp : p ∈ P) (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) (hpy : p * y = y * p) :
    ∀ a ∈ conjSubgroup g B, p * a = a * p := by
  refine H.outer_comm_of_mem_normalizer hg hCen hU hp ?_
  have := H.centralizer_le_conj hy hy1 (Subgroup.mem_centralizer_singleton_iff.mpr hpy)
  rwa [← H.normalizer_conj_eq g] at this

theorem outer_commutator_mul {y p p' : G} (hy : y ∈ conjSubgroup g B) (hp : p ∈ P)
    (hp' : p' ∈ P) : ⁅y, p * p'⁆ = ⁅y, p⁆ * ⁅y, p'⁆ := by
  have e : ⁅y, p * p'⁆ = ⁅y, p⁆ * (p * ⁅y, p'⁆ * p⁻¹) := by
    simp only [commutatorElement_def]; group
  have hB : ⁅y, p'⁆ ∈ B := hg.pfull y hy p' hp'
  have hc : p * ⁅y, p'⁆ = ⁅y, p'⁆ * p := (H.center_Q hB (H.P_le_Q hp)).symm
  rw [e, hc]
  group

theorem outer_commutator_inv {y p : G} (hy : y ∈ conjSubgroup g B) (hp : p ∈ P) :
    ⁅y, p⁻¹⁆ = ⁅y, p⁆⁻¹ := by
  have h := H.outer_commutator_mul hg hy hp (P.inv_mem hp)
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem outer_exists_member (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {y : G} (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) :
    ∃ h : G, conjSubgroup h B ≤ P ∧ ∃ e ∈ conjSubgroup h B, e * y ≠ y * e := by
  by_contra hcon
  push Not at hcon
  exact H.not_centralizes_P hCen hU hy hy1 (H.outer_not_mem_Q hCen hU hg.notLeP hy hy1)
    (H.comm_P_of_comm_gens fun h' hh' a ha => hcon h' (H.conj_le_P hh') a ha)

theorem outer_ker_trivial {h y e₀ : G} (hhP : conjSubgroup h B ≤ P) (hy : y ∈ conjSubgroup g B)
    (he₀ : e₀ ∈ conjSubgroup h B) (hne : e₀ * y ≠ y * e₀) :
    ∀ e ∈ conjSubgroup h B, y * e = e * y → e = 1 := by
  intro e he hye
  by_contra he1
  have hyN : y ∈ Subgroup.normalizer (conjSubgroup h B : Set G) := by
    have := H.centralizer_le_conj he he1 (Subgroup.mem_centralizer_singleton_iff.mpr hye)
    rwa [← H.normalizer_conj_eq h] at this
  have hEB : conjSubgroup h B ≠ B := by
    intro hEB
    rw [hEB] at he₀
    exact hne (H.outer_comm_B hg e₀ he₀ y hy)
  have h1 : ⁅y, e₀⁆ ∈ conjSubgroup h B := by
    rw [commutatorElement_def]
    exact (conjSubgroup h B).mul_mem ((Subgroup.mem_normalizer_iff.mp hyN e₀).mp he₀)
      ((conjSubgroup h B).inv_mem he₀)
  have h2 : ⁅y, e₀⁆ ∈ B := hg.pfull y hy e₀ (hhP he₀)
  have h3 : ⁅y, e₀⁆ ∈ B ⊓ conjSubgroup h B := ⟨h2, h1⟩
  rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hEB, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h3
  exact hne h3.symm

theorem outer_exists_surj {h y e₀ : G} (hhP : conjSubgroup h B ≤ P)
    (hy : y ∈ conjSubgroup g B) (he₀ : e₀ ∈ conjSubgroup h B) (hne : e₀ * y ≠ y * e₀) :
    ∀ b ∈ B, ∃ e ∈ conjSubgroup h B, ⁅y, e⁆ = b := by
  classical
  let f : conjSubgroup h B → B := fun e => ⟨⁅y, (e : G)⁆, hg.pfull y hy e (hhP e.2)⟩
  have hf : Function.Injective f := by
    intro e e' hee'
    have h1 : ⁅y, (e : G)⁆ = ⁅y, (e' : G)⁆ := congrArg Subtype.val hee'
    have h2 : ⁅y, (e' : G)⁻¹ * (e : G)⁆ = 1 := by
      rw [H.outer_commutator_mul hg hy (P.inv_mem (hhP e'.2)) (hhP e.2),
        H.outer_commutator_inv hg hy (hhP e'.2), h1]
      exact inv_mul_cancel _
    have h3 := H.outer_ker_trivial hg hhP hy he₀ hne ((e' : G)⁻¹ * (e : G))
      ((conjSubgroup h B).mul_mem ((conjSubgroup h B).inv_mem e'.2) e.2)
      (commutatorElement_eq_one_iff_mul_comm.mp h2)
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  have hcard : Nat.card B ≤ Nat.card (conjSubgroup h B) := (card_conjSubgroup h B).symm.le
  have hbij := hf.bijective_of_nat_card_le hcard
  intro b hb
  obtain ⟨e, he⟩ := hbij.2 ⟨b, hb⟩
  exact ⟨e, e.2, congrArg Subtype.val he⟩

theorem outer_surj_P (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {y : G}
    (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) : ∀ b ∈ B, ∃ p ∈ P, ⁅y, p⁆ = b := by
  obtain ⟨h, hhP, e₀, he₀, hne⟩ := H.outer_exists_member hg hCen hU hy hy1
  intro b hb
  obtain ⟨e, he, hye⟩ := H.outer_exists_surj hg hhP hy he₀ hne b hb
  exact ⟨e, hhP he, hye⟩

theorem outer_exists_mul_cent {h y e₀ : G} (hhP : conjSubgroup h B ≤ P)
    (hy : y ∈ conjSubgroup g B) (hy1 : y ≠ 1) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (he₀ : e₀ ∈ conjSubgroup h B) (hne : e₀ * y ≠ y * e₀) :
    (∀ e ∈ conjSubgroup h B, e ∈ centP B P g → e = 1) ∧
      ∀ p ∈ P, ∃ e ∈ conjSubgroup h B, ∃ c ∈ centP B P g, p = e * c := by
  refine ⟨fun e he hec => ?_, fun p hp => ?_⟩
  · exact H.outer_ker_trivial hg hhP hy he₀ hne e he ((mem_centP.mp hec).2 y hy).symm
  · obtain ⟨e, he, hye⟩ := H.outer_exists_surj hg hhP hy he₀ hne ⁅y, p⁆ (hg.pfull y hy p hp)
    refine ⟨e, he, e⁻¹ * p, mem_centP.mpr ⟨P.mul_mem (P.inv_mem (hhP he)) hp, ?_⟩, by group⟩
    have h1 : ⁅y, e⁻¹ * p⁆ = 1 := by
      rw [H.outer_commutator_mul hg hy (P.inv_mem (hhP he)) hp,
        H.outer_commutator_inv hg hy (hhP he), hye]
      exact inv_mul_cancel _
    exact H.outer_comm_of_comm_one hg hCen hU (P.mul_mem (P.inv_mem (hhP he)) hp) hy hy1
      (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem outer_L_elemAb : Assembly.IsElemAbelian 2 (B ⊔ conjSubgroup g B) :=
  CFSG.Open.IsElemAbelian.sup_of_commute H.elemAb (isElemAbelian_conjSubgroup H.elemAb g)
    (H.outer_comm_B hg)

theorem outer_commutator_mem_B {p a : G} (hp : p ∈ P) (ha : a ∈ conjSubgroup g B) :
    ⁅p, a⁆ ∈ B := by
  rw [← commutatorElement_inv]
  exact B.inv_mem (hg.pfull a ha p hp)

theorem outer_conj_eq {p a : G} (hp : p ∈ P) (ha : a ∈ conjSubgroup g B) :
    p * a * p⁻¹ = ⁅p, a⁆ * a ∧ ⁅p, a⁆ ∈ B :=
  ⟨by simp only [commutatorElement_def]; group, H.outer_commutator_mem_B hg hp ha⟩

theorem outer_P_le_normalizer_L :
    P ≤ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
  intro p hp
  refine Subgroup.mem_normalizer_fintype fun l hl => ?_
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hg b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  obtain ⟨hpa, hpaB⟩ := H.outer_conj_eq hg hp ha
  have hpb : p * b * p⁻¹ = b := by
    rw [show p * b = b * p from (H.center_Q hb (H.P_le_Q hp)).symm, mul_inv_cancel_right]
  have e : p * (b * a) * p⁻¹ = b * (⁅p, a⁆ * a) := by
    calc p * (b * a) * p⁻¹ = (p * b * p⁻¹) * (p * a * p⁻¹) := by group
      _ = b * (⁅p, a⁆ * a) := by rw [hpb, hpa]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left hpaB) (Subgroup.mem_sup_right ha))

theorem outer_conj_mem_classIn {p : G} (hp : p ∈ P) :
    conjSubgroup p (conjSubgroup g B) ∈ classIn B (B ⊔ conjSubgroup g B) := by
  refine ⟨⟨p * g, (conjSubgroup_mul p g B).symm⟩, fun x hx => ?_⟩
  have hx' := mem_conjSubgroup.mp hx
  obtain ⟨hpa, hpaB⟩ := H.outer_conj_eq hg (P.inv_mem hp) hx'
  have e : x = p * (p⁻¹ * x * p) * p⁻¹ := by group
  have e2 : p * (p⁻¹ * x * p) * p⁻¹ = ⁅p, p⁻¹ * x * p⁆ * (p⁻¹ * x * p) := by
    simp only [commutatorElement_def]; group
  rw [e, e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (H.outer_commutator_mem_B hg hp hx'))
    (Subgroup.mem_sup_right hx')

theorem outer_exists_point (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {w : G}
    (hw : w ∈ B ⊔ conjSubgroup g B) (hw1 : w ≠ 1) :
    ∃ U : Subgroup G, (U = B ∨ ∃ p ∈ P, U = conjSubgroup p (conjSubgroup g B)) ∧
      U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U := by
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hg b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hw
  by_cases ha1 : a = 1
  · refine ⟨B, Or.inl rfl, ⟨⟨1, (conjSubgroup_one B).symm⟩, le_sup_left⟩, ?_⟩
    rw [ha1, mul_one]
    exact hb
  · obtain ⟨p, hp, hpa⟩ := H.outer_surj_P hg hCen hU ha ha1 b hb
    refine ⟨conjSubgroup p (conjSubgroup g B), Or.inr ⟨p, hp, rfl⟩,
      H.outer_conj_mem_classIn hg hp, ?_⟩
    have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by
      have := H.sq_eq_one b hb
      rwa [sq] at this)
    have h1 : ⁅p, a⁆ = b := by rw [← commutatorElement_inv, hpa, hbb]
    have h2 : b * a = p * a * p⁻¹ := by
      rw [(H.outer_conj_eq hg hp ha).1, h1]
    rw [mem_conjSubgroup, h2, show p⁻¹ * (p * a * p⁻¹) * p = a by group]
    exact ha

theorem outer_partition_L (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    ∀ w ∈ B ⊔ conjSubgroup g B, w ≠ 1 →
      ∃! U, U ∈ classIn B (B ⊔ conjSubgroup g B) ∧ w ∈ U := by
  intro w hw hw1
  obtain ⟨U, -, hUc, hwU⟩ := H.outer_exists_point hg hCen hU hw hw1
  refine ⟨U, ⟨hUc, hwU⟩, fun U' ⟨hU'c, hwU'⟩ => ?_⟩
  obtain ⟨⟨x, hx⟩, -⟩ := hUc
  obtain ⟨⟨x', hx'⟩, -⟩ := hU'c
  by_contra hne
  have hne' : conjSubgroup x' B ≠ conjSubgroup x B := fun h => hne (by rw [hx, hx', h])
  have hinf := H.inf_eq_bot_of_conj_ne hne'
  have : w ∈ conjSubgroup x' B ⊓ conjSubgroup x B := ⟨hx' ▸ hwU', hx ▸ hwU⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact hw1 this

theorem outer_classIn_cases (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {U : Subgroup G} (hUc : U ∈ classIn B (B ⊔ conjSubgroup g B)) :
    U = B ∨ ∃ p ∈ P, U = conjSubgroup p (conjSubgroup g B) := by
  obtain ⟨⟨x, hx⟩, hUL⟩ := hUc
  obtain ⟨w, hwU, hw1⟩ : ∃ w ∈ U, w ≠ 1 := by
    obtain ⟨w, hw, hw1⟩ := H.exists_ne_one_mem_conj x
    exact ⟨w, hx ▸ hw, hw1⟩
  obtain ⟨U₀, hU₀, hU₀c, hwU₀⟩ := H.outer_exists_point hg hCen hU (hUL hwU) hw1
  have huniq := H.outer_partition_L hg hCen hU w (hUL hwU) hw1
  obtain ⟨V, -, hV⟩ := huniq
  have e1 : U = V := hV U ⟨⟨⟨x, hx⟩, hUL⟩, hwU⟩
  have e2 : U₀ = V := hV U₀ ⟨hU₀c, hwU₀⟩
  rw [e1, ← e2]
  exact hU₀

theorem outer_commutator_L_P {l p : G} (hl : l ∈ B ⊔ conjSubgroup g B) (hp : p ∈ P) :
    ⁅l, p⁆ ∈ B := by
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hg b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  have e : ⁅b * a, p⁆ = b * ⁅a, p⁆ * b⁻¹ * ⁅b, p⁆ := by
    simp only [commutatorElement_def]; group
  have h1 : ⁅b, p⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (H.center_Q hb (H.P_le_Q hp))
  rw [e, h1, mul_one]
  exact B.mul_mem (B.mul_mem hb (hg.pfull a ha p hp)) (B.inv_mem hb)

theorem outer_conj_ne_of_not_cent {p : G} (hp : p ∈ P) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (hpc : p ∉ centP B P g) :
    conjSubgroup p (conjSubgroup g B) ≠ conjSubgroup g B := fun h =>
  hpc (mem_centP.mpr ⟨hp, H.outer_comm_of_mem_normalizer hg hCen hU hp
    (conjSubgroup_eq_self_iff.mp h)⟩)

theorem outer_conj_ne_B {p : G} (hp : p ∈ P) : conjSubgroup p (conjSubgroup g B) ≠ B := by
  intro h
  apply H.outer_ne_B hg
  have hpM : p⁻¹ ∈ M := M.inv_mem (H.P_le_M hp)
  have e : conjSubgroup g B = conjSubgroup p⁻¹ (conjSubgroup p (conjSubgroup g B)) := by
    rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  rw [e, h]
  exact H.conj_eq_iff.mpr hpM

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

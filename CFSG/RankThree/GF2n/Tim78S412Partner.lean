module

public import CFSG.RankThree.GF2n.Tim78S412Line
public import CFSG.RankThree.GF2n.Tim78S47

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

structure MutualPFull (M B P : Subgroup G) (g : G) : Prop where
  outer : OuterPFull M B P g
  partner : ∀ b ∈ B, ∀ u ∈ conjSubgroup g P, ⁅b, u⁆ ∈ conjSubgroup g B

theorem conjSubgroup_inv_conjSubgroup (g : G) (X : Subgroup G) :
    conjSubgroup g⁻¹ (conjSubgroup g X) = X := by
  rw [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]

theorem partner_of_pfull_inv {B P : Subgroup G} {g : G} (h : PFull B P g⁻¹) :
    ∀ b ∈ B, ∀ u ∈ conjSubgroup g P, ⁅b, u⁆ ∈ conjSubgroup g B := by
  intro b hb u hu
  have hb' : g⁻¹ * b * g ∈ conjSubgroup g⁻¹ B := by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hb
  have hu' : g⁻¹ * u * g ∈ P := mem_conjSubgroup.mp hu
  have h3 := h _ hb' _ hu'
  rw [mem_conjSubgroup]
  rwa [show g⁻¹ * ⁅b, u⁆ * g = ⁅g⁻¹ * b * g, g⁻¹ * u * g⁆ by
    simp only [commutatorElement_def]; group]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

theorem conj_P_eq_of_conj_B_eq {x y : G} (h : conjSubgroup x B = conjSubgroup y B) :
    conjSubgroup x P = conjSubgroup y P := by
  have hm : y⁻¹ * x ∈ M := by
    rw [← H.normalizer_B, ← conjSubgroup_eq_self_iff, conjSubgroup_mul, h,
      conjSubgroup_inv_conjSubgroup]
  have e : conjSubgroup x P = conjSubgroup y (conjSubgroup (y⁻¹ * x) P) := by
    rw [← conjSubgroup_mul, mul_inv_cancel_left]
  rw [e, conjSubgroup_eq_self_iff.mpr (H.M_le_normalizer_P hm)]

section Root

theorem mutual_of_outer (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) (hg : OuterPFull M B P g) :
    MutualPFull M B P g := by
  refine ⟨hg, ?_⟩
  by_cases hpf : PFull B P g⁻¹
  · exact partner_of_pfull_inv hpf
  have hgM' : conjSubgroup g⁻¹ B ≤ M := H.conj_le_M_symm hg.leM
  have hgP' : ¬ conjSubgroup g⁻¹ B ≤ P := by
    intro h
    have := H.conj_inv_le_P_of_conj_le_P h
    rw [inv_inv] at this
    exact hg.notLeP this
  have htf := H.tfull_of_not_pfull hCen hU hRT h48 hgM' hgP' hpf
  have hBT := comm_conj_T_of_partner htf
  have hBC : ∀ b ∈ B, (∀ t ∈ conjSubgroup g T, t * b = b * t) → b = 1 := by
    intro b hb hbc
    by_contra hb1
    have h47 := (H.conj g).tim78_4_7 hCen hU g⁻¹
    have hne : conjSubgroup g⁻¹ (conjSubgroup g B) ⊓
        Subgroup.centralizer (conjSubgroup g T : Set G) ≠ ⊥ := by
      intro hbot
      have hb' : b ∈ conjSubgroup g⁻¹ (conjSubgroup g B) ⊓
          Subgroup.centralizer (conjSubgroup g T : Set G) := by
        rw [conjSubgroup_inv_conjSubgroup]
        exact ⟨hb, Subgroup.mem_centralizer_iff.mpr fun t ht => hbc t ht⟩
      rw [hbot, Subgroup.mem_bot] at hb'
      exact hb1 hb'
    have h1 := h47 hne
    rw [conjSubgroup_inv_conjSubgroup] at h1
    refine hgP' fun x hx => ?_
    have hx1 : g * x * g⁻¹ ∈ B := by
      have := mem_conjSubgroup.mp hx
      rwa [inv_inv] at this
    have := mem_conjSubgroup.mp (h1 hx1)
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  obtain ⟨t, htT, htB⟩ : ∃ t ∈ conjSubgroup g T, conjSubgroup t B ≠ B := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb, hb1⟩ := H.exists_ne_one_mem_conj 1
    rw [conjSubgroup_one] at hb
    refine hb1 (hBC b hb fun t ht => ?_)
    have htN : t ∈ Subgroup.normalizer (B : Set G) := conjSubgroup_eq_self_iff.mp (hcon t ht)
    have h1 : ⁅b, t⁆ ∈ conjSubgroup g B := hBT b hb t ht
    have h2 : ⁅b, t⁆ ∈ B := by
      have e : ⁅b, t⁆ = b * (t * b⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.mp htN b⁻¹).mp (B.inv_mem hb))
    have h3 : ⁅b, t⁆ ∈ B ⊓ conjSubgroup g B := ⟨h2, h1⟩
    rw [H.outer_inf_B hg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hAle : conjSubgroup g B ≤ conjSubgroup g P := Subgroup.map_mono H.B_le_P
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hg b hb a ha).symm
  have htL : ∀ l ∈ B ⊔ conjSubgroup g B, t * l * t⁻¹ ∈ B ⊔ conjSubgroup g B := by
    intro l hl
    obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
    have hta : t * a * t⁻¹ = a := by
      rw [H.conj_T_le_centralizer_conj_P g t htT a (hAle ha), mul_inv_cancel_right]
    have htbA : ⁅t, b⁆ ∈ conjSubgroup g B := by
      rw [← commutatorElement_inv]
      exact (conjSubgroup g B).inv_mem (hBT b hb t htT)
    have e : t * (b * a) * t⁻¹ = (⁅t, b⁆ * b) * a := by
      calc t * (b * a) * t⁻¹ = (t * b * t⁻¹) * (t * a * t⁻¹) := by group
        _ = (⁅t, b⁆ * b) * a := by
          rw [hta]
          simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right htbA)
      (Subgroup.mem_sup_left hb)) (Subgroup.mem_sup_right ha)
  have htN : t ∈ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype htL
  have hS₁ : conjSubgroup t B ∈ classIn B (B ⊔ conjSubgroup g B) :=
    ⟨⟨t, rfl⟩, fun x hx => by
      have hx' := mem_conjSubgroup.mp hx
      have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [e]
      exact htL _ (Subgroup.mem_sup_left hx')⟩
  obtain ⟨p₁, hp₁, hS⟩ := (H.outer_classIn_cases hg hCen hU hS₁).resolve_left htB
  set h := p₁⁻¹ * t with hh
  have hBh : conjSubgroup h B = conjSubgroup g B := by
    rw [hh, conjSubgroup_mul, hS, conjSubgroup_inv_conjSubgroup]
  have hhN : h ∈ Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (H.outer_P_le_normalizer_L hg hp₁)) htN
  have hPh : conjSubgroup h P = conjSubgroup g P := H.conj_P_eq_of_conj_B_eq hBh
  intro b hb u hu
  rw [← hPh] at hu
  have hp : h⁻¹ * u * h ∈ P := mem_conjSubgroup.mp hu
  have hl : h⁻¹ * b * h ∈ B ⊔ conjSubgroup g B := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) b).mp
      (Subgroup.mem_sup_left hb)
    simpa using this
  have h1 := H.outer_commutator_L_P hg hl hp
  rw [← hBh, mem_conjSubgroup]
  rwa [show h⁻¹ * ⁅b, u⁆ * h = ⁅h⁻¹ * b * h, h⁻¹ * u * h⁆ by
    simp only [commutatorElement_def]; group]

theorem outer_conj_of_mutual (hmut : MutualPFull M B P g) :
    OuterPFull (conjSubgroup g M) (conjSubgroup g B) (conjSubgroup g P) g⁻¹ where
  leM := by
    rw [conjSubgroup_inv_conjSubgroup]
    intro x hx
    rw [mem_conjSubgroup]
    have hx' : g⁻¹ * x * g ∈ conjSubgroup g⁻¹ B := by
      rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      exact hx
    exact H.conj_le_M_symm hmut.outer.leM hx'
  notLeP := by
    rw [conjSubgroup_inv_conjSubgroup]
    intro h
    have h1 : conjSubgroup g⁻¹ B ≤ P := fun x hx => by
      have hx1 : g * x * g⁻¹ ∈ B := by
        have := mem_conjSubgroup.mp hx
        rwa [inv_inv] at this
      have := mem_conjSubgroup.mp (h hx1)
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    have := H.conj_inv_le_P_of_conj_le_P h1
    rw [inv_inv] at this
    exact hmut.outer.notLeP this
  pfull := fun a ha p hp => by
    rw [conjSubgroup_inv_conjSubgroup] at ha
    exact hmut.partner a ha p hp

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

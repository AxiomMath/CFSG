module

public import CFSG.RankThree.GF2n.Tim78S411
public import CFSG.RankThree.GF2n.Tim78S412Stmt

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def PFull (B P : Subgroup G) (g : G) : Prop :=
  ∀ a ∈ conjSubgroup g B, ∀ p ∈ P, ⁅a, p⁆ ∈ B

@[expose] def NoPFull (M B P : Subgroup G) : Prop :=
  ∀ g : G, conjSubgroup g B ≤ M → ¬ conjSubgroup g B ≤ P → ¬ PFull B P g

theorem mem_classD_of_mem_conjSubgroup {B : Subgroup G} {g a : G} (ha : a ∈ conjSubgroup g B)
    (ha1 : a ≠ 1) : a ∈ classD B := by
  refine ⟨g, g⁻¹ * a * g, mem_conjSubgroup.mp ha, ?_, by group⟩
  intro h
  apply ha1
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem comm_conj_T_of_partner {B T : Subgroup G} {g : G}
    (h2 : ∀ a ∈ conjSubgroup g⁻¹ B, ∀ t ∈ T, ⁅a, t⁆ ∈ B) :
    ∀ b ∈ B, ∀ t ∈ conjSubgroup g T, ⁅b, t⁆ ∈ conjSubgroup g B := by
  intro b hb t ht
  have hb' : g⁻¹ * b * g ∈ conjSubgroup g⁻¹ B := by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hb
  have ht' : g⁻¹ * t * g ∈ T := mem_conjSubgroup.mp ht
  have h3 := h2 _ hb' _ ht'
  rw [mem_conjSubgroup]
  rwa [show g⁻¹ * ⁅b, t⁆ * g = ⁅g⁻¹ * b * g, g⁻¹ * t * g⁆ by
    simp only [commutatorElement_def]; group]


namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem outer_not_mem_Q (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {g : G}
    (hgP : ¬ conjSubgroup g B ≤ P) {a : G} (ha : a ∈ conjSubgroup g B) (ha1 : a ≠ 1) :
    a ∉ Q := by
  intro haQ
  refine hgP (H.tim78_4_5 hCen hU g fun hbot => ha1 ?_)
  have : a ∈ conjSubgroup g B ⊓ Q := ⟨ha, haQ⟩
  rwa [hbot, Subgroup.mem_bot] at this

theorem outer_pfull_or_tfull (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) {g : G} (hgM : conjSubgroup g B ≤ M)
    (hgP : ¬ conjSubgroup g B ≤ P) {a : G} (ha : a ∈ conjSubgroup g B) :
    (∀ p ∈ P, ⁅a, p⁆ ∈ B) ∨ (∀ t ∈ T, ⁅a, t⁆ ∈ B) := by
  by_cases ha1 : a = 1
  · left
    intro p _
    rw [ha1, commutatorElement_one_left]
    exact B.one_mem
  exact H.tim78_4_11 hCen hU hRT h48 a (mem_classD_of_mem_conjSubgroup ha ha1) (hgM ha)
    (H.outer_not_mem_Q hCen hU hgP ha ha1)

theorem tfull_of_not_pfull (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) {g : G} (hgM : conjSubgroup g B ≤ M)
    (hgP : ¬ conjSubgroup g B ≤ P) (hnp : ¬ PFull B P g) :
    ∀ a ∈ conjSubgroup g B, ∀ t ∈ T, ⁅a, t⁆ ∈ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₂, ha₂, t₂, ht₂, ht₂B⟩ := hcon
  unfold PFull at hnp
  push Not at hnp
  obtain ⟨a₁, ha₁, p₁, hp₁, hp₁B⟩ := hnp
  have hmulB : ∀ {m b : G}, m ∈ M → b ∈ B → m * b * m⁻¹ ∈ B := fun hm hb =>
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B hm) _).mp hb
  have ha₁M : a₁ ∈ M := hgM ha₁
  have ha₂M : a₂ ∈ M := hgM ha₂
  have ha₁₂ : a₁ * a₂ ∈ conjSubgroup g B := (conjSubgroup g B).mul_mem ha₁ ha₂
  have ha₁sq : a₁ * a₁ = 1 := H.conj_sq ha₁
  have ha₂sq : a₂ * a₂ = 1 := H.conj_sq ha₂
  have ha₂P : ∀ p ∈ P, ⁅a₂, p⁆ ∈ B := by
    rcases H.outer_pfull_or_tfull hCen hU hRT h48 hgM hgP ha₂ with h | h
    · exact h
    · exact absurd (h t₂ ht₂) ht₂B
  have ha₁T : ∀ t ∈ T, ⁅a₁, t⁆ ∈ B := by
    rcases H.outer_pfull_or_tfull hCen hU hRT h48 hgM hgP ha₁ with h | h
    · exact absurd (h p₁ hp₁) hp₁B
    · exact h
  rcases H.outer_pfull_or_tfull hCen hU hRT h48 hgM hgP ha₁₂ with h | h
  ·
    apply hp₁B
    have e : a₁ = (a₁ * a₂) * a₂ := by
      rw [mul_assoc, ha₂sq, mul_one]
    have e2 : ⁅(a₁ * a₂) * a₂, p₁⁆ =
        (a₁ * a₂) * ⁅a₂, p₁⁆ * (a₁ * a₂)⁻¹ * ⁅a₁ * a₂, p₁⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, e2]
    exact B.mul_mem (hmulB (hgM ha₁₂) (ha₂P p₁ hp₁)) (h p₁ hp₁)
  ·
    apply ht₂B
    have e : a₂ = a₁ * (a₁ * a₂) := by
      rw [← mul_assoc, ha₁sq, one_mul]
    have e2 : ⁅a₁ * (a₁ * a₂), t₂⁆ = a₁ * ⁅a₁ * a₂, t₂⁆ * a₁⁻¹ * ⁅a₁, t₂⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, e2]
    exact B.mul_mem (hmulB ha₁M (h t₂ ht₂)) (ha₁T t₂ ht₂)

theorem hyp48_of_tfull {g : G} (hgM : conjSubgroup g B ≤ M)
    (h1 : ∀ a ∈ conjSubgroup g B, ∀ t ∈ T, ⁅a, t⁆ ∈ B)
    (h2 : ∀ a ∈ conjSubgroup g⁻¹ B, ∀ t ∈ T, ⁅a, t⁆ ∈ B) : Hyp48 M B T g :=
  ⟨hgM, h1, comm_conj_T_of_partner h2⟩

theorem step412_of_noPFull (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) (hnp : NoPFull M B P) :
    Step412 M B P Q := by
  rintro ⟨x, hxD, hxM, hxQ, hxP⟩
  obtain ⟨g, b0, hb0, hb01, hx⟩ := hxD
  have hxg : x ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup, hx, show g⁻¹ * (g * b0 * g⁻¹) * g = b0 by group]
    exact hb0
  have hgM : conjSubgroup g B ≤ M := hRT g b0 hb0 hb01 (hx ▸ hxM)
  have hgP : ¬ conjSubgroup g B ≤ P := fun h => hxQ (H.P_le_Q (h hxg))
  have hgM' : conjSubgroup g⁻¹ B ≤ M := H.conj_le_M_symm hgM
  have hgP' : ¬ conjSubgroup g⁻¹ B ≤ P := by
    intro h
    have := H.conj_inv_le_P_of_conj_le_P h
    rw [inv_inv] at this
    exact hgP this
  by_cases hpf : PFull B P g
  · exact hnp g hgM hgP hpf
  · exact hgP (h48 g (H.hyp48_of_tfull hgM
      (H.tfull_of_not_pfull hCen hU hRT h48 hgM hgP hpf)
      (H.tfull_of_not_pfull hCen hU hRT h48 hgM' hgP' (hnp g⁻¹ hgM' hgP'))))

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

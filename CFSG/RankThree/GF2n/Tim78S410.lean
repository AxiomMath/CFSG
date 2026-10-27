module

public import CFSG.RankThree.GF2n.Tim78S410Core
public import CFSG.RankThree.GF2n.Tim78S4LemA

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem tim78_4_10_first (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) :
    ∀ x ∈ classD B, x ∈ M → x ∉ Q → ∀ b ∈ B, x * b ∈ classD B := by
  intro x hx hxM hxQ b hb
  obtain ⟨k, b0, hb0, hb01, hxk⟩ := hx
  have hxD : x ∈ classD B := ⟨k, b0, hb0, hb01, hxk⟩
  have hxK : x ∈ conjSubgroup k B := by
    rw [mem_conjSubgroup, hxk, show k⁻¹ * (k * b0 * k⁻¹) * k = b0 by group]
    exact hb0
  have hx1 : x ≠ 1 := by
    intro h
    apply hb01
    calc b0 = k⁻¹ * x * k := by rw [hxk]; group
      _ = 1 := by rw [h]; group
  have hKM : conjSubgroup k B ≤ M := hRT k b0 hb0 hb01 (hxk ▸ hxM)
  have hxC : ∀ b ∈ B, x * b = b * x := fun b hb =>
    (H.commute_of_conj_le_M hKM b hb x hxK).symm
  have hx2 : x * x = 1 := H.conj_sq hxK
  obtain ⟨g, hgP, a, ha, hax⟩ : ∃ g : G, conjSubgroup g B ≤ P ∧
      ∃ a ∈ conjSubgroup g B, a * x ≠ x * a := by
    by_contra hcon
    push Not at hcon
    exact H.not_centralizes_P hCen hU hxK hx1 hxQ
      (H.comm_P_of_comm_gens fun g hg a ha => hcon g (H.conj_le_P hg) a ha)
  have hgB : conjSubgroup g B ≠ B := by
    intro h
    rw [h] at ha
    exact hax (hxC a ha).symm
  have hconj : ∀ z : G, z * x * z⁻¹ = x * b → x * b ∈ classD B := fun z hz => by
    rw [← hz]
    exact mem_classD_conj hxD z
  by_cases hc : ∀ a ∈ conjSubgroup g B, ∀ b' ∈ conjSubgroup (x * g) B, a * b' = b' * a
  · obtain ⟨z, hz⟩ := H.exists_conj_eq_mul_of_comm hCen hU h48 hxM hx2 hx1 hxC hgP hgB
      ⟨a, ha, hax⟩ hc b hb
    exact hconj z hz
  · obtain ⟨e, -, hsq⟩ := H.exists_sq_eq_of_noncomm hxM hx2 hxC hgP hgB hc b hb
    refine hconj ⁅x, e⁆ ?_
    have hbi : b⁻¹ = b := by
      refine inv_eq_of_mul_eq_one_right ?_
      have := H.sq_eq_one b hb
      rwa [sq] at this
    rw [comm_mul_conj_of_mul_self_eq_one hx2 e, hsq, hbi]

theorem tim78_4_10_second (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hfirst : ∀ x ∈ classD B, x ∈ M → x ∉ Q → ∀ b ∈ B, x * b ∈ classD B) :
    ∀ a ∈ classD B, ∀ b ∈ classD B, a * b = b * a → a ≠ b → a * b ∈ classD B := by
  have key : ∀ a ∈ B, a ≠ 1 → ∀ b ∈ classD B, a * b = b * a → a ≠ b → a * b ∈ classD B := by
    intro a ha ha1 b hb hab hne
    have haa : a * a = 1 := by
      have := H.sq_eq_one a ha
      rwa [sq] at this
    obtain ⟨j, b1, hb1, hb11, hbj⟩ := hb
    have hbD : b ∈ classD B := ⟨j, b1, hb1, hb11, hbj⟩
    have hbj' : b ∈ conjSubgroup j B := by
      rw [mem_conjSubgroup, hbj, show j⁻¹ * (j * b1 * j⁻¹) * j = b1 by group]
      exact hb1
    have hb1' : b ≠ 1 := by
      intro h
      apply hb11
      calc b1 = j⁻¹ * b * j := by rw [hbj]; group
        _ = 1 := by rw [h]; group
    have hbM : b ∈ M := (H.normalizer_eq_and_centralizer_le.2 a ha ha1)
      (Subgroup.mem_centralizer_singleton_iff.mpr hab.symm)
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hne
      have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [hb']
      exact (inv_eq_of_mul_eq_one_right haa).symm
    by_cases hbQ : b ∈ Q
    · have hne' : conjSubgroup j B ⊓ Q ≠ ⊥ := by
        intro hbot
        have : b ∈ conjSubgroup j B ⊓ Q := ⟨hbj', hbQ⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact hb1' this
      have hjP := H.tim78_4_5 hCen hU j hne'
      by_cases hjB : conjSubgroup j B = B
      · have hbB : b ∈ B := hjB ▸ hbj'
        exact ⟨1, a * b, B.mul_mem ha hbB, hab1, by simp⟩
      · have habU : a * b ∈ B ⊔ conjSubgroup j B :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbj')
        obtain ⟨F, ⟨⟨f, hf⟩, -⟩, hwF⟩ := (H.partition_of_le_P hjP hjB _ habU hab1).exists
        rw [hf, mem_conjSubgroup] at hwF
        refine ⟨f, f⁻¹ * (a * b) * f, hwF, ?_, by group⟩
        intro h
        apply hab1
        calc a * b = f * (f⁻¹ * (a * b) * f) * f⁻¹ := by group
          _ = 1 := by rw [h]; group
    · have := hfirst b hbD hbM hbQ a ha
      rwa [← hab] at this
  intro a ha b hb hab hne
  obtain ⟨k, a0, ha0, ha01, hak⟩ := ha
  have hb0 : k⁻¹ * b * k ∈ classD B := by
    have := mem_classD_conj hb k⁻¹
    simpa using this
  have hcomm0 : a0 * (k⁻¹ * b * k) = (k⁻¹ * b * k) * a0 := by
    have e1 : a0 = k⁻¹ * a * k := by rw [hak]; group
    rw [e1]
    calc k⁻¹ * a * k * (k⁻¹ * b * k) = k⁻¹ * (a * b) * k := by group
      _ = k⁻¹ * (b * a) * k := by rw [hab]
      _ = k⁻¹ * b * k * (k⁻¹ * a * k) := by group
  have hne0 : a0 ≠ k⁻¹ * b * k := by
    intro h
    apply hne
    calc a = k * a0 * k⁻¹ := hak
      _ = k * (k⁻¹ * b * k) * k⁻¹ := by rw [h]
      _ = b := by group
  have h1 := mem_classD_conj (key a0 ha0 ha01 _ hb0 hcomm0 hne0) k
  rwa [show k * (a0 * (k⁻¹ * b * k)) * k⁻¹ = a * b by rw [hak]; group] at h1

theorem tim78_4_10 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) :
    (∀ x ∈ classD B, x ∈ M → x ∉ Q → ∀ b ∈ B, x * b ∈ classD B) ∧
    (∀ a ∈ classD B, ∀ b ∈ classD B, a * b = b * a → a ≠ b → a * b ∈ classD B) :=
  ⟨H.tim78_4_10_first hCen hU hRT h48,
    H.tim78_4_10_second hCen hU (H.tim78_4_10_first hCen hU hRT h48)⟩

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78

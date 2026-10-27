module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aX

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.exists_H0_generators_of_actions (h : FF81Hyp b L)
    {b₁ b₂ b₃ n₁ n₂ n₃ : G} (hn₁ : n₁ ∈ L) (hn₂ : n₂ ∈ L) (hn₃ : n₃ ∈ L)
    (hn₁b₁ : n₁ * b₁ * n₁⁻¹ = b₁⁻¹) (hn₁b₂ : n₁ * b₂ * n₁⁻¹ = b₂)
    (hn₁b₃ : n₁ * b₃ * n₁⁻¹ = b₃)
    (hn₂b₁ : n₂ * b₁ * n₂⁻¹ = b₂) (hn₂b₂ : n₂ * b₂ * n₂⁻¹ = b₁)
    (hn₂b₃ : n₂ * b₃ * n₂⁻¹ = b₃)
    (hn₃b₁ : n₃ * b₁ * n₃⁻¹ = b₂) (hn₃b₂ : n₃ * b₂ * n₃⁻¹ = b₃)
    (hn₃b₃ : n₃ * b₃ * n₃⁻¹ = b₁)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) :
    ∃ t₁ s c : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G)),
      t₁ ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ∧
      s ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ∧
      c ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) ∧
      (t₁ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ t₁ ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹ ∧
        t₁ ⟨b₂, hb₂B⟩ = ⟨b₂, hb₂B⟩ ∧ t₁ ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩) ∧
      (s ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ s ⟨b₁, hb₁B⟩ = ⟨b₂, hb₂B⟩ ∧
        s ⟨b₂, hb₂B⟩ = ⟨b₁, hb₁B⟩ ∧ s ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩) ∧
      (c ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ c ⟨b₁, hb₁B⟩ = ⟨b₂, hb₂B⟩ ∧
        c ⟨b₂, hb₂B⟩ = ⟨b₃, hb₃B⟩ ∧ c ⟨b₃, hb₃B⟩ = ⟨b₁, hb₁B⟩) := by
  classical
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  have hb (n : G) (hn : n ∈ L) : n * b * n⁻¹ = b := by
    have hc : Commute n b := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hn)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hnor (n : G) (hnb : n * b * n⁻¹ = b)
      (h₁ : n * b₁ * n⁻¹ ∈ B) (h₂ : n * b₂ * n⁻¹ ∈ B) (h₃ : n * b₃ * n⁻¹ ∈ B) :
      n ∈ Nor B := by
    show n ∈ Nor (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    refine mem_nor_of_gen (S := ({b, b₁, b₂, b₃} : Set G)) ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [hnb]
      exact Subgroup.subset_closure (by simp)
    · exact h₁
    · exact h₂
    · exact h₃
  have hn₁N : n₁ ∈ Nor B := by
    refine hnor n₁ (hb n₁ hn₁) ?_ ?_ ?_
    · rw [hn₁b₁]
      exact B.inv_mem (Subgroup.subset_closure (by simp))
    · rw [hn₁b₂]
      exact Subgroup.subset_closure (by simp)
    · rw [hn₁b₃]
      exact Subgroup.subset_closure (by simp)
  have hn₂N : n₂ ∈ Nor B := by
    refine hnor n₂ (hb n₂ hn₂) ?_ ?_ ?_
    · rw [hn₂b₁]
      exact Subgroup.subset_closure (by simp)
    · rw [hn₂b₂]
      exact Subgroup.subset_closure (by simp)
    · rw [hn₂b₃]
      exact Subgroup.subset_closure (by simp)
  have hn₃N : n₃ ∈ Nor B := by
    refine hnor n₃ (hb n₃ hn₃) ?_ ?_ ?_
    · rw [hn₃b₁]
      exact Subgroup.subset_closure (by simp)
    · rw [hn₃b₂]
      exact Subgroup.subset_closure (by simp)
    · rw [hn₃b₃]
      exact Subgroup.subset_closure (by simp)
  let t₁ : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hn₁N⟩
  let s : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hn₂N⟩
  let c : MulAut ↥B := Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hn₃N⟩
  have hcoe₁ : ∀ x : ↥B,
      ((Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hn₁N⟩) x : G) = n₁ * (x : G) * n₁⁻¹ := by
    intro x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hcoe₂ : ∀ x : ↥B,
      ((Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hn₂N⟩) x : G) = n₂ * (x : G) * n₂⁻¹ := by
    intro x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hcoe₃ : ∀ x : ↥B,
      ((Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hn₃N⟩) x : G) = n₃ * (x : G) * n₃⁻¹ := by
    intro x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have ht₁X : t₁ ∈ FF81X B := by
    rw [mem_FF81X_iff]
    exact ⟨⟨n₁, hn₁N⟩, rfl⟩
  have hsX : s ∈ FF81X B := by
    rw [mem_FF81X_iff]
    exact ⟨⟨n₂, hn₂N⟩, rfl⟩
  have hcX : c ∈ FF81X B := by
    rw [mem_FF81X_iff]
    exact ⟨⟨n₃, hn₃N⟩, rfl⟩
  have ht₁ : t₁ ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ t₁ ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹ ∧
      t₁ ⟨b₂, hb₂B⟩ = ⟨b₂, hb₂B⟩ ∧ t₁ ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hn₁N⟩) ⟨b, hbB⟩ : G) = b
      rw [hcoe₁, Subgroup.coe_mk]
      exact hb n₁ hn₁
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hn₁N⟩) ⟨b₁, hb₁B⟩ : G) = b₁⁻¹
      rw [hcoe₁, Subgroup.coe_mk]
      exact hn₁b₁
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hn₁N⟩) ⟨b₂, hb₂B⟩ : G) = b₂
      rw [hcoe₁, Subgroup.coe_mk]
      exact hn₁b₂
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₁, hn₁N⟩) ⟨b₃, hb₃B⟩ : G) = b₃
      rw [hcoe₁, Subgroup.coe_mk]
      exact hn₁b₃
  have hs : s ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ s ⟨b₁, hb₁B⟩ = ⟨b₂, hb₂B⟩ ∧
      s ⟨b₂, hb₂B⟩ = ⟨b₁, hb₁B⟩ ∧ s ⟨b₃, hb₃B⟩ = ⟨b₃, hb₃B⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hn₂N⟩) ⟨b, hbB⟩ : G) = b
      rw [hcoe₂, Subgroup.coe_mk]
      exact hb n₂ hn₂
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hn₂N⟩) ⟨b₁, hb₁B⟩ : G) = b₂
      rw [hcoe₂, Subgroup.coe_mk]
      exact hn₂b₁
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hn₂N⟩) ⟨b₂, hb₂B⟩ : G) = b₁
      rw [hcoe₂, Subgroup.coe_mk]
      exact hn₂b₂
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₂, hn₂N⟩) ⟨b₃, hb₃B⟩ : G) = b₃
      rw [hcoe₂, Subgroup.coe_mk]
      exact hn₂b₃
  have hc : c ⟨b, hbB⟩ = ⟨b, hbB⟩ ∧ c ⟨b₁, hb₁B⟩ = ⟨b₂, hb₂B⟩ ∧
      c ⟨b₂, hb₂B⟩ = ⟨b₃, hb₃B⟩ ∧ c ⟨b₃, hb₃B⟩ = ⟨b₁, hb₁B⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hn₃N⟩) ⟨b, hbB⟩ : G) = b
      rw [hcoe₃, Subgroup.coe_mk]
      exact hb n₃ hn₃
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hn₃N⟩) ⟨b₁, hb₁B⟩ : G) = b₂
      rw [hcoe₃, Subgroup.coe_mk]
      exact hn₃b₁
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hn₃N⟩) ⟨b₂, hb₂B⟩ : G) = b₃
      rw [hcoe₃, Subgroup.coe_mk]
      exact hn₃b₂
    · refine Subtype.ext ?_
      change ((Subgroup.normalizerMonoidHom (H := B) ⟨n₃, hn₃N⟩) ⟨b₃, hb₃B⟩ : G) = b₁
      rw [hcoe₃, Subgroup.coe_mk]
      exact hn₃b₃
  exact ⟨t₁, s, c, ht₁X, hsX, hcX, ht₁, hs, hc⟩

end CFSG.RankThree.PartTwo.Sec21.FF81

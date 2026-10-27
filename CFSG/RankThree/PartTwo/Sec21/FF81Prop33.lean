module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G]

theorem conjBy_zpowers (g b : G) :
    conjBy g (Subgroup.zpowers b) = Subgroup.zpowers (g * b * g⁻¹) :=
  MonoidHom.map_zpowers _ _

theorem conjLines_eq [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}
    (hB : FF81Basis b L B b₁ b₂ b₃) :
    ConjLines B b = {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} := by
  have hbB : b ∈ B := by rw [hB.mono.2.1]; exact Subgroup.subset_closure (by simp)
  ext D
  refine ⟨fun hD => hB.fus D hD, ?_⟩
  rintro ⟨n, hn, rfl⟩
  refine ⟨?_, n, rfl⟩
  rw [conjBy_zpowers, Subgroup.zpowers_le]
  exact (Subgroup.mem_normalizer_iff.mp hn b).mp hbB

theorem ff81_3_3 :
    KF_Prop51 → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ : G),
      FF81Basis b L B b₁ b₂ b₃ → Odd (Nat.card (CenS B)) →
      (∃ n ∈ Nor B, n * b * n⁻¹ ∈ Subgroup.closure {b₁, b₂, b₃}) →
      CaseI b B b₁ b₂ b₃ ∨ CaseIIa b B b₁ b₂ b₃ ∨ CaseIIb b B b₁ b₂ b₃ ∨ CaseBad b B := by
  intro hP G _ _ b L B b₁ b₂ b₃ hB hodd hmeet
  have hset := conjLines_eq hB
  rcases hP G B b b₁ b₂ b₃ hB.mono hodd hB.stab hmeet with
    ⟨hex, -, hsub⟩ | ⟨hm, h, hc, hw⟩ | ⟨hm, h, hc, hw⟩ | ⟨h, hc⟩ | ⟨h, hc⟩
  · left
    refine ⟨hex, Set.Subset.antisymm (fun D hD => ?_) ?_⟩
    · obtain ⟨n, hn, rfl⟩ := hB.fus D hD
      exact hsub n hn _ rfl
    · obtain ⟨c, hcN, hc0, hc1, hc2, hc3⟩ := hex.1.2.2.2.2
      have hmem : ∀ n ∈ Nor B, Subgroup.zpowers (n * b * n⁻¹) ∈ ConjLines B b := fun n hn => by
        rw [hset, ← conjBy_zpowers]
        exact ⟨n, hn, rfl⟩
      intro D hD
      rcases hD with rfl | rfl | rfl | rfl
      · simpa using hmem 1 (Subgroup.one_mem _)
      · simpa [hc0] using hmem c hcN
      · have e : c * c * b * (c * c)⁻¹ = b₂ := by
          calc c * c * b * (c * c)⁻¹ = c * (c * b * c⁻¹) * c⁻¹ := by group
            _ = b₂ := by rw [hc0, hc1]
        have := hmem (c * c) (Subgroup.mul_mem _ hcN hcN)
        rwa [e] at this
      · have e : c * c * c * b * (c * c * c)⁻¹ = b₃ := by
          calc c * c * c * b * (c * c * c)⁻¹ = c * (c * (c * b * c⁻¹) * c⁻¹) * c⁻¹ := by group
            _ = b₃ := by rw [hc0, hc1, hc2]
        have := hmem (c * c * c) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hcN) hcN)
        rwa [e] at this
  · exact Or.inr (Or.inl ⟨hm, by rw [h]; norm_num, by rw [hset]; exact hc, hw⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hm, by rw [h]; norm_num, by rw [hset]; exact hc, hw⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hset]; exact hc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by rw [hset]; exact hc))))

end CFSG.RankThree.PartTwo.Sec21.FF81

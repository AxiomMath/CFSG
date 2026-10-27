module

public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Stmt5_3_3_factsAt (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T t m f → IsSec53Param t m f →
      (perfectCore (sec53M1 L) = L ∧ perfectCore (sec53M2 H) = oTwoUpper H ∧
        pCoreOf 2 (sec53M12 L H) = sec53S T L) ∧
      (∀ z ∈ centerOf L, z ≠ 1 → ∀ z' ∈ centerOf L, z' ≠ 1 → ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
      (∀ z ∈ centerOf (oTwoUpper H), z ≠ 1 → ∀ z' ∈ centerOf (oTwoUpper H), z' ≠ 1 →
        ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
      (t = .PSp → ∀ u ∈ sec53ZS T L, orderOf u = 2 → ∃ g ∈ B ⊔ D, g * u * g⁻¹ ∈ centerOf T)

theorem stmt5_3_3_facts_of_at (hL3 : Stmt5_3_3_factsAt .PSL 3)
    (hSp : Stmt5_3_3_factsAt .PSp 2) (hG2 : Stmt5_3_3_factsAt .G2 0)
    (h3D4 : Stmt5_3_3_factsAt .trialityD4 0) (h2F4 : Stmt5_3_3_factsAt .twistedF4 0)
    (hU4 : Stmt5_3_3_factsAt .PSU 4) (hU5 : Stmt5_3_3_factsAt .PSU 5) : Stmt5_3_3_facts := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  rcases hpar.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl, -⟩
  · exact hL3 G T M L V H B D L₂ n f hyp hty hpar
  · exact hSp G T M L V H B D L₂ n f hyp hty hpar
  · exact hG2 G T M L V H B D L₂ n f hyp hty hpar
  · exact h3D4 G T M L V H B D L₂ n f hyp hty hpar
  · exact h2F4 G T M L V H B D L₂ n f hyp hty hpar
  · exact hU4 G T M L V H B D L₂ n f hyp hty hpar
  · exact hU5 G T M L V H B D L₂ n f hyp hty hpar

end CFSG.Quasithin.H13

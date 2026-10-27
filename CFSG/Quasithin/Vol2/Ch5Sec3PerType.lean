module

public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Stmt5_3_2At (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T t m f → IsSec53Param t m f →
      ∃ (Y : Type) (_ : Group Y), LieModel Y t m 2 f ∧
        IsExtensionOfLieAmalgam Y (sec53M1 L) (sec53M2 H)

@[expose] def F431Rank2At (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G) (f : ℕ), IsSec53Param t m f → F431Hyps M₁ M₂ t m f →
      LieModel G t m 2 f

variable {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}

theorem stmt5_3_2_of_at (hL3 : Stmt5_3_2At .PSL 3) (hSp : Stmt5_3_2At .PSp 2)
    (hG2 : Stmt5_3_2At .G2 0) (h3D4 : Stmt5_3_2At .trialityD4 0)
    (h2F4 : Stmt5_3_2At .twistedF4 0) (hU4 : Stmt5_3_2At .PSU 4) (hU5 : Stmt5_3_2At .PSU 5) :
    Stmt5_3_2 := by
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

theorem f431Rank2_of_at (hL3 : F431Rank2At .PSL 3) (hSp : F431Rank2At .PSp 2)
    (hG2 : F431Rank2At .G2 0) (h3D4 : F431Rank2At .trialityD4 0)
    (h2F4 : F431Rank2At .twistedF4 0) (hU4 : F431Rank2At .PSU 4) (hU5 : F431Rank2At .PSU 5) :
    F431Rank2 := by
  intro G _ _ hG hnab M₁ M₂ t m f hpar hyps
  rcases hpar.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl, -⟩
  · exact hL3 G hG hnab M₁ M₂ f hpar hyps
  · exact hSp G hG hnab M₁ M₂ f hpar hyps
  · exact hG2 G hG hnab M₁ M₂ f hpar hyps
  · exact h3D4 G hG hnab M₁ M₂ f hpar hyps
  · exact h2F4 G hG hnab M₁ M₂ f hpar hyps
  · exact hU4 G hG hnab M₁ M₂ f hpar hyps
  · exact hU5 G hG hnab M₁ M₂ f hpar hyps

end CFSG.Quasithin.H13

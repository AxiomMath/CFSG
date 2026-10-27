module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77FromOne

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step77FromOneMovesStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    ∃ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t), ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∉ Z

@[expose] def Step77FromOneCommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    ∀ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t), ⁅y * t * y⁻¹, t⁆ ∈ Q

@[expose] def Step77FromOneNotCentreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    ∀ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t),
      (∃ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∉ Z) → y * t * y⁻¹ ∉ Z0

@[expose] def Step77FromOneMeetStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    ∀ y ∈ conjSubgroup g (LB M Q B ⊓ hc.CN t),
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup y (Vt M (LB M Q B) B Z t) ≠ Z

theorem step77FromOneCore_of_parts (hMoves : Step77FromOneMovesStatement)
    (hComm : Step77FromOneCommStatement) (hNot : Step77FromOneNotCentreStatement)
    (hMeet : Step77FromOneMeetStatement) : Step77FromOneCoreStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3
  by_cases hV : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z
  · obtain ⟨y, hy, hmov⟩ := hMoves G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV
    have hyM : y ∈ M := by
      have h1 : g⁻¹ * y * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy
      have h2 : g⁻¹ * y * g ∈ M := hc.LB_le_M h1.1
      have h3 := M.mul_mem (M.mul_mem hgM h2) (M.inv_mem hgM)
      simpa [mul_assoc] using h3
    refine ⟨y, hyM, y * t * y⁻¹, ?_, hComm G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3
      hV y hy, hNot G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV y hy hmov,
      hMeet G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV y hy⟩
    rw [mul_inv_cancel]
    exact Q.one_mem
  · exact ⟨g, hgM, s, hs1, hs2, hs3, hV⟩

end CFSG.RankThree.GF2n.Stroth80

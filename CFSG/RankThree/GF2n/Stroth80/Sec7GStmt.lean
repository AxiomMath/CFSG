module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly78
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1617
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndMain
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.Open.StatedDefs
public import Mathlib.RepresentationTheory.Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def SmithOmegaPlusEightStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (Y : Type) [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K Y] (ρ : Representation K (StatedOmega (StatedQuadPlus 4 K)) Y),
    (∀ A : AddSubgroup Y,
        (∀ (g : StatedOmega (StatedQuadPlus 4 K)) (y : Y), y ∈ A → ρ g y ∈ A) → A = ⊥ ∨ A = ⊤) →
    (∃ (g : StatedOmega (StatedQuadPlus 4 K)) (y : Y), ρ g y ≠ y) →
    ∀ e : Fin 4 ⊕ Fin 4 → K, e ≠ 0 → StatedQuadPlus 4 K e = 0 →
    ∀ W : Submodule K Y,
      (∀ (g : StatedOmega (StatedQuadPlus 4 K)),
        (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = e ∧
          (∀ x, StatedQuadPlus 4 K (x + e) - StatedQuadPlus 4 K x - StatedQuadPlus 4 K e = 0 →
            ∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x = c • e) ∧
          (∀ x, StatedQuadPlus 4 K
              ((((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) + e)
              - StatedQuadPlus 4 K (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x)
              - StatedQuadPlus 4 K e = 0)) →
        ∀ y ∈ W, ρ g y = y) →
      (∀ (g : StatedOmega (StatedQuadPlus 4 K)),
        (∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = c • e) →
        ∀ y ∈ W, ρ g y ∈ W) →
      W = ⊥ ∨
        ∀ y : Y, (∀ (g : StatedOmega (StatedQuadPlus 4 K)),
          (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = e ∧
            (∀ x, StatedQuadPlus 4 K (x + e) - StatedQuadPlus 4 K x - StatedQuadPlus 4 K e = 0 →
              ∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x = c • e) ∧
            (∀ x, StatedQuadPlus 4 K
                ((((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) + e)
                - StatedQuadPlus 4 K (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x)
                - StatedQuadPlus 4 K e = 0)) → ρ g y = y) → y ∈ W

@[expose] def Step76NoWildSixStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → ¬ OmegaPlusNat hc t 3

@[expose] def Step76NoWildSixCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 3 →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q →
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

theorem step76NoWildSix_of (h71 : Stroth71Statement) (hcore : Step76NoWildSixCoreStatement) :
    Step76NoWildSixStatement := by
  intro G _ _ M Q Z B hc n t hs hno h3
  rcases h71 G M Q Z B hc n t hs with h | ⟨-, ⟨x, hxc, hxt, w, hw, hxw⟩, -⟩
  · exact hno h
  · exact hxw (hcore G M Q Z B hc n t hs hno h3 x hxc hxt w hw)

@[expose] def Step76EEightStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0

theorem step76E_of_cases (h71 : Stroth71Statement)
    (h6 : Step76NoWildSixStatement) (h8 : Step76EEightStatement) : Step76EStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0
  rcases h71 G M Q Z B hc n t hs with h | ⟨htype, -, -⟩
  · exact absurd h hno
  rcases htype with h2 | h3 | h4
  · exact absurd h2 hom
  · exact absurd h3 (h6 G M Q Z B hc n t hs hno)
  · exact h8 G M Q Z B hc n t hs hno h4 Z0 hZ0

@[expose] def Step77FromOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z) →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 → False

theorem step77Two_of_one (h1 : Step77OneStatement) (hF : Step77FromOneStatement) :
    Step77TwoStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hg s h1' h2' h3'
  exact (hF G M Q Z B hc n t hs hno hom Z0 hZ0
    (fun g' hg' s' a b c => h1 G M Q Z B hc n t hs hno hom Z0 hZ0 g' hg' s' a b c)
    g hg s h1' h2' h3').elim

theorem step77End_of_one (h1 : Step77OneStatement) (hF : Step77FromOneStatement) :
    Step77EndStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 _ _ g hg s h1' h2' h3' _ _
  exact (hF G M Q Z B hc n t hs hno hom Z0 hZ0
    (fun g' hg' s' a b c => h1 G M Q Z B hc n t hs hno hom Z0 hZ0 g' hg' s' a b c)
    g hg s h1' h2' h3').elim

@[expose] def Sec7WVNe6Om4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaMinusNat hc t 2 → n ≠ 6

theorem sec7WVGeOm4_of (hW : Sec7WVOrderStatement) (h6 : Sec7WVNe6Om4Statement) :
    Sec7WVGeOm4Statement := by
  intro G _ _ M Q Z B hc n t hs hom
  obtain ⟨y, hy, hn⟩ := (hW G M Q Z B hc n t hs 2 le_rfl).1 hom
  have h6' := h6 G M Q Z B hc n t hs hom
  norm_num at hn
  omega

end CFSG.RankThree.GF2n.Stroth80

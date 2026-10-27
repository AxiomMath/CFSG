module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Frame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

structure s16c4v1_Std (D : Data G) : Prop where
  dataExt : DataExt D
  sigmaStd : UC6S846.SigmaStd D
  h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1
  r61 : UC6.R6_1 D
  r126 : R126 D
  w3_111 : W3Thm111 G
  r129 : R129_1 D
  r1217 : R1217 D
  rank : 3 < CFSG.Open.evenRank G

structure s16c4v1_Sit (D : Data G) (V L : Subgroup G) (hV : IsElemAbelian 2 V) where
  sect : Sect16 D ⊥ V L hV
  case4 : Case167_4 D ⊥ V hV L
  ne_bot : v1Sub D.M ⊥ V hV L ≠ ⊥
  F : UFrame (v1Sub D.M ⊥ V hV L) V hV L

variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

open Classical in
@[expose] noncomputable def s16c4v1_vec (S : s16c4v1_Sit D V L hV) (v : G) : Fin 4 → S.F.K :=
  if hv : v ∈ V then
    S.F.vec (mkTil (v1Sub D.M ⊥ V hV L) V hV (IntMod.mk hV ⟨v, hv⟩))
  else 0

@[expose] def s16c4v1_Induces (S : s16c4v1_Sit D V L hV) (m : G) (γ : ↥(SUid S.F.σ 4)) : Prop :=
  ∀ v ∈ V, s16c4v1_vec S (m * v * m⁻¹) = γ • s16c4v1_vec S v

@[expose] def s16c4v1_Scal (S : s16c4v1_Sit D V L hV) (m : G) (c : S.F.K) : Prop :=
  ∀ v ∈ V, s16c4v1_vec S (m * v * m⁻¹) = c • s16c4v1_vec S v

@[expose] def s16c4v1_ScalarOf (S : s16c4v1_Sit D V L hV) (z : G) (ω : S.F.K) : Prop :=
  z ∈ D.M ∧ ω ≠ 1 ∧ s16c4v1_Scal S z ω

@[expose] def s16c4v1_ActsLike (V : Subgroup G) (a l : G) : Prop :=
  ∀ v ∈ V, a * v * a⁻¹ = l * v * l⁻¹

@[expose] def s16c4v1_Lin (S : s16c4v1_Sit D V L hV) (m : G) : Prop :=
  ∃ (c : S.F.K) (γ : ↥(SUid S.F.σ 4)), c ≠ 0 ∧
    ∀ v ∈ V, s16c4v1_vec S (m * v * m⁻¹) = c • (γ • s16c4v1_vec S v)

@[expose] def s16c4v1_Bad (D : Data G) (v : G) : Prop :=
  ¬ Subgroup.centralizer ({v} : Set G) ≤ D.M

@[expose] noncomputable def s16c4v1_r1 (V : Subgroup G) (g : G) : ℕ :=
  CFSG.Quasithin.E3.mQuot V (Subgroup.centralizer (conjSubgroup V g : Set G))

@[expose] noncomputable def s16c4v1_r2 (V : Subgroup G) (g : G) : ℕ :=
  CFSG.Quasithin.E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G))

@[expose] def s16c4v1_Cex (D : Data G) (V : Subgroup G) (g : G) : Prop :=
  conjSubgroup V g ≤ D.M ∧ ⁅V, conjSubgroup V g⁆ ≠ ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

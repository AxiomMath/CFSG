module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.W18PackG
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)
open W183K3

@[expose] def Br3MasterOne : Prop :=
  ∀ (_rows : Br3Rows) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Y T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
    {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ},
    Br2Common Y Γ VA T 𝒢 Zs m i₀ δ → Br3OneComp Y T L →
      (IsAlt (↥L ⧸ Subgroup.center ↥L) 6 ∨ IsL3 (↥L ⧸ Subgroup.center ↥L) 2) →
      Γ.Nonempty → (∀ D ∈ Γ, 2 ≤ mRank D) → False

@[expose] def Br3MasterTwo : Prop :=
  ∀ (_rows : Br3Rows) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
    {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V},
    Br2Common Y Γ VA T 𝒢 Zs m i₀ δ → Br3TwoComp Y T L₁ L₂ →
      (IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6 ∨ IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2) →
      Nat.card ↥(Subgroup.center ↥L₁) = 3 →
      (∃ τ ∈ T, ActsOnDynkinMod (quasiCentre L₁) L₁ τ) →
      Γ.Nonempty → (∀ D ∈ Γ, 2 ≤ mRank D) → Br2ED Γ VA m δ ED → False

@[expose] def Br3CoverOne : Prop :=
  ∀ (_rows : Br3Rows) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Y T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ},
    Assumption131 Y Γ VA i → QuasiCore Y L (quasiCentre L) →
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 p 1 ∨
        LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 p 1)) →
      (∃ A ∈ Γ, 4 ≤ Nat.card ↥A) → False

@[expose] def Br3CoverTwo : Prop :=
  ∀ (_rows : Br3Rows) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
    {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
    {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ},
    Br2Common Y Γ VA T 𝒢 Zs m i₀ δ → Br3TwoComp Y T L₁ L₂ →
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ (LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 3 p 1 ∨
        LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSU 3 p 1)) →
      Γ.Nonempty → (∀ D ∈ Γ, 2 ≤ mRank D) → False

structure Br3Leaves : Prop where
  one : Br3MasterOne
  two : Br3MasterTwo
  coverOne : Br3CoverOne
  coverTwo : Br3CoverTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def Tail1812FourFreeKStarBig (G : Type) [Group G] [Finite G] : Prop :=
  W3Thm162Gt2 G → W3Thm172Weak G → Asch5_4 → Asch5_11AS → Asch5_12 → Asch5_13AS →
    ∀ {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}, MinCex183 D V₀ V H i →
      ¬ Concl182 D V₀ V H i →
      ¬ kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G) →
      (∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g')) →
      ∀ {g : G}, vInH V H g ≤ D.T → ¬ vInH V H g ≤ kerMV V H →
        E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i →
        3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) → False

end CFSG.LocalAnalysis.WeakClosure81

end

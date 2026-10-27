module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2Res
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

inductive Q2RowKind where
  | linear
  | symplectic
  | orthogonalPlus
  | orthogonalMinus
  | fieldTwo
  | e6Three
  | e7Seven
  | e8Three
  deriving DecidableEq

instance : Fintype Q2RowKind where
  elems :=
    {.linear, .symplectic, .orthogonalPlus, .orthogonalMinus, .fieldTwo, .e6Three, .e7Seven,
      .e8Three}
  complete := by intro k; cases k <;> simp

@[expose] def q2RowFits (kind : Q2RowKind) (p d Q : ℕ) (lab : LargeEvenLabel) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ∣ d ∧ p ∣ Q - 1 ∧
    match kind with
    | .linear => lab.tag = .A ∧ lab.rank = d ∧ Q = 2 ^ lab.n
    | .symplectic => (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = d ∧ Q = 2 ^ lab.n
    | .orthogonalPlus => lab.tag = .D ∧ lab.rank = d ∧ Q = 2 ^ lab.n
    | .orthogonalMinus => lab.tag = .twD ∧ lab.rank = d + 1 ∧ Q = 2 ^ lab.n
    | .fieldTwo =>
        lab.tag = .A ∧ lab.n = 1 ∧ (lab.rank = 2 * d - 1 ∨ lab.rank = 2 * d) ∧
          p = 3 ∧ Q = 4
    | .e6Three => lab.tag = .E6 ∧ p = 3 ∧ d = 6 ∧ Q = 2 ^ lab.n
    | .e7Seven => lab.tag = .E7 ∧ p = 7 ∧ d = 7 ∧ Q = 2 ^ lab.n
    | .e8Three => lab.tag = .E8 ∧ p = 3 ∧ d = 9 ∧ Q = 2 ^ lab.n

theorem q2RowFits_orthogonalPlus_parameters {p d Q : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hrow : q2RowFits .orthogonalPlus p d Q lab) :
    lab.tag = .D ∧ lab.rank = d ∧ 3 ≤ d ∧ 2 ≤ lab.n ∧ Q = 2 ^ lab.n := by
  obtain ⟨hp, hp2, hpd, hpQ, htag, hrank, hQ⟩ := hrow
  have hallowed : 1 ≤ lab.n ∧ 3 ≤ lab.rank := by
    simpa only [LargeEvenInLambda2, htag] using hlab
  have hn : 2 ≤ lab.n := by
    by_contra hn
    have hn1 : lab.n = 1 := by omega
    have hQ2 : Q = 2 := by simpa only [hn1, pow_one] using hQ
    have hp1 : p ∣ 1 := by simpa only [hQ2, Nat.reduceSub] using hpQ
    exact hp.not_dvd_one hp1
  exact ⟨htag, hrank, hrank ▸ hallowed.2, hn, hQ⟩

theorem q2RowFits_orthogonalPlus_three {p Q : ℕ} {lab : LargeEvenLabel}
    (hrow : q2RowFits .orthogonalPlus p 3 Q lab) : p = 3 := by
  have hp : p.Prime := hrow.1
  have hp2 : p ≠ 2 := hrow.2.1
  have hple : p ≤ 3 := Nat.le_of_dvd (by decide) hrow.2.2.1
  have hpge : 2 ≤ p := hp.two_le
  omega

theorem q2RowFits_orthogonalPlus_four_impossible {p Q : ℕ} {lab : LargeEvenLabel}
    (hrow : q2RowFits .orthogonalPlus p 4 Q lab) : False := by
  have hp : p.Prime := hrow.1
  have hp2 : p ≠ 2 := hrow.2.1
  have hpd : p ∣ 2 ^ 2 := by simpa using hrow.2.2.1
  have hple : p ≤ 2 := Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_pow hpd)
  exact hp2 (Nat.le_antisymm hple hp.two_le)

@[expose] def Q2ResidualCensusInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
        (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        p ∣ d → p ∣ Nat.card K - 1 →
        ∃ kind : Q2RowKind,
          GGInnerDiagOnLab (fun p lab => q2RowFits kind p d (Nat.card K) lab) p Bs L

@[expose] def Q2RowSolverInput (kind : Q2RowKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
        (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        p ∣ d → p ∣ Nat.card K - 1 →
        GGInnerDiagOnLab (fun p lab => q2RowFits kind p d (Nat.card K) lab) p Bs L →
        IsMulCommutative
          ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K))

theorem ggBstarAbelianPreimageJLinResInput_of_census_and_rows (hc : Q2ResidualCensusInput)
    (hs : ∀ kind, Q2RowSolverInput kind) : GGBstarAbelianPreimageJLinResInput := by
  intro G instG instFin p B Bs x L D J hcfg hInner hN d K instK instFinK θ hpd hpq
  obtain ⟨kind, hkind⟩ := hc G p B Bs x L D J hcfg hInner hN d K θ hpd hpq
  exact hs kind G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hkind

@[expose] def GGBstarAbelianPreimageJLinResNotOrthogonalPlusInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
      ∀ (hN : Bs ≤ Subgroup.normalizer (J : Set G)) (d : ℕ) (K : Type) [Field K] [Finite K]
        (θ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        p ∣ d → p ∣ Nat.card K - 1 →
        ¬ GGInnerDiagOnLab (fun p lab => q2RowFits .orthogonalPlus p d (Nat.card K) lab)
          p Bs L →
        IsMulCommutative
          ((((ggBsAut hN).range).map (kgInducedAut θ)).comap (TableB.linConjAut (Fin d) K))

theorem ggBstarAbelianPreimageJLinResInput_of_orthogonalPlus_and_rest
    (hplus : Q2RowSolverInput .orthogonalPlus)
    (hrest : GGBstarAbelianPreimageJLinResNotOrthogonalPlusInput) :
    GGBstarAbelianPreimageJLinResInput := by
  classical
  intro G instG instFin p B Bs x L D J hcfg hInner hN d K instK instFinK θ hpd hpq
  by_cases hmark : GGInnerDiagOnLab
      (fun p lab => q2RowFits .orthogonalPlus p d (Nat.card K) lab) p Bs L
  · exact hplus G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hmark
  · exact hrest G p B Bs x L D J hcfg hInner hN d K θ hpd hpq hmark

theorem ggBstarAbelianPreimageJLinInput_of_orthogonalPlus_and_rest
    (hplus : Q2RowSolverInput .orthogonalPlus)
    (hrest : GGBstarAbelianPreimageJLinResNotOrthogonalPlusInput) :
    GGBstarAbelianPreimageJLinInput :=
  ggBstarAbelianPreimageJLinInput_of_res
    (ggBstarAbelianPreimageJLinResInput_of_orthogonalPlus_and_rest hplus hrest)

theorem q2RowKind_card : Fintype.card Q2RowKind = 8 := by decide

end CFSG.StandardType

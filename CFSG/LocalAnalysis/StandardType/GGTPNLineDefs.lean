module

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrTablePNbrInputI1On (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    ∀ labJ labK : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labK →
      R p (Nat.card Bs) labJ labK →
      GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labK (K ⧸ Subgroup.center K) →
      ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labK' ∧
        GGTablePRow p labJ' labK' ∧
        GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)

@[expose] def GGRegimeLine : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop :=
  fun p n labJ _ => p = 3 ∧ n ≤ 3 ^ 5 ∧ ∃ T : GGResLineJType, ggResLineJLabel T labJ

theorem ggResLineJLabel_of_iso {T : GGResLineJType} {lab lab' : LargeEvenLabel}
    (h : ggResLineJLabel T lab) (hiso : GGLabelIso lab lab') : ggResLineJLabel T lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only [GGLabelIso, LargeEvenLabel.mk.injEq] at hiso
  cases T <;> simp only [ggResLineJLabel] at h ⊢ <;>
    rcases hiso with ⟨rfl, rfl, rfl⟩ | ⟨rfl | rfl, rfl | rfl, rfl, rfl⟩ |
      ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ |
      ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ |
      ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩
  all_goals first | exact h | simp_all

theorem ggResLineJLabel_of_iso_symm {T : GGResLineJType} {lab lab' : LargeEvenLabel}
    (h : ggResLineJLabel T lab') (hiso : GGLabelIso lab lab') : ggResLineJLabel T lab := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only [GGLabelIso, LargeEvenLabel.mk.injEq] at hiso
  cases T <;> simp only [ggResLineJLabel] at h ⊢ <;>
    rcases hiso with ⟨rfl, rfl, rfl⟩ | ⟨rfl | rfl, rfl | rfl, rfl, rfl⟩ |
      ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ |
      ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ |
      ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩
  all_goals first | exact h | simp_all

theorem three_not_dvd_both_pow_two {n : ℕ} (h1 : 3 ∣ 2 ^ n - 1) (h2 : 3 ∣ 2 ^ n + 1) : False := by
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h := Nat.dvd_sub h2 h1
  have e : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
  rw [e] at h
  omega

theorem ggResLineJLabel_not_pRankOne {T : GGResLineJType} {lab : LargeEvenLabel}
    (h : ggResLineJLabel T lab) : ¬ GGTPNPRankOne 3 lab := by
  obtain ⟨t, r, n⟩ := lab
  intro hrk
  unfold GGTPNPRankOne at hrk
  rcases hrk with ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr, h3⟩ | ⟨ht, hr, h3⟩ <;>
    dsimp only at ht hr <;> subst ht hr <;> cases T <;>
    simp [ggResLineJLabel] at h
  all_goals first
    | exact three_not_dvd_both_pow_two h h3
    | exact three_not_dvd_both_pow_two h3 h

theorem ggResLineJLabel_not_rankOne {T : GGResLineJType} {lab : LargeEvenLabel}
    (h : ggResLineJLabel T lab) : ¬ GGTPNRankOne lab := by
  intro hrk
  apply ggResLineJLabel_not_pRankOne h
  rcases hrk with hrk | hrk
  · exact Or.inl hrk
  · exact Or.inr (Or.inl hrk)

theorem ggRegimeLine_not_pRankOne {p n : ℕ} {labJ labX : LargeEvenLabel}
    (h : GGRegimeLine p n labJ labX) (lab : LargeEvenLabel) (hiso : GGLabelIso lab labJ) :
    ¬ GGTPNPRankOne p lab := by
  obtain ⟨rfl, -, T, hT⟩ := h
  exact ggResLineJLabel_not_pRankOne (ggResLineJLabel_of_iso_symm hT hiso)

theorem ggTPNRankJ_of_line (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {T : GGResLineJType} {labJ : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hT : ggResLineJLabel T labJ) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRankJ J := by
  intro lab hlab hhas
  exact ggResLineJLabel_not_rankOne
    (ggResLineJLabel_of_iso hT (hrig labJ lab (↥J ⧸ Subgroup.center ↥J) hΛ hlab hhJ hhas))

@[expose] def GGLineExcOneThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeLine p n labJ labX ∧ GGKacExcPair labX p ∧ GGKacCentred labX p ∧ labX.n = 1 ∧ p = 3

@[expose] def GGLineE6ThreeRK : Prop :=
  GGTablePKnownRK fun p n labJ labX =>
    GGRegimeLine p n labJ labX ∧ (labX.tag = .E6 ∨ labX.tag = .twE6) ∧ p = 3 ∧
      GGKacExcPair labX p

end CFSG.StandardType

end

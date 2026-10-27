module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTypeAClRARK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ GGKacRA labX p

@[expose] def GGTypeAExcRERK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeTypeA p n labJ labX ∧ GGKacRE labX p

theorem ggKacRE_of_excPair_of_not_generic {lab : LargeEvenLabel} {p : ℕ}
    (h : GGKacExcPair lab p) (hg : ¬ GGKacGeneric lab p) : GGKacRE lab p := by
  obtain ⟨hp, hp2, hdiv, htag⟩ := h
  refine ⟨hp, hp2, hdiv, ?_⟩
  by_contra hn
  apply hg
  refine ⟨hp, hp2, hdiv, htag, ?_, ?_, ?_⟩
  · rintro ⟨hF, hp3⟩
    exact hn (Or.inl ⟨hF, hp3⟩)
  · rintro ⟨hE, hp35⟩
    exact hn (Or.inr (Or.inl ⟨hE, hp35⟩))
  · rintro ⟨hE, hp357⟩
    exact hn (Or.inr (Or.inr ⟨hE, hp357⟩))

theorem ggTypeA_regime_not_rankOne {p n : ℕ} {labJ labX : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : GGRegimeTypeA p n labJ labX) (lab : LargeEvenLabel)
    (hiso : GGLabelIso lab labJ) : ¬ GGTPNPRankOne p lab := by
  obtain ⟨t, r, m⟩ := labJ
  obtain ⟨ht, hr, hm, hpd⟩ := h
  simp only at ht hr hm hpd
  subst ht
  intro hrk
  simp only [GGLabelIso] at hiso
  simp only [GGTPNPRankOne] at hrk
  rcases hiso with rfl | ⟨-, hB, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h2, -⟩
  · rcases hrk with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨h1, -⟩
    · simp only at h2; omega
    · exact absurd h1 (by simp)
    · simp only at h3
      have h2d : p ∣ 2 := by
        have := Nat.dvd_sub h3 hpd
        have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        have e : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by omega
        rwa [e] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2d)
    · exact absurd h1 (by simp)
  · simp at hB
  · have ht : lab.tag = .D := congrArg LargeEvenLabel.tag h1
    rcases hrk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [ht] at h <;> cases h
  · exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)
  · have := congrArg LargeEvenLabel.rank h2
    simp only at this
    omega
  · exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)

theorem ggTPNRankJ_of_typeA (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {p n : ℕ} {labJ labX : LargeEvenLabel} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΛ : LargeEvenInLambda2 labJ) (hreg : GGRegimeTypeA p n labJ labX)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : GGTPNRankJ J := by
  intro lab hlab hhas hrk
  have hiso : GGLabelIso lab labJ := hrig lab labJ (↥J ⧸ Subgroup.center ↥J) hlab hΛ hhas hhJ
  refine ggTypeA_regime_not_rankOne hp hp2 hreg lab hiso ?_
  rcases hrk with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType

end

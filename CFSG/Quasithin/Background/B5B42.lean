module

public import CFSG.Quasithin.Background.B5Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section B42Cases

variable {V : Type} [CommGroup V] [Finite V]

theorem not_isPerfect_perm (n : ℕ) (hn : 5 ≤ n) : ¬ Group.IsPerfect (Equiv.Perm (Fin n)) := by
  intro hp
  have h1 : commutator (Equiv.Perm (Fin n)) = alternatingGroup (Fin n) :=
    alternatingGroup.commutator_perm_eq (by simpa using hn)
  have h2 : commutator (Equiv.Perm (Fin n)) = ⊤ := hp.1
  rw [h1] at h2
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [ha, hb] at this
  have hmem : Equiv.swap a b ∈ alternatingGroup (Fin n) := by
    rw [h2]; trivial
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab] at hmem
  exact absurd hmem (by decide)


@[expose] def B42QData (G L : Subgroup (MulAut V)) : Prop :=
  qOf G = ((1 : ℚ) : WithTop ℚ) ∨ (∃ n, BinaryNaturalSL L (⊤ : Subgroup V) ⊥ 3 n) ∨
    (∃ n, BinaryNaturalSp4 L (⊤ : Subgroup V) ⊥ n) ∨ BinaryNaturalSL L (⊤ : Subgroup V) ⊥ 4 1 ∨
    BinaryNaturalSL L (⊤ : Subgroup V) ⊥ 5 1

@[expose] def B42BetaData (G L : Subgroup (MulAut V)) : Prop :=
  G = ffJ G ∧ L = ⁅G, G⁆ ∧
    ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥G ≃* Equiv.Perm (Fin n))) ∨
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
        Nonempty (↥G ≃* ↥(CFSG.Open.quasithinG2 K))) ∧
    (BinaryNaturalSp4 G (⊤ : Subgroup V) ⊥ 1 ∨ G2Natural G (⊤ : Subgroup V) ⊥ 1 ∨
      (∃ n, (n = 5 ∨ n = 7) ∧ SymmetricNatural G (⊤ : Subgroup V) ⊥ n) ∨
      (SLExteriorTwo L (⊤ : Subgroup V) ⊥ 4 ∧ Nonempty (↥G ≃* Equiv.Perm (Fin 8))))

omit [Finite V] in
theorem one_le_of_binaryNaturalSp4 {H : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : BinaryNaturalSp4 H U Z n) : 1 ≤ n := by
  obtain ⟨K, hK, hf, hc, -⟩ := h
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hc] at h1
  by_contra h0
  have : n = 0 := by omega
  rw [this] at h1
  simp at h1

omit [Finite V] in
theorem one_le_of_g2Natural {H : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : G2Natural H U Z n) : 1 ≤ n := by
  obtain ⟨K, hK, hf, hc, -⟩ := h
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hc] at h1
  by_contra h0
  have : n = 0 := by omega
  rw [this] at h1
  simp at h1

theorem b42_cases (hIdent : AsB42Ident) (hV : ∀ v : V, v ^ 2 = 1) {G L A : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hA : IsFFStarOffender G A) (h : B42Conclusion G L A) :
    (ffJ G = L ∧ B42ModulePair L (⊤ : Subgroup V) ⊥ ∧ B42QData G L) ∨
      (ffJ G ≠ L ∧ B42BetaData G L) := by
  by_cases hJL : ffJ G = L
  · left
    refine ⟨hJL, ?_⟩
    have h5 : ¬ B42Case5 G A := fun h5 =>
      (hIdent V hV G L hHyp A hA (Or.inl h5)).1 hJL
    rcases h with ⟨hJ, ⟨n, hn⟩, -, hq⟩ | ⟨hJ, ⟨n, hn⟩, hq⟩ | ⟨⟨n, hn, -⟩, hq⟩ | ⟨⟨n, hn, -, -⟩, hq⟩ | h5' |
      ⟨hJ, hn, -, hq, -⟩ | ⟨-, hJ, hn, -, hq, -⟩ |
      ⟨hJ, -, hq, ⟨K, hK, hf, Γ₀, hc, hdet, hhat, hcen, π, hπ, -⟩⟩ |
      ⟨hJ, n, hn4, hn, hq⟩ | ⟨hn, hrest⟩ | ⟨-, hJ, -, hq, π, hπ, -⟩
    · have h2 : ∃ n, BinaryNaturalSL L (⊤ : Subgroup V) ⊥ 2 n := ⟨n, hn⟩
      unfold B42ModulePair B42QData
      tauto
    · have h2 : ∃ n, BinaryNaturalSL L (⊤ : Subgroup V) ⊥ 3 n := ⟨n, hn⟩
      unfold B42ModulePair B42QData
      tauto
    · rw [hJL] at hn
      have h2 : ∃ n, BinaryNaturalSp4 L (⊤ : Subgroup V) ⊥ n := ⟨n, hn⟩
      unfold B42ModulePair B42QData
      tauto
    · rw [hJL] at hn
      have h2 : ∃ n, G2Natural L (⊤ : Subgroup V) ⊥ n := ⟨n, hn⟩
      unfold B42ModulePair B42QData
      tauto
    · exact absurd h5' h5
    · unfold B42ModulePair B42QData
      tauto
    · unfold B42ModulePair B42QData
      tauto
    · have h2 : TripleA6Six L (⊤ : Subgroup V) ⊥ := ⟨K, hK, hf, Γ₀, hc, hdet, hhat, hcen, ⟨π, hπ⟩⟩
      unfold B42ModulePair B42QData
      tauto
    · rcases hn4 with rfl | rfl
      · unfold B42ModulePair B42QData
        tauto
      · unfold B42ModulePair B42QData
        tauto
    · rcases hrest with ⟨-, hJ, -, hq⟩ | ⟨hGJ, ⟨e⟩, -⟩
      · unfold B42ModulePair B42QData
        tauto
      · exfalso
        have hperf : Group.IsPerfect ↥G := by
          have hq := hHyp.2.2.1
          have h1 : Group.IsPerfect ↥(ffJ G) := by rw [hJL]; exact hq.1
          rw [← hGJ] at h1
          exact h1
        have := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
        exact not_isPerfect_perm 8 (by norm_num) this
    · have h2 : SLExteriorTwo L (⊤ : Subgroup V) ⊥ 5 := ⟨π, hπ⟩
      unfold B42ModulePair B42QData
      tauto
  · right
    refine ⟨hJL, ?_⟩
    obtain ⟨-, hGJ, hLG, hstruct⟩ := hIdent V hV G L hHyp A hA (Or.inr hJL)
    refine ⟨hGJ, hLG, hstruct, ?_⟩
    rcases h with ⟨hJ, -⟩ | ⟨hJ, -⟩ | ⟨⟨n, hn, hn1⟩, -⟩ | ⟨⟨n, hn, -, hn1⟩, -⟩ | ⟨⟨n, hn5, π, hπ, -⟩, -⟩ |
      ⟨hJ, -⟩ | ⟨-, hJ, -⟩ | ⟨hJ, -⟩ | ⟨hJ, -⟩ | ⟨hn, hrest⟩ | ⟨-, hJ, -⟩
    · exact absurd hJ hJL
    · exact absurd hJ hJL
    · have h1 : n = 1 := by
        by_contra hne
        exact hJL (hn1 (by have := one_le_of_binaryNaturalSp4 hn; omega))
      subst h1
      rw [← hGJ] at hn
      exact Or.inl hn
    · have h1 : n = 1 := by
        by_contra hne
        exact hJL (hn1 (by have := one_le_of_g2Natural hn; omega))
      subst h1
      rw [← hGJ] at hn
      exact Or.inr (Or.inl hn)
    · have hS : SymmetricNatural (ffJ G) (⊤ : Subgroup V) ⊥ n := ⟨π, hπ⟩
      rw [← hGJ] at hS
      exact Or.inr (Or.inr (Or.inl ⟨n, hn5, hS⟩))
    · exact absurd hJ hJL
    · exact absurd hJ hJL
    · exact absurd hJ hJL
    · exact absurd hJ hJL
    · rcases hrest with ⟨-, hJ, -⟩ | ⟨-, e, -⟩
      · exact absurd hJ hJL
      · exact Or.inr (Or.inr (Or.inr ⟨hn, e⟩))
    · exact absurd hJ hJL

end B42Cases

end B5

end CFSG.Quasithin

module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def IsRankOneIn {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (g : GL ι F) : Prop :=
  Matrix.rank ((g : Matrix ι ι F) - 1) = 1

@[expose] def IsOrthReflection (X : Type) [Group X] (m n : ℕ) (s : X) : Prop :=
  (∃ k : ℕ, 2 ≤ k ∧ m = 2 * k ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧ ∃ e : (X ⧸ center X) ≃* ↥(CFSG.PGLModel.orthogonalPlus k F),
        haveI := Fintype.ofFinite F;
          IsRankOneIn ((e (QuotientGroup.mk s) : GL (Fin k ⊕ Fin k) F))) ∨
    (∃ k : ℕ, 1 ≤ k ∧ m = 2 * k + 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧ ∃ b c : F, (∀ t : F, t ^ 2 + b * t + c ≠ 0) ∧
        ∃ e : (X ⧸ center X) ≃* ↥(CFSG.PGLModel.orthogonalMinus k F b c),
          haveI := Fintype.ofFinite F;
            IsRankOneIn ((e (QuotientGroup.mk s) : GL (Fin k ⊕ Fin k ⊕ Fin 2) F)))

@[expose] def IsWreathTransposition (X : Type) [Group X] (n m : ℕ) (s : X) : Prop :=
  1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ e : (X ⧸ center X) ≃* WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m,
      ∃ i j : Fin m, i ≠ j ∧
        IsConj (e (QuotientGroup.mk s)) (SemidirectProduct.inr (Equiv.swap i j))

@[expose] def IsSymTransposition (X : Type) [Group X] (n : ℕ) (s : X) : Prop :=
  ∃ e : (X ⧸ fusionOddCore X) ≃* Equiv.Perm (Fin n), (e (QuotientGroup.mk s)).IsSwap

@[expose] def IsOrth63Reflection (X : Type) [Group X] (s : X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧
    ∃ b c : F, (∀ t : F, t ^ 2 + b * t + c ≠ 0) ∧
      ∃ N : Subgroup (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F),
        CFSG.PGLModel.projOmegaMinus 2 F b c ≤ N ∧
          N ≤ (CFSG.PGLModel.orthogonalMinus 2 F b c).map Matrix.ProjGenLinGroup.mk ∧
          ∃ (φ : X →* ↥N), Function.Surjective φ ∧ Nat.card φ.ker = 3 ∧
            φ.ker ≤ center X ∧ ∃ r ∈ CFSG.PGLModel.orthogonalMinus 2 F b c,
              haveI := Fintype.ofFinite F;
              IsRankOneIn r ∧
                ((φ s : ↥N) : Matrix.ProjGenLinGroup _ F) = Matrix.ProjGenLinGroup.mk r

theorem isOrthGp_of_isOrthReflection {X : Type} [Group X] {m n : ℕ} {s : X}
    (h : IsOrthReflection X m n s) : IsOrthGp (X ⧸ center X) m n := by
  rcases h with ⟨k, hk, hm, F, hF, hFin, hcard, e, -⟩ |
    ⟨k, hk, hm, F, hF, hFin, hcard, b, c, hbc, e, -⟩
  · exact Or.inl ⟨k, hk, hm, F, hF, hFin, hcard, ⟨e⟩⟩
  · exact Or.inr ⟨k, hk, hm, F, hF, hFin, hcard, b, c, hbc, ⟨e⟩⟩

theorem isL2WrSymGp_of_isWreathTransposition {X : Type} [Group X] {n m : ℕ} {s : X}
    (h : IsWreathTransposition X n m s) : IsL2WrSymGp (X ⧸ center X) n m := by
  obtain ⟨-, F, hF, hFin, hcard, e, -⟩ := h
  exact ⟨F, hF, hFin, hcard, ⟨e⟩⟩

theorem isSymGp_of_isSymTransposition {X : Type} [Group X] {n : ℕ} {s : X}
    (h : IsSymTransposition X n s) : IsSymGp (X ⧸ fusionOddCore X) n := by
  obtain ⟨e, -⟩ := h
  exact ⟨e⟩

theorem isThreeCoverOrth6Minus_of_isOrth63Reflection {X : Type} [Group X] {s : X}
    (h : IsOrth63Reflection X s) : IsThreeCoverOrth6Minus X := by
  obtain ⟨F, hF, hFin, hcard, b, c, hbc, N, hN1, hN2, φ, hφ, hker, hcen, -⟩ := h
  exact ⟨↥N, inferInstance, φ, hφ, hker, hcen, F, hF, hFin, hcard, b, c, hbc, N, hN1, hN2,
    ⟨MulEquiv.refl _⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

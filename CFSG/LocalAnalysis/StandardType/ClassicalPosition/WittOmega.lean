module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarElementary

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal

theorem exists_mem_omegaGroup_family_apply_eq {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) {ι : Type} [Fintype ι] (w w' : ι → V)
    (hw : LinearIndependent K w) (hw' : LinearIndependent K w') (hQ : ∀ i, Q (w' i) = Q (w i))
    (hpol : ∀ i k, QuadraticMap.polar Q (w' i) (w' k) = QuadraticMap.polar Q (w i) (w k))
    (a : V) (ha : Q a ≠ 0) (haw : ∀ i, QuadraticMap.polar Q a (w' i) = 0) :
    ∃ g ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd, ∀ i, g (w i) = w' i := by
  obtain ⟨g, hgO, hg⟩ := CFSG.StandardType.TableBOrth.exists_orth_apply_eq hnd w w' hw hw' hQ hpol
  set D := CFSG.RankThree.OrthogonalInvolutions.dicksonHom Q hnd
  have hker : ∀ x : TauCeti.QuadraticMap.orthogonalGroup Q, D x = 1 →
      (x : V ≃ₗ[K] V) ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hnd := by
    intro x hx
    have : x ∈ D.ker := hx
    rw [CFSG.RankThree.OrthogonalInvolutions.dicksonHom_ker] at this
    exact this
  have hval : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by
    intro z
    rcases (show ∀ y : ZMod 2, y = 0 ∨ y = 1 by decide) (Multiplicative.toAdd z) with h | h
    · exact Or.inl (by simpa using congrArg Multiplicative.ofAdd h)
    · exact Or.inr (by simpa using congrArg Multiplicative.ofAdd h)
  rcases hval (D ⟨g, hgO⟩) with h1 | h1
  · exact ⟨g, hker _ h1, hg⟩
  · set r : TauCeti.QuadraticMap.orthogonalGroup Q :=
      ⟨CFSG.ClassicalGroups.Orthogonal.reflect Q a,
        CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q a⟩
    have hr : D r = Multiplicative.ofAdd 1 :=
      CFSG.RankThree.PartOne.KCOrthogonal.dicksonHom_reflect hnd ha
    refine ⟨((r * ⟨g, hgO⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[K] V), hker _ ?_, ?_⟩
    · rw [map_mul, hr, h1, ← ofAdd_add]
      decide
    · intro i
      change CFSG.ClassicalGroups.Orthogonal.reflect Q a (g (w i)) = w' i
      rw [hg i]
      exact CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero (haw i)

theorem exists_spinAction_apply_eq_POmegaPlus (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) {ι : Type} [Fintype ι]
    (w w' : ι → Fin n ⊕ Fin n → F) (hw : LinearIndependent F w) (hw' : LinearIndependent F w')
    (hQ : ∀ i, (Spin.quadPlus n F) (w' i) = (Spin.quadPlus n F) (w i))
    (hpol : ∀ i k, QuadraticMap.polar (Spin.quadPlus n F) (w' i) (w' k) = QuadraticMap.polar
      (Spin.quadPlus n F) (w i) (w k))
    (a : Fin n ⊕ Fin n → F) (ha : (Spin.quadPlus n F) a ≠ 0)
    (haw : ∀ i, QuadraticMap.polar (Spin.quadPlus n F) a (w' i) = 0) :
    ∃ g : ↥(spinGroup (Spin.quadPlus n F)), ∀ i, Spin.spinAction (Spin.quadPlus n F) g (w i) = w' i
      := by
  obtain ⟨g, hgΩ, hg⟩ := exists_mem_omegaGroup_family_apply_eq
    (Spin.nondegenerate_polarBilin_quadPlus n F) w w' hw hw' hQ hpol a ha haw
  obtain ⟨h, hh⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn
    hgΩ
  exact ⟨h, fun i => by rw [hh]; exact hg i⟩

theorem exists_spinAction_apply_eq_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {ι : Type} [Fintype ι]
    (w w' : ι → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) (hw : LinearIndependent F w)
    (hw' : LinearIndependent F w')
    (hQ : ∀ i, (Spin.quadMinus n F bq cq) (w' i) = (Spin.quadMinus n F bq cq) (w i))
    (hpol : ∀ i k, QuadraticMap.polar (Spin.quadMinus n F bq cq) (w' i) (w' k) = QuadraticMap.polar
      (Spin.quadMinus n F bq cq) (w i) (w k))
    (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) (ha : (Spin.quadMinus n F bq cq) a ≠ 0)
    (haw : ∀ i, QuadraticMap.polar (Spin.quadMinus n F bq cq) a (w' i) = 0) :
    ∃ g : ↥(spinGroup (Spin.quadMinus n F bq cq)), ∀ i, Spin.spinAction (Spin.quadMinus n F bq cq) g
      (w i) = w' i := by
  obtain ⟨g, hgΩ, hg⟩ := exists_mem_omegaGroup_family_apply_eq
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr) w w' hw hw' hQ hpol a ha haw
  obtain ⟨h, hh⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus hirr hn hgΩ
  exact ⟨h, fun i => by rw [hh]; exact hg i⟩

end CFSG.StandardType.ClassicalPosition

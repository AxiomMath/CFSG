module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoSiegelConj

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private theorem grcPOm_quadVec_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (F : Spin.HypFrame Q n) (i : Fin n) (s : Bool) :
    F.vec i s ≠ 0 := by
  intro h
  have h1 := F.polar_vec_not i s
  rw [h, QuadraticMap.polar_zero_left] at h1
  exact zero_ne_one h1

private theorem grcPOm_polar_spinAction {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (u : spinGroup Q) (x y : V) :
    QuadraticMap.polar Q (Spin.spinAction Q u x) (Spin.spinAction Q u y) =
      QuadraticMap.polar Q x y := by
  change Q (Spin.spinAction Q u x + Spin.spinAction Q u y)
      - Q (Spin.spinAction Q u x) - Q (Spin.spinAction Q u y)
    = Q (x + y) - Q x - Q y
  rw [← map_add, Spin.map_spinAction, Spin.map_spinAction, Spin.map_spinAction]

private theorem grcPOm_spinAction_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (F : Spin.HypFrame Q n) (i : Fin n) (s : Bool)
    (u : spinGroup Q) : Spin.spinAction Q u (F.vec i s) ≠ 0 := by
  intro h
  exact grcPOm_quadVec_ne_zero F i s ((Spin.spinAction Q u).injective (by simpa using h))

private theorem grcPOm_rootGroup_eq_long
    (n f : ℕ) (hn : 4 ≤ n)
    {γ : Fin (ggU .POmegaMinus n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .POmegaMinus n f).D γ) :
    ∃ (i j : Fin (n - 1)) (hij : i ≠ j) (s t : Bool),
      (ggU .POmegaMinus n f).D.rootGroup γ =
        (((Spin.Twisted.minusFrame n (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2).toHypFrame).longRoot hij s t).range := by
  have hirr : ∀ s : GaloisField 2 f,
      s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 :=
    minusCoeffs_irr 2 f
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus (n := n) (K := GaloisField 2 f)
      (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) hirr hn hl
  refine ⟨i, j, hij, s, t, ?_⟩
  rw [show (ggU .POmegaMinus n f).D.rootGroup γ = Spin.Twisted.minusRootGroup n hirr γ
    from rfl]
  exact Spin.Twisted.minusRootGroup_eq_long (n := n) (b := (minusCoeffs 2 f).1)
    (c := (minusCoeffs 2 f).2) hirr hij s t hst

private theorem grcPOm_side_conditions {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (F : Spin.HypFrame Q n) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (u : spinGroup Q) :
    Q (Spin.spinAction Q u (F.vec j t)) = 0 ∧
      Q (Spin.spinAction Q u (F.vec i s)) = 0 ∧
      QuadraticMap.polar Q (Spin.spinAction Q u (F.vec j t))
        (Spin.spinAction Q u (F.vec i s)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Spin.map_spinAction Q u (F.vec j t)).trans (F.map_vec j t)
  · exact (Spin.map_spinAction Q u (F.vec i s)).trans (F.map_vec i s)
  · exact (grcPOm_polar_spinAction Q u (F.vec j t) (F.vec i s)).trans
      (F.polar_vec_of_ne hij.symm t s)

private theorem grcPOm_linearIndependent_pair_image {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {n : ℕ} (F : Spin.HypFrame Q n) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool) (u : spinGroup Q) :
    LinearIndependent K
      ![Spin.spinAction Q u (F.vec j t), Spin.spinAction Q u (F.vec i s)] := by
  have hQw : Q (F.vec j t) = 0 ∧ Q (F.vec i s) = 0 ∧ Q (F.vec j (!t)) = 0 ∧
      Q (F.vec i (!s)) = 0 :=
    ⟨F.map_vec j t, F.map_vec i s, F.map_vec j (!t), F.map_vec i (!s)⟩
  have h0w : QuadraticMap.polar Q (F.vec j t) (F.vec i s) = 0 ∧
      QuadraticMap.polar Q (F.vec j (!t)) (F.vec i (!s)) = 0 ∧
      QuadraticMap.polar Q (F.vec j t) (F.vec i (!s)) = 0 ∧
      QuadraticMap.polar Q (F.vec i s) (F.vec j (!t)) = 0 :=
    ⟨F.polar_vec_of_ne hij.symm t s, F.polar_vec_of_ne hij.symm (!t) (!s),
      F.polar_vec_of_ne hij.symm t (!s), F.polar_vec_of_ne hij s (!t)⟩
  have hw : LinearIndependent K
      ![F.vec j t, F.vec i s, F.vec j (!t), F.vec i (!s)] :=
    Geo.linearIndependent_quad_of_polar Q hQw (F.polar_vec_not j t)
      (F.polar_vec_not i s) h0w
  have hmap := hw.map' ((Spin.spinAction Q u).toLinearMap) (by simp)
  have hfun : (⇑((Spin.spinAction Q u).toLinearMap) ∘
        ![F.vec j t, F.vec i s, F.vec j (!t), F.vec i (!s)]) =
      ![Spin.spinAction Q u (F.vec j t), Spin.spinAction Q u (F.vec i s),
        Spin.spinAction Q u (F.vec j (!t)), Spin.spinAction Q u (F.vec i (!s))] := by
    funext m
    fin_cases m <;> rfl
  rw [hfun] at hmap
  have hpair := hmap.comp (Fin.castLE (by norm_num : 2 ≤ 4)) (Fin.castLE_injective _)
  have hfun2 : (![Spin.spinAction Q u (F.vec j t), Spin.spinAction Q u (F.vec i s),
        Spin.spinAction Q u (F.vec j (!t)), Spin.spinAction Q u (F.vec i (!s))]) ∘
      Fin.castLE (by norm_num : 2 ≤ 4) =
      ![Spin.spinAction Q u (F.vec j t), Spin.spinAction Q u (F.vec i s)] := by
    funext m
    fin_cases m <;> rfl
  rw [hfun2] at hpair
  exact hpair

private theorem grcPOm_conj_eq_siegel {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {n : ℕ} (F : Spin.HypFrame Q n) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (u : spinGroup Q) :
    (((F.longRoot hij s t).range.map (MulAut.conj u).toMonoidHom).map (Spin.spinAction Q)) =
      siegelGroup Q (Spin.spinAction Q u (F.vec j t)) (Spin.spinAction Q u (F.vec i s)) := by
  exact Geo.map_conj_range_longRoot_eq_siegelGroup F hij s t u

theorem exists_siegelGroup_eq_rootGroup_POmegaMinus
    (n f
        : ℕ) (hn : 4 ≤ n)
    {γ : Fin (ggU .POmegaMinus n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .POmegaMinus n f).D γ) (u : (ggU .POmegaMinus n f).K) :
    ∃ a₁ a₂ : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 a₁ = 0 ∧
      Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2 a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) a₁ a₂ = 0 ∧
      (((ggU .POmegaMinus n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (Spin.spinAction (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2)) =
        siegelGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) a₁ a₂ := by
  let Q : QuadraticForm (GaloisField 2 f)
      ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → GaloisField 2 f) :=
    Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  obtain ⟨i, j, hij, s, t, hX⟩ := grcPOm_rootGroup_eq_long n f hn hl
  let Fr : Spin.HypFrame Q (n - 1) :=
    (Spin.Twisted.minusFrame n (minusCoeffs 2 f).1 (minusCoeffs 2 f).2).toHypFrame
  refine ⟨Spin.spinAction Q u (Fr.vec j t), Spin.spinAction Q u (Fr.vec i s),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact grcPOm_spinAction_ne_zero Fr j t u
  · exact grcPOm_spinAction_ne_zero Fr i s u
  · exact grcPOm_linearIndependent_pair_image Fr hij s t u
  · change Q (Spin.spinAction Q u (Fr.vec j t)) = 0
    exact (grcPOm_side_conditions Fr hij s t u).1
  · change Q (Spin.spinAction Q u (Fr.vec i s)) = 0
    exact (grcPOm_side_conditions Fr hij s t u).2.1
  · change QuadraticMap.polar Q (Spin.spinAction Q u (Fr.vec j t))
        (Spin.spinAction Q u (Fr.vec i s)) = 0
    exact (grcPOm_side_conditions Fr hij s t u).2.2
  · rw [hX]
    exact grcPOm_conj_eq_siegel Fr hij s t u

end CFSG.StandardType.ClassicalPosition

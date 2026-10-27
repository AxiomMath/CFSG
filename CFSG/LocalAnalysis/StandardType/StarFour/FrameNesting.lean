module

public import CFSG.LocalAnalysis.StandardType.StarFour.FrameMinpoly
public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.StandardType.StarFour

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def groupRep {P : Type} [Group P] (η : P →* SpecialLinearGroup F V) :
    P →* (V ≃ₗ[F] V) :=
  SpecialLinearGroup.toLinearEquiv.comp η

variable [Finite F] [Module.Finite F V]

private lemma act_pow {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (p : P) (n : ℕ) (w : V) (i : Fin fr.r) :
    fr.Φ (((ρ p : Module.End F V) ^ n) w) i =
      ((((fr.χ i p : (fr.E i)ˣ) : fr.E i)) ^ n) • fr.Φ w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, LinearEquiv.coe_coe,
        fr.act p (((ρ p : Module.End F V) ^ n) w) i, ih w, smul_smul, pow_succ']

private lemma aeval_act {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (p : P) (q : Polynomial F) (w : V) (i : Fin fr.r) :
    fr.Φ ((Polynomial.aeval (ρ p : Module.End F V) q) w) i =
      Polynomial.aeval (((fr.χ i p : (fr.E i)ˣ) : fr.E i)) q • fr.Φ w i := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ ih₁ ih₂ =>
      rw [map_add (Polynomial.aeval (ρ p : Module.End F V)) q₁ q₂, LinearMap.add_apply,
        map_add fr.Φ, Pi.add_apply, ih₁, ih₂,
        map_add (Polynomial.aeval (((fr.χ i p : (fr.E i)ˣ) : fr.E i))) q₁ q₂, add_smul]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, Pi.smul_apply, act_pow fr p n w i, mul_smul,
        IsScalarTower.algebraMap_smul]

private lemma aeval_minpoly_kills_block {P : Type} [CommGroup P] {ρ : P →* (V ≃ₗ[F] V)}
    (fr : SemiFrame F ρ) (p : P) (i : Fin fr.r) (u : Fin (fr.m i) → fr.E i) :
    (Polynomial.aeval (ρ p : Module.End F V)
      (minpoly F (((fr.χ i p : (fr.E i)ˣ) : fr.E i))))
      (fr.Φ.symm (Pi.single i u)) = 0 := by
  apply fr.Φ.injective
  rw [map_zero]
  funext k
  rw [aeval_act fr p _ _ k, LinearEquiv.apply_symm_apply, Pi.zero_apply]
  by_cases hk : k = i
  · subst hk
    rw [Pi.single_eq_same, minpoly.aeval, zero_smul]
  · rw [Pi.single_eq_of_ne hk, smul_zero]

theorem exists_nesting_index {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V) {g : P} {g' : P'}
    (hg' : ∀ x : P', x ∈ Subgroup.zpowers g') (hgg : η' g' = η g)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (hi : 0 < fr.m i) :
    ∃ i' : Fin fr'.r, 0 < fr'.m i' ∧
      (∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
        fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0) ∧
      (∀ j : Fin fr'.r, j ≠ i' → ∀ y : Fin (fr'.m j) → fr'.E j,
        fr.Φ (fr'.Φ.symm (Pi.single j y)) i = 0) := by
  classical
  have hσ : ((groupRep η') g' : V ≃ₗ[F] V) = (groupRep η) g := by
    show SpecialLinearGroup.toLinearEquiv (η' g') = SpecialLinearGroup.toLinearEquiv (η g)
    rw [hgg]
  set u₀ : Fin (fr.m i) → fr.E i := Pi.single ⟨0, hi⟩ 1 with hu₀def
  have hu₀ : u₀ ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨0, hi⟩
    rw [hu₀def, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have hv₀ : fr.Φ.symm (Pi.single i u₀) ≠ 0 := by
    intro h
    have h1 : Pi.single (M := fun j => Fin (fr.m j) → fr.E j) i u₀ = 0 := by
      have h2 := congrArg fr.Φ h
      rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
    have h3 := congrFun h1 i
    rw [Pi.single_eq_same, Pi.zero_apply] at h3
    exact hu₀ h3
  obtain ⟨j, hj⟩ : ∃ j, fr'.Φ (fr.Φ.symm (Pi.single i u₀)) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₀ (fr'.Φ.injective (by funext k; rw [map_zero]; exact h k))
  have hmj : 0 < fr'.m j := by
    rcases Nat.eq_zero_or_pos (fr'.m j) with h0 | hpos
    · exfalso
      exact hj (by funext t; rw [h0] at t; exact Fin.elim0 t)
    · exact hpos
  have hkey : Polynomial.aeval (((fr'.χ j g' : (fr'.E j)ˣ) : fr'.E j))
      (minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i))) = 0 := by
    have h1 := aeval_act fr' g'
      (minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)))
      (fr.Φ.symm (Pi.single i u₀)) j
    rw [hσ, aeval_minpoly_kills_block fr g i u₀, map_zero] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_right hj
  have hmin : minpoly F (((fr'.χ j g' : (fr'.E j)ˣ) : fr'.E j)) =
      minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)) := by
    have hx : IsIntegral F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)) := IsIntegral.of_finite F _
    exact ((minpoly.eq_iff_aeval_eq_zero (A := F)
      (x := ((fr'.χ j g' : (fr'.E j)ˣ) : fr'.E j))
      (minpoly.irreducible hx) (minpoly.monic hx)).mpr hkey).symm
  refine ⟨j, hmj, ?_, ?_⟩
  · intro u k hk
    rcases Nat.eq_zero_or_pos (fr'.m k) with hk0 | hmk
    · funext t
      rw [hk0] at t
      exact Fin.elim0 t
    · have hkill := aeval_minpoly_kills_block fr g i u
      have h2 := aeval_act fr' g' (minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)))
        (fr.Φ.symm (Pi.single i u)) k
      rw [hσ, hkill, map_zero] at h2
      have hne : Polynomial.aeval (((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k))
          (minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i))) ≠ 0 := by
        intro hz
        have hx : IsIntegral F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)) :=
          IsIntegral.of_finite F _
        have heq : minpoly F (((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k)) =
            minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)) :=
          ((minpoly.eq_iff_aeval_eq_zero (A := F)
            (x := ((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k))
            (minpoly.irreducible hx) (minpoly.monic hx)).mpr hz).symm
        exact (SemiFrame.minpoly_ne_of_ne fr' g' hg' hk hmk hmj) (heq.trans hmin.symm)
      exact (smul_eq_zero.mp h2.symm).resolve_left hne
  · intro k hk y
    rcases Nat.eq_zero_or_pos (fr'.m k) with hk0 | hmk
    · have hy : y = 0 := by
        funext t
        rw [hk0] at t
        exact Fin.elim0 t
      simp only [hy, Pi.single_zero, map_zero, Pi.zero_apply]
    · have hkill := aeval_minpoly_kills_block fr' g' k y
      have h2 := aeval_act fr g (minpoly F (((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k)))
        (fr'.Φ.symm (Pi.single k y)) i
      rw [← hσ] at h2
      rw [hkill, map_zero] at h2
      by_contra hne
      have hz : Polynomial.aeval (((fr.χ i g : (fr.E i)ˣ) : fr.E i))
          (minpoly F (((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k))) = 0 :=
        (smul_eq_zero.mp h2.symm).resolve_right hne
      have hx : IsIntegral F (((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k)) :=
        IsIntegral.of_finite F _
      have heq : minpoly F (((fr.χ i g : (fr.E i)ˣ) : fr.E i)) =
          minpoly F (((fr'.χ k g' : (fr'.E k)ˣ) : fr'.E k)) :=
        ((minpoly.eq_iff_aeval_eq_zero (A := F)
          (x := ((fr.χ i g : (fr.E i)ˣ) : fr.E i))
          (minpoly.irreducible hx) (minpoly.monic hx)).mpr hz).symm
      exact (SemiFrame.minpoly_ne_of_ne fr' g' hg' hk hmk hmj) (heq.symm.trans hmin.symm)

theorem exists_nesting_embedding {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V) {g : P} {g' : P'}
    (hg' : ∀ x : P', x ∈ Subgroup.zpowers g') (hgg : η' g' = η g)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (hi : 0 < fr.m i) (i' : Fin fr'.r)
    (h3 : ∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
      fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0) :
    ∃ ε : fr'.E i' →ₐ[F] fr.E i,
      (∀ (c : fr'.E i') (u : Fin (fr.m i) → fr.E i),
        fr'.Φ (fr.Φ.symm (Pi.single i (ε c • u))) i' = c • fr'.Φ (fr.Φ.symm (Pi.single i u)) i') ∧
      (∀ (c : fr'.E i') (y : Fin (fr'.m i') → fr'.E i'),
        fr.Φ (fr'.Φ.symm (Pi.single i' (c • y))) i =
          ε c • fr.Φ (fr'.Φ.symm (Pi.single i' y)) i) := by
  classical
  have hσ : ((groupRep η') g' : V ≃ₗ[F] V) = (groupRep η) g := by
    show SpecialLinearGroup.toLinearEquiv (η' g') = SpecialLinearGroup.toLinearEquiv (η g)
    rw [hgg]
  set u₀ : Fin (fr.m i) → fr.E i := Pi.single ⟨0, hi⟩ 1 with hu₀def
  have hu₀ : u₀ ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨0, hi⟩
    rw [hu₀def, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  set si : fr.E i := ((fr.χ i g : (fr.E i)ˣ) : fr.E i) with hsi
  set si' : fr'.E i' := ((fr'.χ i' g' : (fr'.E i')ˣ) : fr'.E i') with hsi'
  let A : (Fin (fr.m i) → fr.E i) →ₗ[F] (Fin (fr'.m i') → fr'.E i') :=
    { toFun := fun u => fr'.Φ (fr.Φ.symm (Pi.single i u)) i'
      map_add' := by
        intro u v
        simp only [Pi.single_add, map_add, Pi.add_apply]
      map_smul' := by
        intro a u
        simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply] }
  let B : (Fin (fr'.m i') → fr'.E i') →ₗ[F] (Fin (fr.m i) → fr.E i) :=
    { toFun := fun y => fr.Φ (fr'.Φ.symm (Pi.single i' y)) i
      map_add' := by
        intro y z
        simp only [Pi.single_add, map_add, Pi.add_apply]
      map_smul' := by
        intro a y
        simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hA_s : ∀ u, A (si • u) = si' • A u := by
    intro u
    have hv : fr.Φ.symm (Pi.single i (si • u)) =
        (groupRep η) g (fr.Φ.symm (Pi.single i u)) := by
      apply fr.Φ.injective
      rw [LinearEquiv.apply_symm_apply]
      funext k
      rw [fr.act g _ k, LinearEquiv.apply_symm_apply]
      by_cases hk : k = i
      · subst hk
        rw [hsi, Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, smul_zero]
    change fr'.Φ (fr.Φ.symm (Pi.single i (si • u))) i' =
      si' • fr'.Φ (fr.Φ.symm (Pi.single i u)) i'
    rw [hv, ← hσ, fr'.act g' _ i', ← hsi']
  have hB_s : ∀ y, B (si' • y) = si • B y := by
    intro y
    have hw : fr'.Φ.symm (Pi.single i' (si' • y)) =
        (groupRep η') g' (fr'.Φ.symm (Pi.single i' y)) := by
      apply fr'.Φ.injective
      rw [LinearEquiv.apply_symm_apply]
      funext k
      rw [fr'.act g' _ k, LinearEquiv.apply_symm_apply]
      by_cases hk : k = i'
      · subst hk
        rw [hsi', Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, smul_zero]
    change fr.Φ (fr'.Φ.symm (Pi.single i' (si' • y))) i =
      si • fr.Φ (fr'.Φ.symm (Pi.single i' y)) i
    rw [hw, hσ, fr.act g _ i, ← hsi]
  have hA_inj : Function.Injective A := by
    intro u v huv
    have hΦ : fr.Φ.symm (Pi.single i u) = fr.Φ.symm (Pi.single i v) := by
      apply fr'.Φ.injective
      funext j
      by_cases hj : j = i'
      · subst hj
        exact huv
      · rw [h3 u j hj, h3 v j hj]
    have h2 := fr.Φ.symm.injective hΦ
    have h3' := congrFun h2 i
    rwa [Pi.single_eq_same, Pi.single_eq_same] at h3'
  have hA_pow : ∀ n u, A ((si ^ n) • u) = (si' ^ n) • A u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
        intro u
        rw [pow_succ', mul_smul, hA_s (si ^ n • u), ih u, smul_smul, pow_succ']
  have hA_poly : ∀ (q : Polynomial F) u,
      A (Polynomial.aeval si q • u) = Polynomial.aeval si' q • A u := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ ih₁ ih₂ =>
        intro u
        rw [map_add (Polynomial.aeval si) q₁ q₂, add_smul, map_add A, ih₁ u, ih₂ u,
          map_add (Polynomial.aeval si') q₁ q₂, add_smul]
    | monomial n a =>
        intro u
        rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, mul_smul, mul_smul,
          IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul, map_smul A,
          hA_pow n u]
  have hmu' : Polynomial.aeval si (minpoly F si') = 0 := by
    have h := hA_poly (minpoly F si') u₀
    rw [minpoly.aeval, zero_smul] at h
    have h2 : Polynomial.aeval si (minpoly F si') • u₀ = 0 := by
      apply hA_inj
      rw [h, map_zero]
    exact (smul_eq_zero.mp h2).resolve_right hu₀
  obtain ⟨ε, hε⟩ := SemiFrame.exists_algHom_chi fr' g' hg' i' si hmu'
  have hA_eps : ∀ c : fr'.E i', ∀ u, A (ε c • u) = c • A u := by
    intro c
    have hc : c ∈ Algebra.adjoin F
        ({((fr'.χ i' g' : (fr'.E i')ˣ) : fr'.E i')} : Set (fr'.E i')) := by
      rw [SemiFrame.adjoin_chi_eq_top fr' g' hg' i']
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        intro u
        rw [hε, hA_s u, ← hsi']
    | algebraMap r =>
        intro u
        rw [ε.commutes, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul,
          map_smul A]
    | add x y hx hy ihx ihy =>
        intro u
        rw [map_add ε, add_smul, map_add A, ihx u, ihy u, add_smul]
    | mul x y hx hy ihx ihy =>
        intro u
        rw [map_mul ε, mul_smul, ihx (ε y • u), ihy u, smul_smul]
  have hB_eps : ∀ c : fr'.E i', ∀ y, B (c • y) = ε c • B y := by
    intro c
    have hc : c ∈ Algebra.adjoin F
        ({((fr'.χ i' g' : (fr'.E i')ˣ) : fr'.E i')} : Set (fr'.E i')) := by
      rw [SemiFrame.adjoin_chi_eq_top fr' g' hg' i']
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst hx
        intro z
        rw [← hsi', hB_s z, hε]
    | algebraMap r =>
        intro z
        rw [ε.commutes, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul,
          map_smul B]
    | add x y hx hy ihx ihy =>
        intro z
        rw [map_add ε, add_smul, map_add B, ihx z, ihy z, add_smul]
    | mul x y hx hy ihx ihy =>
        intro z
        rw [map_mul ε, mul_smul, ihx (y • z), ihy z, smul_smul]
  exact ⟨ε, fun c u => hA_eps c u, fun c y => hB_eps c y⟩

theorem exists_nesting {P P' : Type} [CommGroup P] [CommGroup P']
    (η : P →* SpecialLinearGroup F V) (η' : P' →* SpecialLinearGroup F V) {g : P} {g' : P'}
    (hg' : ∀ x : P', x ∈ Subgroup.zpowers g') (hgg : η' g' = η g)
    (fr : SemiFrame F (groupRep η)) (fr' : SemiFrame F (groupRep η')) (i : Fin fr.r)
    (hi : 0 < fr.m i) :
    ∃ (i' : Fin fr'.r) (ε : fr'.E i' →ₐ[F] fr.E i), 0 < fr'.m i' ∧
      (∀ (u : Fin (fr.m i) → fr.E i) (j : Fin fr'.r), j ≠ i' →
        fr'.Φ (fr.Φ.symm (Pi.single i u)) j = 0) ∧
      (∀ j : Fin fr'.r, j ≠ i' → ∀ y : Fin (fr'.m j) → fr'.E j,
        fr.Φ (fr'.Φ.symm (Pi.single j y)) i = 0) ∧
      (∀ (c : fr'.E i') (u : Fin (fr.m i) → fr.E i),
        fr'.Φ (fr.Φ.symm (Pi.single i (ε c • u))) i' = c • fr'.Φ (fr.Φ.symm (Pi.single i u)) i') ∧
      (∀ (c : fr'.E i') (y : Fin (fr'.m i') → fr'.E i'),
        fr.Φ (fr'.Φ.symm (Pi.single i' (c • y))) i =
          ε c • fr.Φ (fr'.Φ.symm (Pi.single i' y)) i) := by
  obtain ⟨i', hmi', h3, h4⟩ := exists_nesting_index η η' hg' hgg fr fr' i hi
  obtain ⟨ε, hε1, hε2⟩ := exists_nesting_embedding η η' hg' hgg fr fr' i hi i' h3
  exact ⟨i', ε, hmi', h3, h4, hε1, hε2⟩

end CFSG.StandardType.StarFour

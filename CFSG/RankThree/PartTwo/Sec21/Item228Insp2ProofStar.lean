module

public import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofMat
public import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofConj
public import CFSG.RankThree.PartTwo.Sec21.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)
open CFSG.RankThree.PartTwo.Sec4.Res417Frame (permGL)
open Matrix

variable {G : Type} [Group G] {X A : Subgroup G} {K : Type} [Field K]

theorem autIn_eq_starOf' (A X : Subgroup G) : Sec4.autIn X A = starOf A X := by
  rw [Sec4.autIn, starOf, Subgroup.inf_subgroupOf_right]

theorem coe_eq_conj_of_actSL (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    {a : Subgroup.normalizer (X : Set G)} {D : GL (Fin 3) K} (hD : actSL ι a = slConjugation 3 K D)
    {x y : X} (h : (y : G) = a * x * (a : G)⁻¹) :
    ((ι y : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (D : Matrix (Fin 3) (Fin 3) K) *
        ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  rw [← actSL_apply_eq ι a h, hD, coe_slConjugation]

theorem mul_comm_of_actSL_isDiag (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    {a : Subgroup.normalizer (X : Set G)} {D : GL (Fin 3) K}
    (hDd : (D : Matrix (Fin 3) (Fin 3) K).IsDiag) (hD : actSL ι a = slConjugation 3 K D) {x : X}
    (hx : ((ι x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    (a : G) * x = x * a := by
  have hmem : (a : G) * x * (a : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp a.2 x).mp x.2
  have h := coe_eq_conj_of_actSL ι hD (x := x) (y := ⟨_, hmem⟩) rfl
  rw [mul_comm_of_isDiag hDd hx, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] at h
  have h' := congrArg Subtype.val (ι.injective (ext_of_coe h))
  change (a : G) * x * (a : G)⁻¹ = x at h'
  calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
    _ = x * a := by rw [h']

theorem diagUnits_cubes {s t : Kˣ} (hs : s ^ 3 = 1) (ht : t ^ 3 = 1) (i j : Fin 3) :
    ((diagUnits 1 s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
      ((diagUnits 1 s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3 := by
  have hs' : (s : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hs, Units.val_one]
  have ht' : (t : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  have hall : ∀ k : Fin 3,
      ((diagUnits 1 s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k ^ 3 = 1 := by
    intro k
    rw [coe_diagUnits, diagonal_apply_eq]
    fin_cases k
    · simp
    · exact hs'
    · exact ht'
  rw [hall i, hall j]

theorem nonempty_starOf_equiv_perm (h2 : (2 : K) = 0) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (ι : X ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (hTA : ∀ y ∈ tZero K, ((ι.symm y : X) : G) ∈ A)
    (hT : ∀ x : X, (x : G) ∈ A → ι x ∈ tZero K)
    (hact : ∀ a (ha : a ∈ A), ∃ s t : Kˣ, s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      actSL ι ⟨a, hAX ha⟩ = slConjugation 3 K (diagUnits 1 s t)) :
    Nonempty (starOf A X ≃* Equiv.Perm (Fin 3)) := by
  rw [← autIn_eq_starOf']
  set Θ : Equiv.Perm (Fin 3) →* G := X.subtype.comp (ι.symm.toMonoidHom.comp (permSL h2))
    with hΘ
  have hΘX : ∀ σ, Θ σ ∈ X := fun σ => (ι.symm (permSL h2 σ)).2
  have hΘι : ∀ σ, ι ⟨Θ σ, hΘX σ⟩ = permSL h2 σ := fun σ => by
    have : (⟨Θ σ, hΘX σ⟩ : X) = ι.symm (permSL h2 σ) := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hdiagD : ∀ s t : Kˣ, ((diagUnits 1 s t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    fun s t => by rw [coe_diagUnits]; exact isDiag_diagonal _
  set z₀ : X := ι.symm (regSL hω) with hz₀
  have hz₀A : (z₀ : G) ∈ A := hTA _ (regSL_mem_tZero hω)
  refine Sec4.Res417Frame.nonempty_autIn_equiv_perm Θ hΘX ?_ ?_ ?_
  ·
    intro σ a ha
    obtain ⟨s, t, hs, ht, hD⟩ := hact a ha
    set w : X := ⟨Θ σ, hΘX σ⟩ with hw
    have hvX : a * ((w⁻¹ : X) : G) * a⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hAX ha) _).mp (w⁻¹).2
    set v : X := ⟨_, hvX⟩ with hv
    have hιv := coe_eq_conj_of_actSL ι hD (x := w⁻¹) (y := v) rfl
    obtain ⟨hCd, hC3⟩ := Sec4.Res417Frame.commutator_permGL σ (hdiagD s t)
      (diagUnits_cubes hs ht)
    have hwv : ((ι (w * v) : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((permGL σ * diagUnits 1 s t * (permGL σ)⁻¹ * (diagUnits 1 s t)⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by
      have hwinv : ((ι w⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (((permGL σ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [map_inv, hw, hΘι, ← map_inv, coe_permSL, map_inv]
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hιv, hwinv, hw, hΘι, coe_permSL]
      simp only [Units.val_mul, Matrix.mul_assoc]
    have hwvT : ι (w * v) ∈ tZero K := by
      refine ⟨by rw [hwv]; exact hCd, ext_of_coe ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_pow, hwv, ← Units.val_pow_eq_pow_val, hC3, Units.val_one,
        Matrix.SpecialLinearGroup.coe_one]
    have hwvA : ((w * v : X) : G) ∈ A := by
      have := hTA _ hwvT
      rwa [MulEquiv.symm_apply_apply] at this
    have heq : Θ σ * a * (Θ σ)⁻¹ = ((w * v : X) : G) * a := by
      change Θ σ * a * (Θ σ)⁻¹ = Θ σ * (a * (Θ σ)⁻¹ * a⁻¹) * a
      group
    rw [heq]
    exact A.mul_mem hwvA ha
  ·
    intro σ hσ
    have h1 := hσ _ hz₀A
    have h2' : ι ⟨Θ σ, hΘX σ⟩ * ι z₀ = ι z₀ * ι ⟨Θ σ, hΘX σ⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    rw [hΘι, hz₀, MulEquiv.apply_symm_apply] at h2'
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 3) K =>
      (M : Matrix (Fin 3) (Fin 3) K)) h2'
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_regSL] at h3
    exact Sec4.Res417Frame.eq_one_of_permGL_commute (injective_omega hω) h3
  ·
    intro l hlX hlN
    set l' : X := ⟨l, hlX⟩ with hl'
    set Gm : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL (ι l') with hGm
    set H : Subgroup (GL (Fin 3) K) :=
      (A.subgroupOf X).map (Matrix.SpecialLinearGroup.toGL.comp ι.toMonoidHom) with hH
    have hdiag : ∀ u ∈ H, (u : Matrix (Fin 3) (Fin 3) K).IsDiag := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hT x (Subgroup.mem_subgroupOf.mp hx)).1
    have hsep : ∀ i j : Fin 3, i ≠ j →
        ∃ u ∈ H, (u : Matrix (Fin 3) (Fin 3) K) i i ≠ (u : Matrix (Fin 3) (Fin 3) K) j j := by
      intro i j hij
      refine ⟨Matrix.SpecialLinearGroup.toGL (regSL hω), ⟨z₀, Subgroup.mem_subgroupOf.mpr hz₀A,
        by simp [hz₀]⟩, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_regSL, diagonal_apply_eq,
        diagonal_apply_eq]
      exact fun h => hij (injective_omega hω h)
    have hG : ∀ u ∈ H, Gm⁻¹ * u * Gm ∈ H := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨l'⁻¹ * x * l', Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · have hx' : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlN) (x : G)).mp hx'
        simpa [hl', mul_assoc] using this
      · simp [hGm, map_mul, map_inv]
    obtain ⟨σ', hσ'⟩ := Sec15.KSL3Two.exists_monomial_of_normalizes hdiag hsep hG
    obtain ⟨π, hπ⟩ := Sec4.Res417Frame.exists_perm_of_isMonomialWith hσ'
    refine ⟨π, fun a ha => ?_⟩
    obtain ⟨s, t, hs, ht, hD⟩ := hact a ha
    set m : X := (⟨Θ π, hΘX π⟩ : X)⁻¹ * l' with hm
    have hmd : ((ι m : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
      have : ((ι m : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (((permGL π)⁻¹ * Gm : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hm, map_mul, map_inv, hΘι, Matrix.SpecialLinearGroup.coe_mul, Units.val_mul, hGm,
          Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv]
        rfl
      rw [this]
      exact hπ
    have hma := mul_comm_of_actSL_isDiag ι (hdiagD s t) hD hmd
    have hl : l = Θ π * (m : G) := by
      change l = Θ π * ((Θ π)⁻¹ * l)
      group
    rw [hl]
    calc Θ π * (m : G) * a * (Θ π * (m : G))⁻¹ =
        Θ π * ((m : G) * a) * (m : G)⁻¹ * (Θ π)⁻¹ := by group
      _ = Θ π * (a * (m : G)) * (m : G)⁻¹ * (Θ π)⁻¹ := by
        rw [show (m : G) * a = a * (m : G) from hma.symm]
      _ = Θ π * a * (Θ π)⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec21.Item228Insp2Proof

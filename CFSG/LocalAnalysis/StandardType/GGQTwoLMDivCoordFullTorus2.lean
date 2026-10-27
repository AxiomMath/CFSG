module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullTorus

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord CFSG.SectionRank.OddCover
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 Matrix

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

theorem qTwoLMDivF_tormono {m : ℕ}
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0}
    (hdiag : ∀ f, ggIsDiagMat (δ f))
    (hperm : ∀ (σ : Equiv.Perm (Fin m)) f,
      permGL σ * δ f * (permGL σ)⁻¹ = δ (SpCoord.permAut σ f))
    (hsep : ∀ i j : Fin m, i ≠ j → ∃ f : Fin m → Multiplicative (ZMod 3),
      ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i ≠
        ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) j j)
    (u : GL (Fin m) F0) (hu : ∀ f, ∃ f', ∃ z : F0, z ≠ 0 ∧
      (u : Matrix (Fin m) (Fin m) F0) * ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        z • ((δ f' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (u : Matrix (Fin m) (Fin m) F0)) :
    ∃ ρ : Equiv.Perm (Fin m), ∀ f,
      u * (δ f : GL (Fin m) F0) = (δ (SpCoord.permAut ρ f) : GL (Fin m) F0) * u := by
  classical
  choose d hd using hdiag
  let M : Matrix (Fin m) (Fin m) F0 := (u : Matrix (Fin m) (Fin m) F0)
  let N : Matrix (Fin m) (Fin m) F0 := ((u⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
  have hMN : M * N = 1 := by
    have h := congrArg (fun g : GL (Fin m) F0 => (g : Matrix (Fin m) (Fin m) F0))
      (mul_inv_cancel u)
    simpa [M, N] using h
  have hNM : N * M = 1 := by
    have h := congrArg (fun g : GL (Fin m) F0 => (g : Matrix (Fin m) (Fin m) F0))
      (inv_mul_cancel u)
    simpa [M, N] using h
  have hrow : ∀ (g : Fin m → Multiplicative (ZMod 3)) (k l l' : Fin m),
      M k l ≠ 0 → M k l' ≠ 0 → d g l = d g l' := by
    intro g k l l' hl hl'
    obtain ⟨g', z, hz, heq⟩ := hu g
    have h1 : M k l * d g l = z * (d g' k * M k l) := by
      have h := congrFun (congrFun heq k) l
      rw [hd g, hd g'] at h
      rw [Matrix.mul_diagonal] at h
      rw [smul_mul_assoc, Matrix.smul_apply, Matrix.diagonal_mul] at h
      simpa using h
    have h2 : M k l' * d g l' = z * (d g' k * M k l') := by
      have h := congrFun (congrFun heq k) l'
      rw [hd g, hd g'] at h
      rw [Matrix.mul_diagonal] at h
      rw [smul_mul_assoc, Matrix.smul_apply, Matrix.diagonal_mul] at h
      simpa using h
    have e1 : d g l = z * d g' k := by
      have hh : M k l * d g l = M k l * (z * d g' k) := by rw [h1]; ring
      exact mul_left_cancel₀ hl hh
    have e2 : d g l' = z * d g' k := by
      have hh : M k l' * d g l' = M k l' * (z * d g' k) := by rw [h2]; ring
      exact mul_left_cancel₀ hl' hh
    rw [e1, e2]
  have huniqrow : ∀ (k l l' : Fin m), M k l ≠ 0 → M k l' ≠ 0 → l = l' := by
    intro k l l' hl hl'
    by_contra hne
    obtain ⟨g, hg⟩ := hsep l l' hne
    rw [hd g] at hg
    have hg' : d g l ≠ d g l' := by simpa [Matrix.diagonal_apply_eq] using hg
    exact hg' (hrow g k l l' hl hl')
  have hex : ∀ k : Fin m, ∃ l : Fin m, M k l ≠ 0 := by
    intro k
    by_contra h
    have hzero : ∀ l, M k l = 0 := by
      intro l
      by_contra hl
      exact h ⟨l, hl⟩
    have hsum : (M * N) k k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [hzero l, zero_mul]
    have hone : (M * N) k k = 1 := by simp [hMN]
    rw [hsum] at hone
    exact one_ne_zero hone.symm
  let r : Fin m → Fin m := fun k => Classical.choose (hex k)
  have hr : ∀ k, M k (r k) ≠ 0 := fun k => Classical.choose_spec (hex k)
  have hr_eq : ∀ (k l : Fin m), M k l ≠ 0 → l = r k :=
    fun k l hl => huniqrow k l (r k) hl (hr k)
  have hrinj : Function.Injective r := by
    intro k k' hkk
    by_contra hne
    have hmk : M k' (r k) ≠ 0 := by rw [hkk]; exact hr k'
    have h0 : (M * N) k' k = 0 := by
      simp [hMN, Matrix.one_apply, Ne.symm hne]
    have hcalc : (M * N) k' k = M k' (r k) * N (r k) k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (r k)]
      · intro j _ hj
        have hMj : M k' j = 0 := by
          by_contra hjj
          exact hj ((hr_eq k' j hjj).trans hkk.symm)
        rw [hMj, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hNk : N (r k) k = 0 := by
      rw [hcalc] at h0
      exact (mul_eq_zero.mp h0).resolve_left hmk
    have hcalc2 : (M * N) k k = M k (r k) * N (r k) k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (r k)]
      · intro j _ hj
        have hMj : M k j = 0 := by
          by_contra hjj
          exact hj (hr_eq k j hjj)
        rw [hMj, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have h1 : (M * N) k k = 1 := by simp [hMN]
    rw [hcalc2, hNk, mul_zero] at h1
    exact one_ne_zero h1.symm
  have hdiagperm : ∀ (σ : Equiv.Perm (Fin m)) (g : Fin m → Multiplicative (ZMod 3))
      (k : Fin m), d (SpCoord.permAut σ g) k = d g (σ⁻¹ k) := by
    intro σ g k
    have h2 : permGL σ * δ g = δ (SpCoord.permAut σ g) * permGL σ := by
      calc permGL σ * δ g = permGL σ * δ g * (permGL σ)⁻¹ * permGL σ := by group
        _ = δ (SpCoord.permAut σ g) * permGL σ := by rw [hperm σ g]
    have hmat : ((permGL σ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
        Matrix.diagonal (d g) =
        Matrix.diagonal (d (SpCoord.permAut σ g)) *
          ((permGL σ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
      have h := congrArg (fun x : GL (Fin m) F0 =>
        ((x : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) h2
      simpa [hd g, hd (SpCoord.permAut σ g)] using h
    have hkk := congrFun (congrFun hmat k) (σ⁻¹ k)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hkk
    have hp : ((permGL σ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) k (σ⁻¹ k) = 1 := by
      simp [permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [hp, one_mul, mul_one] at hkk
    exact hkk.symm
  let ρ : Equiv.Perm (Fin m) := (Equiv.ofBijective r hrinj.bijective_of_finite).symm
  refine ⟨ρ, fun g => ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro k l
  simp only [Units.val_mul, hd g, hd (SpCoord.permAut ρ g)]
  by_cases hl : l = r k
  · subst hl
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hdiagperm ρ g k]
    have hρ : ρ⁻¹ k = r k := rfl
    rw [hρ]
    ring
  · have hMkl : (u : Matrix (Fin m) (Fin m) F0) k l = 0 := by
      by_contra h
      exact hl (hr_eq k l h)
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hMkl]
    ring

theorem qTwoLMDivF_torus (hF0 : Nat.card F0 = 4) (m : ℕ) :
    ∃ δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0, QTwoDivFullTorus hF0 δ := by
  classical
  have hdiag : ∀ f, ggIsDiagMat (qTwoLMDivF_diagHom hF0 m f) :=
    fun f => ⟨fun i => ((qTwoLMDivF_unitsIso hF0 (f i) : F0ˣ) : F0), qTwoLMDivF_diagHom_coe hF0 f⟩
  have hperm : ∀ (σ : Equiv.Perm (Fin m)) f,
      permGL σ * qTwoLMDivF_diagHom hF0 m f * (permGL σ)⁻¹ =
        qTwoLMDivF_diagHom hF0 m (SpCoord.permAut σ f) := by
    intro σ f
    simp only [qTwoLMDivF_diagHom, MonoidHom.comp_apply, permGL_mul_diagHom_mul_inv]
    rfl
  have hsep : ∀ i j : Fin m, i ≠ j → ∃ f : Fin m → Multiplicative (ZMod 3),
      ((qTwoLMDivF_diagHom hF0 m f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) i i ≠
        ((qTwoLMDivF_diagHom hF0 m f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) j j := by
    intro i j hij
    refine ⟨(rootV i j).1, ?_⟩
    simp only [qTwoLMDivF_diagHom_coe, Matrix.diagonal_apply_eq]
    intro h
    have h1 : (rootV i j).1 i = (rootV i j).1 j :=
      (qTwoLMDivF_unitsIso hF0).injective (Units.ext h)
    have h2 : crd (rootV i j : ↥(sumZero m 3)) i = crd (rootV i j) j := by
      simpa [crd] using congrArg Multiplicative.toAdd h1
    rw [crd_rootV_left hij, crd_rootV_right hij] at h2
    exact absurd h2 (by decide)
  have hinj : Function.Injective (qTwoLMDivF_diagHom hF0 m) := by
    intro f g hfg
    have h1 : (fun i => qTwoLMDivF_unitsIso hF0 (f i)) =
        (fun i => qTwoLMDivF_unitsIso hF0 (g i)) :=
      diagHom_injective m hfg
    funext i
    exact (qTwoLMDivF_unitsIso hF0).injective (congrFun h1 i)
  have hsurj : ∀ g : GL (Fin m) F0, ggIsDiagMat g →
      ∃ f, qTwoLMDivF_diagHom hF0 m f = g := by
    intro g hg
    obtain ⟨d, hd⟩ := hg
    have hdne : ∀ i, d i ≠ 0 := by
      intro i h0
      have hunit : ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          (((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) = 1 := by
        simpa using congrArg (fun x : GL (Fin m) F0 =>
          ((x : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) (mul_inv_cancel g)
      have hentry := congrFun (congrFun hunit i) i
      rw [hd, Matrix.diagonal_mul, h0, zero_mul] at hentry
      exact absurd (by simpa using hentry.symm : (1 : F0) = 0) one_ne_zero
    let f : Fin m → Multiplicative (ZMod 3) :=
      fun i => (qTwoLMDivF_unitsIso hF0).symm (Units.mk0 (d i) (hdne i))
    refine ⟨f, ?_⟩
    apply Units.ext
    rw [qTwoLMDivF_diagHom_coe, hd]
    congr 1
    funext i
    exact congrArg (fun u : F0ˣ => (u : F0))
      (MulEquiv.apply_symm_apply (qTwoLMDivF_unitsIso hF0) _)
  refine ⟨qTwoLMDivF_diagHom hF0 m, hinj, hdiag, hsurj, hperm, ?_, ?_, ?_⟩
  · intro c
    rw [qTwoLMDivF_diagHom_coe]
    congr 1
    funext i
    exact congrArg (fun u : F0ˣ => (u : F0))
      (MulEquiv.apply_symm_apply (qTwoLMDivF_unitsIso hF0) c)
  · intro f
    rw [qTwoLMDivF_zpowers_oneVec_iff]
    constructor
    · rintro ⟨c, hc⟩
      rw [qTwoLMDivF_diagHom_coe] at hc
      have h := Matrix.diagonal_injective hc
      intro i j
      apply (qTwoLMDivF_unitsIso hF0).injective
      apply Units.ext
      rw [congrFun h i, congrFun h j]
    · intro hf
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        exact ⟨1, by ext i; exact i.elim0⟩
      · haveI : NeZero m := ⟨hpos.ne'⟩
        refine ⟨((qTwoLMDivF_unitsIso hF0 (f 0) : F0ˣ) : F0), ?_⟩
        rw [qTwoLMDivF_diagHom_coe]
        congr 1
        funext i
        rw [hf i 0]
  · intro u hu
    exact qTwoLMDivF_tormono hdiag hperm hsep u hu

end CFSG.StandardType.QTwo

end

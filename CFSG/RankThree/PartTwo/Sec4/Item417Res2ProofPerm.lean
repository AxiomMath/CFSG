module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.RankThree.PartTwo.Sec15.KSL3TwoProofDiag

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Frame

open Matrix CFSG.RankThree.PartTwo.Sec15.KSL3Two

variable {K : Type} [Field K]

theorem isDiag_of_commute_diagonal {M : Matrix (Fin 3) (Fin 3) K} {d : Fin 3 → K}
    (hd : Function.Injective d) (h : M * diagonal d = diagonal d * M) : M.IsDiag := by
  intro i j hij
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h' : M i j * (d j - d i) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr fun e => hij (hd e).symm)

theorem apply_self_ne_zero_of_isDiag {D : GL (Fin 3) K}
    (h : (D : Matrix (Fin 3) (Fin 3) K).IsDiag) (i : Fin 3) :
    (D : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
  have hdet : (D : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (D.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  rw [← h.diagonal_diag, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem coe_inv_of_isDiag {D : GL (Fin 3) K} (h : (D : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => ((D : Matrix (Fin 3) (Fin 3) K) i i)⁻¹ := by
  set d : Fin 3 → K := fun i => (D : Matrix (Fin 3) (Fin 3) K) i i with hd
  have hDd : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := h.diagonal_diag.symm
  have hED : (diagonal fun i => (d i)⁻¹) * (D : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hDd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (apply_self_ne_zero_of_isDiag h i)
  calc ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = (diagonal fun i => (d i)⁻¹) * (D : Matrix (Fin 3) (Fin 3) K) *
          ((D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hED, Matrix.one_mul]
    _ = _ := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

@[expose] noncomputable def permGL : Equiv.Perm (Fin 3) →* GL (Fin 3) K :=
  (Matrix.permMatrixHom (n := Fin 3) (R := K)).toHomUnits

theorem permGL_apply (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = if i = σ j then 1 else 0 := by
  change (σ⁻¹.permMatrix K) i j = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  congr 1
  rw [Option.mem_def, Option.some_inj, Equiv.Perm.inv_eq_iff_eq, eq_comm]

theorem isMonomialWith_permGL (σ : Equiv.Perm (Fin 3)) :
    IsMonomialWith ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) σ := by
  intro i j
  rw [permGL_apply]
  split_ifs with h <;> simp [h]

theorem det_permGL (h2 : (2 : K) = 0) (σ : Equiv.Perm (Fin 3)) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  change (σ⁻¹.permMatrix K).det = 1
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h]
  · simp
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination (-1 : K) * h2

theorem permGL_mul_diagonal (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → K) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d =
      diagonal (fun i => d (σ⁻¹ i)) * ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, permGL_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem eq_one_of_permGL_commute {σ : Equiv.Perm (Fin 3)} {d : Fin 3 → K}
    (hd : Function.Injective d)
    (h : ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d =
      diagonal d * ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : σ = 1 := by
  ext j
  have h1 := congrFun (congrFun h (σ j)) j
  have hP : ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (σ j) j = 1 := by
    rw [permGL_apply]
    simp
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hP, one_mul, mul_one] at h1
  rw [Equiv.Perm.one_apply]
  exact congrArg Fin.val (hd h1.symm)

theorem eq_one_of_permGL_isDiag {σ : Equiv.Perm (Fin 3)}
    (h : ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) : σ = 1 := by
  ext j
  rw [Equiv.Perm.one_apply]
  by_contra hne
  have h1 : ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (σ j) j = 0 :=
    h (show σ j ≠ j from fun e => hne (congrArg Fin.val e))
  rw [permGL_apply] at h1
  simp at h1

theorem eq_one_of_diagonal_mul_permGL {σ : Equiv.Perm (Fin 3)} {d : Fin 3 → K}
    (hd : Function.Injective d) (hd0 : ∀ i, d i ≠ 0) {μ : K}
    (h : diagonal d * ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      μ • (((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d))
    {k : Fin 3} (hk : σ k = k) : σ = 1 := by
  have key : ∀ j, d (σ j) = μ * d j := by
    intro j
    have h1 := congrFun (congrFun h (σ j)) j
    have hP : ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (σ j) j = 1 := by
      rw [permGL_apply]
      simp
    rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, hP, mul_one, one_mul,
      smul_eq_mul] at h1
    exact h1
  have hμ : μ = 1 := by
    have h1 := key k
    rw [hk] at h1
    have : (μ - 1) * d k = 0 := by linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (hd0 k))
  ext j
  rw [Equiv.Perm.one_apply]
  have h1 := key j
  rw [hμ, one_mul] at h1
  exact congrArg Fin.val (hd h1)

theorem commutator_permGL (σ : Equiv.Perm (Fin 3)) {D : GL (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (h3 : ∀ i j, (D : Matrix (Fin 3) (Fin 3) K) i i ^ 3 = (D : Matrix (Fin 3) (Fin 3) K) j j ^ 3) :
    ((permGL σ * D * (permGL σ)⁻¹ * D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧
      (permGL σ * D * (permGL σ)⁻¹ * D⁻¹ : GL (Fin 3) K) ^ 3 = 1 := by
  set d : Fin 3 → K := fun i => (D : Matrix (Fin 3) (Fin 3) K) i i with hd
  have hDd : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := hD.diagonal_diag.symm
  have hconj : ((permGL σ * D * (permGL σ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => d (σ⁻¹ i)) := by
    rw [Units.val_mul, Units.val_mul, hDd, permGL_mul_diagonal, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hC : ((permGL σ * D * (permGL σ)⁻¹ * D⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => d (σ⁻¹ i) * (d i)⁻¹) := by
    rw [Units.val_mul, hconj, coe_inv_of_isDiag hD, Matrix.diagonal_mul_diagonal]
  refine ⟨by rw [hC]; exact isDiag_diagonal _, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hC, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  have hd0 : d i ≠ 0 := apply_self_ne_zero_of_isDiag hD i
  simp only [Pi.pow_apply]
  rw [mul_pow, inv_pow, h3 (σ⁻¹ i) i, mul_inv_cancel₀ (pow_ne_zero 3 hd0)]

theorem exists_perm_of_isMonomialWith {G : GL (Fin 3) K} {σ : Fin 3 → Fin 3}
    (h : IsMonomialWith (G : Matrix (Fin 3) (Fin 3) K) σ) :
    ∃ π : Equiv.Perm (Fin 3),
      (((permGL π)⁻¹ * G : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  have hrow : ∀ j, ∃ i, (G : Matrix (Fin 3) (Fin 3) K) j i ≠ 0 := by
    intro j
    by_contra hall
    push Not at hall
    have h0 : (G : Matrix (Fin 3) (Fin 3) K).det = 0 := Matrix.det_eq_zero_of_row_eq_zero j hall
    exact (G.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero h0
  have hsurj : Function.Surjective σ := fun j => by
    obtain ⟨i, hi⟩ := hrow j
    exact ⟨i, ((h i j).mp hi).symm⟩
  have hbij : Function.Bijective σ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  set π := Equiv.ofBijective σ hbij with hπ
  refine ⟨π, ?_⟩
  have h1 : IsMonomialWith (((permGL π)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      ⇑(π⁻¹) := by
    rw [← map_inv]
    exact isMonomialWith_permGL π⁻¹
  have h2 := h1.mul h
  have hid : (⇑(π⁻¹) ∘ σ) = id := by
    funext i
    simp only [Function.comp_apply, id]
    rw [Equiv.Perm.inv_eq_iff_eq]
    rfl
  rw [hid] at h2
  rw [Units.val_mul]
  exact h2.isDiag

theorem nonempty_autIn_equiv_perm {H : Type} [Group H] {L A : Subgroup H}
    (Θ : Equiv.Perm (Fin 3) →* H) (hΘL : ∀ σ, Θ σ ∈ L)
    (hΘN : ∀ σ, ∀ a ∈ A, Θ σ * a * (Θ σ)⁻¹ ∈ A)
    (hinj : ∀ σ, (∀ a ∈ A, Θ σ * a = a * Θ σ) → σ = 1)
    (hsurj : ∀ l ∈ L, l ∈ Subgroup.normalizer (A : Set H) →
      ∃ σ, ∀ a ∈ A, l * a * l⁻¹ = Θ σ * a * (Θ σ)⁻¹) :
    Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)) := by
  have hN : ∀ σ, Θ σ ∈ Subgroup.normalizer (A : Set H) := by
    intro σ
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hΘN σ a, fun ha => ?_⟩
    have h1 := hΘN σ⁻¹ _ ha
    rw [map_inv, inv_inv] at h1
    have e : (Θ σ)⁻¹ * (Θ σ * a * (Θ σ)⁻¹) * Θ σ = a := by group
    rwa [e] at h1
  let Θ' : Equiv.Perm (Fin 3) →* Subgroup.normalizer (A : Set H) := Θ.codRestrict _ hN
  let φ : Equiv.Perm (Fin 3) →* autIn L A :=
    (A.normalizerMonoidHom.comp Θ').codRestrict (autIn L A) fun σ =>
      mem_autIn_iff.mpr ⟨Θ σ, hN σ, hΘL σ, rfl⟩
  have hφ : ∀ σ (a : A), (((φ σ : MulAut A) a : A) : H) = Θ σ * a * (Θ σ)⁻¹ := fun _ _ => rfl
  have hinj' : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply hinj σ
    intro a ha
    have h1 := congrArg (fun α : autIn L A => (((α : MulAut A) ⟨a, ha⟩ : A) : H)) hσ
    simp only [hφ] at h1
    change Θ σ * a * (Θ σ)⁻¹ = a at h1
    calc Θ σ * a = Θ σ * a * (Θ σ)⁻¹ * Θ σ := by group
      _ = a * Θ σ := by rw [h1]
  have hsurj' : Function.Surjective φ := by
    rintro ⟨α, hα⟩
    obtain ⟨l, hlN, hlL, rfl⟩ := mem_autIn_iff.mp hα
    obtain ⟨σ, hσ⟩ := hsurj l hlL hlN
    refine ⟨σ, Subtype.ext (MulEquiv.ext fun a => Subtype.ext ?_)⟩
    rw [hφ, normalizerMonoidHom_apply_coe]
    exact (hσ a a.2).symm
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj', hsurj'⟩).symm⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Frame

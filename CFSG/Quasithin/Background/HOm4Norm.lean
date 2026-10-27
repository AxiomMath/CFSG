module

public import CFSG.Quasithin.Background.HOm4Aut
public import CFSG.Quasithin.Background.HL3WrNorm

public section

namespace CFSG.Quasithin.H.Om4

open Matrix

variable {K : Type} [Field K]

abbrev VM (K : Type) [Field K] := Multiplicative (Matrix (Fin 2) (Fin 2) K)

@[expose] def addMap (ψ : MulAut (VM K)) : Matrix (Fin 2) (Fin 2) K →+
    Matrix (Fin 2) (Fin 2) K :=
  AddMonoidHom.toMultiplicative.symm ψ.toMonoidHom

theorem addMap_apply (ψ : MulAut (VM K)) (X : Matrix (Fin 2) (Fin 2) K) :
    addMap ψ X = Multiplicative.toAdd (ψ (Multiplicative.ofAdd X)) := rfl

@[expose] def lr (A B : GL (Fin 2) K) : MulAut (VM K) where
  toFun X := Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
    (B : Matrix (Fin 2) (Fin 2) K)ᵀ)
  invFun X := Multiplicative.ofAdd (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
    Multiplicative.toAdd X * ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ)
  left_inv X := by
    simp only [toAdd_ofAdd]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.mul_one, ofAdd_toAdd]
  right_inv X := by
    simp only [toAdd_ofAdd]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.mul_one, ofAdd_toAdd]
  map_mul' X Y := by
    simp only [toAdd_mul, Matrix.mul_add, Matrix.add_mul, ofAdd_add]

theorem toAdd_lr (A B : GL (Fin 2) K) (X : VM K) :
    Multiplicative.toAdd (lr A B X) = (A : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
      (B : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl

theorem lr_mul (A B A' B' : GL (Fin 2) K) : lr A B * lr A' B' = lr (A * A') (B * B') := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  rw [MulAut.mul_apply, toAdd_lr, toAdd_lr, toAdd_lr, Units.val_mul, Units.val_mul,
    Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc]

theorem lr_one : lr (1 : GL (Fin 2) K) 1 = 1 := by
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  rw [toAdd_lr, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    MulAut.one_apply]

@[expose] def trM : MulAut (VM K) where
  toFun X := Multiplicative.ofAdd (Multiplicative.toAdd X)ᵀ
  invFun X := Multiplicative.ofAdd (Multiplicative.toAdd X)ᵀ
  left_inv X := by simp
  right_inv X := by simp
  map_mul' X Y := by simp

theorem toAdd_trM (X : VM K) :
    Multiplicative.toAdd (trM X) = (Multiplicative.toAdd X)ᵀ := rfl

theorem trM_mul_self : (trM : MulAut (VM K)) * trM = 1 :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (by
    rw [MulAut.mul_apply, toAdd_trM, toAdd_trM, Matrix.transpose_transpose, MulAut.one_apply])

theorem trM_lr (A B : GL (Fin 2) K) : trM * lr A B = lr B A * trM :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (by
    rw [MulAut.mul_apply, MulAut.mul_apply, toAdd_trM, toAdd_lr, toAdd_lr, toAdd_trM,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc])

@[expose] def frM (τ : K ≃+* K) : MulAut (VM K) where
  toFun X := Multiplicative.ofAdd ((Multiplicative.toAdd X).map τ)
  invFun X := Multiplicative.ofAdd ((Multiplicative.toAdd X).map τ.symm)
  left_inv X := by
    simp only [toAdd_ofAdd, Matrix.map_map]
    ext i j
    simp
  right_inv X := by
    simp only [toAdd_ofAdd, Matrix.map_map]
    ext i j
    simp
  map_mul' X Y := by
    simp only [toAdd_mul]
    rw [← ofAdd_add]
    congr 1
    ext i j
    simp

theorem toAdd_frM (τ : K ≃+* K) (X : VM K) :
    Multiplicative.toAdd (frM τ X) = (Multiplicative.toAdd X).map τ := rfl

theorem frM_lr (τ : K ≃+* K) (A B : GL (Fin 2) K) :
    frM τ * lr A B = lr (GeneralLinearGroup.map τ.toRingHom A)
      (GeneralLinearGroup.map τ.toRingHom B) * frM τ :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (by
    rw [MulAut.mul_apply, MulAut.mul_apply, toAdd_frM, toAdd_lr, toAdd_lr, toAdd_frM]
    change ((A : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
      (B : Matrix (Fin 2) (Fin 2) K)ᵀ).map τ = (A : Matrix (Fin 2) (Fin 2) K).map τ *
        (Multiplicative.toAdd X).map τ * ((B : Matrix (Fin 2) (Fin 2) K).map τ)ᵀ
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map])

@[expose] def tv (i j : Fin 2) (hij : i ≠ j) (c : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

abbrev lg (g : SpecialLinearGroup (Fin 2) K) : MulAut (VM K) :=
  lr (Matrix.SpecialLinearGroup.toGL g) 1

theorem addMap_lg (g : SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    addMap (lg g) X = (g : Matrix (Fin 2) (Fin 2) K) * X := by
  rw [addMap_apply, toAdd_lr, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  rfl

theorem exists_eq_lr_one_of_commute {y : MulAut (VM K)}
    (h : ∀ g : SpecialLinearGroup (Fin 2) K, y * lg g = lg g * y) :
    ∃ B : GL (Fin 2) K, y = lr 1 B := by
  have key : ∀ y : MulAut (VM K), (∀ g : SpecialLinearGroup (Fin 2) K, y * lg g = lg g * y) →
      ∀ A X : Matrix (Fin 2) (Fin 2) K, addMap y (A * X) = A * addMap y X := by
    intro y h
    have hg : ∀ (g : SpecialLinearGroup (Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K),
        addMap y ((g : Matrix (Fin 2) (Fin 2) K) * X) = (g : Matrix (Fin 2) (Fin 2) K) *
          addMap y X := by
      intro g X
      have := congrArg (fun φ : MulAut (VM K) => Multiplicative.toAdd (φ (Multiplicative.ofAdd X)))
        (h g)
      simp only [MulAut.mul_apply] at this
      rw [← addMap_lg, ← addMap_lg]
      exact this
    have hs : ∀ (i j : Fin 2) (hij : i ≠ j) (c : K) (X : Matrix (Fin 2) (Fin 2) K),
        addMap y (Matrix.single i j c * X) = Matrix.single i j c * addMap y X := by
      intro i j hij c X
      have h1 := hg (tv i j hij c) X
      change addMap y (Matrix.transvection i j c * X) = Matrix.transvection i j c * addMap y X
        at h1
      rw [Matrix.transvection, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.one_mul,
        map_add] at h1
      exact add_left_cancel h1
    have hsingle : ∀ (i j : Fin 2) (c : K) (X : Matrix (Fin 2) (Fin 2) K),
        addMap y (Matrix.single i j c * X) = Matrix.single i j c * addMap y X := by
      intro i j c X
      by_cases hij : i = j
      · subst hij
        have hk : ∃ k : Fin 2, k ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
        obtain ⟨k, hk⟩ := hk
        have e : Matrix.single i i c = Matrix.single i k c * Matrix.single k i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [e, Matrix.mul_assoc, hs i k (Ne.symm hk) c, hs k i hk 1, Matrix.mul_assoc]
      · exact hs i j hij c X
    intro A X
    rw [Matrix.matrix_eq_sum_single A, Matrix.sum_mul, map_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.sum_mul, map_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hsingle i j _ X
  have hy := key y h
  have hyi := key y⁻¹ fun g => (Commute.inv_left (h g)).eq
  set Y := addMap y 1 with hY
  set Z := addMap y⁻¹ 1 with hZ
  have hy' : ∀ X, addMap y X = X * Y := fun X => by
    rw [hY, ← hy X 1, Matrix.mul_one]
  have hyi' : ∀ X, addMap y⁻¹ X = X * Z := fun X => by
    rw [hZ, ← hyi X 1, Matrix.mul_one]
  have hYZ : Z * Y = 1 := by
    have h1 : addMap y (addMap y⁻¹ 1) = 1 := by
      rw [addMap_apply, addMap_apply, ofAdd_toAdd, ← MulAut.mul_apply, mul_inv_cancel,
        MulAut.one_apply, toAdd_ofAdd]
    rw [hyi', hy', Matrix.one_mul] at h1
    exact h1
  have hZY : Y * Z = 1 := by
    have h1 : addMap y⁻¹ (addMap y 1) = 1 := by
      rw [addMap_apply, addMap_apply, ofAdd_toAdd, ← MulAut.mul_apply, inv_mul_cancel,
        MulAut.one_apply, toAdd_ofAdd]
    rw [hy', hyi', Matrix.one_mul] at h1
    exact h1
  refine ⟨⟨Yᵀ, Zᵀ, by rw [← Matrix.transpose_mul, hYZ, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hZY, Matrix.transpose_one]⟩, ?_⟩
  refine MulEquiv.ext fun X => Multiplicative.toAdd.injective ?_
  rw [toAdd_lr, Units.val_one, Matrix.one_mul]
  change addMap y (Multiplicative.toAdd X) = _
  rw [hy']
  rfl

theorem exists_mulAut_of_mem_normalizer {Γ H : Type*} [Group Γ] [Group H] {ρ : Γ →* H}
    (hρ : Function.Injective ρ) {x : H} (hx : x ∈ Subgroup.normalizer (ρ.range : Set H)) :
    ∃ α : MulAut Γ, ∀ γ, ρ (α γ) = x * ρ γ * x⁻¹ := by
  let e : Γ ≃* ρ.range := MonoidHom.ofInjective hρ
  let c : MulAut ρ.range := ρ.range.normalizerMonoidHom ⟨x, hx⟩
  refine ⟨e.trans (c.trans e.symm), fun γ => ?_⟩
  have h1 : ρ ((e.trans (c.trans e.symm)) γ) = ((e (e.symm (c (e γ))) : ρ.range) : H) := rfl
  rw [h1, MulEquiv.apply_symm_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe ρ.range ⟨x, hx⟩ (e γ)

theorem lg_mul (g g' : SpecialLinearGroup (Fin 2) K) : lg (g * g') = lg g * lg g' := by
  rw [lg, lg, lg, lr_mul, map_mul, mul_one]

theorem lg_one : lg (1 : SpecialLinearGroup (Fin 2) K) = 1 := by
  rw [lg, map_one, lr_one]

theorem lr_inv (A B : GL (Fin 2) K) : (lr A B)⁻¹ = lr A⁻¹ B⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, lr_mul, mul_inv_cancel, mul_inv_cancel, lr_one]

theorem lg_injective [CharP K 2] : Function.Injective (lg (K := K)) := by
  intro g g' h
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) * X = (g' : Matrix (Fin 2) (Fin 2) K) * X := by
    intro X
    have := congrArg (fun φ : MulAut (VM K) => Multiplicative.toAdd (φ (Multiplicative.ofAdd X))) h
    simpa [toAdd_lr] using this
  have := key 1
  rw [Matrix.mul_one, Matrix.mul_one] at this
  exact Subtype.ext this

@[expose] noncomputable def rho : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K →*
    MulAut (VM K) where
  toFun γ := lr (Matrix.SpecialLinearGroup.toGL γ.1) (Matrix.SpecialLinearGroup.toGL γ.2)
  map_one' := by rw [Prod.fst_one, Prod.snd_one, map_one, lr_one]
  map_mul' γ δ := by rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, lr_mul]

theorem rho_apply (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) :
    rho γ = lr (Matrix.SpecialLinearGroup.toGL γ.1) (Matrix.SpecialLinearGroup.toGL γ.2) := rfl

theorem rho_injective [CharP K 2] : Function.Injective (rho (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, h⟩ hγ
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) * X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
    intro X
    have := congrArg (fun φ : MulAut (VM K) => Multiplicative.toAdd (φ (Multiplicative.ofAdd X)))
      hγ
    simpa [rho_apply, toAdd_lr] using this
  have hinv : (h : Matrix (Fin 2) (Fin 2) K)ᵀ = ((g⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) := by
    have h1 := key 1
    rw [Matrix.mul_one] at h1
    calc (h : Matrix (Fin 2) (Fin 2) K)ᵀ
        = ((g⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
          rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) K, Commute X (g : Matrix (Fin 2) (Fin 2) K) := by
    intro X
    have h1 := key X
    rw [hinv] at h1
    calc X * (g : Matrix (Fin 2) (Fin 2) K)
        = (g : Matrix (Fin 2) (Fin 2) K) * X * ((g⁻¹ : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := by rw [h1]
      _ = (g : Matrix (Fin 2) (Fin 2) K) * X := by
          rw [Matrix.mul_assoc _ _ (g : Matrix (Fin 2) (Fin 2) K),
            ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : c * c = 1 := by
    have := g.2
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at this
    exact this
  have hc1 : c = 1 := by
    have h3 : (c + 1) * (c + 1) = 0 := by linear_combination hdet + (c + 1) * h2
    linear_combination mul_self_eq_zero.mp h3 - h2
  have hg1 : g = 1 := Subtype.ext (by rw [← hc, hc1, map_one]; rfl)
  have hh1 : h = 1 := by
    rw [hg1, inv_one, Matrix.SpecialLinearGroup.coe_one] at hinv
    exact Subtype.ext (by
      rw [← Matrix.transpose_transpose (h : Matrix (Fin 2) (Fin 2) K), hinv,
        Matrix.transpose_one]
      rfl)
  rw [hg1, hh1]
  rfl

variable [Finite K] [CharP K 2]

theorem exists_eq_of_preserves {x : MulAut (VM K)}
    (hx : ∀ g : SpecialLinearGroup (Fin 2) K, ∃ g' : SpecialLinearGroup (Fin 2) K,
      x * lg g * x⁻¹ = lg g') :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), x = lr A B * frM τ := by
  classical
  have : Finite (SpecialLinearGroup (Fin 2) K) := inferInstance
  choose f hf using hx
  have hfmul : ∀ g g', f (g * g') = f g * f g' := by
    intro g g'
    apply lg_injective
    rw [← hf, lg_mul, lg_mul, ← hf, ← hf]
    group
  have hfinj : Function.Injective f := by
    intro g g' h
    apply lg_injective
    have h1 := hf g
    rw [h, ← hf g'] at h1
    have h2 := congrArg (fun φ => x⁻¹ * φ * x) h1
    simpa [mul_assoc] using h2
  let α : MulAut (SpecialLinearGroup (Fin 2) K) :=
    MulEquiv.ofBijective (MonoidHom.mk' f hfmul) ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  obtain ⟨G, τ, hG⟩ := exists_eq_conj_map α
  have hz : ∀ g, (lr G 1 * frM τ) * lg g * (lr G 1 * frM τ)⁻¹ = lg (f g) := by
    intro g
    have h1 : Matrix.SpecialLinearGroup.toGL (f g) =
        G * GeneralLinearGroup.map τ.toRingHom (Matrix.SpecialLinearGroup.toGL g) * G⁻¹ :=
      Units.ext (hG g)
    simp only [lg]
    rw [h1, _root_.mul_inv_rev, lr_inv, mul_assoc, mul_assoc, ← mul_assoc (frM τ), frM_lr,
      map_one, mul_assoc, mul_inv_cancel_left, lr_mul, lr_mul, inv_one, mul_one, mul_one,
      mul_assoc]
  obtain ⟨B, hB⟩ := exists_eq_lr_one_of_commute (y := (lr G 1 * frM τ)⁻¹ * x) fun g => by
    have e1 : x * lg g = lg (f g) * x := by rw [← hf g]; group
    have e2 : (lr G 1 * frM τ)⁻¹ * lg (f g) = lg g * (lr G 1 * frM τ)⁻¹ := by rw [← hz g]; group
    rw [mul_assoc, e1, ← mul_assoc, e2, mul_assoc]
  refine ⟨G, GeneralLinearGroup.map τ.toRingHom B, τ, ?_⟩
  have hx : x = lr G 1 * frM τ * lr 1 B := by rw [← hB]; group
  rw [hx, mul_assoc, frM_lr, map_one, ← mul_assoc, lr_mul, mul_one, one_mul]

theorem exists_eq_of_mem_normalizer (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)}
    (hx : x ∈ Subgroup.normalizer ((rho (K := K)).range : Set (MulAut (VM K)))) :
    ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), x = lr A B * frM τ ∨ x = lr A B * frM τ * trM := by
  classical
  have : Finite (SpecialLinearGroup (Fin 2) K) := inferInstance
  obtain ⟨α, hα⟩ := exists_mulAut_of_mem_normalizer rho_injective hx
  have hs := sl2_isSimple (K := K) h4
  have hp := sl2_commutator_eq_top (K := K) h4
  have hfst : ∀ (N : Subgroup (SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K))
      (γ : SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K), γ ∈ N →
      N.map α.toMonoidHom = (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)).prod ⊥ →
      x * rho γ * x⁻¹ = lg (α γ).1 := by
    intro N γ hγ hN
    have hmem : α γ ∈ N.map α.toMonoidHom := ⟨γ, hγ, rfl⟩
    rw [hN] at hmem
    have h2 : (α γ).2 = 1 := Subgroup.mem_bot.mp hmem.2
    rw [← hα, rho_apply, h2, map_one]
  rcases H.L3Wr.map_prod_eq_or hs hp α with h1 | h1
  · obtain ⟨A, B, τ, hx'⟩ := exists_eq_of_preserves (x := x) fun g =>
      ⟨(α (g, 1)).1, by
        rw [← hfst _ (g, 1) (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top g, Subgroup.mem_bot.mpr rfl⟩)
          h1, rho_apply, map_one]⟩
    exact ⟨A, B, τ, Or.inl hx'⟩
  · have h1' : ((⊥ : Subgroup (SpecialLinearGroup (Fin 2) K)).prod ⊤).map α.toMonoidHom =
        (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)).prod ⊥ := by
      rcases H.L3Wr.map_prod_eq_or' hs hp α with h | h
      · exact h
      · exfalso
        have h3 := Subgroup.map_injective α.injective (h.trans h1.symm)
        have hmem : ((tv 0 1 (by decide) (1 : K)), (1 : SpecialLinearGroup (Fin 2) K)) ∈
            (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K)).prod ⊥ :=
          Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
        rw [← h3] at hmem
        have h4' := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).1
        have h5 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
          (g : Matrix (Fin 2) (Fin 2) K) 0 1) h4'
        simp [tv, Matrix.transvection] at h5
    obtain ⟨A, B, τ, hx'⟩ := exists_eq_of_preserves (x := x * trM) fun g =>
      ⟨(α (1, g)).1, by
        have h2 := hfst _ (1, g)
          (Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top g⟩) h1'
        rw [rho_apply, map_one] at h2
        rw [← h2]
        have htinv : (trM : MulAut (VM K))⁻¹ = trM := inv_eq_of_mul_eq_one_right trM_mul_self
        have e1 : trM * lg g * trM⁻¹ = lr 1 (Matrix.SpecialLinearGroup.toGL g) := by
          rw [lg, trM_lr, mul_assoc, mul_inv_cancel, mul_one]
        calc x * trM * lg g * (x * trM)⁻¹ = x * (trM * lg g * trM⁻¹) * x⁻¹ := by group
          _ = _ := by rw [e1]⟩
    refine ⟨A, B, τ, Or.inr ?_⟩
    rw [← hx', mul_assoc, trM_mul_self, mul_one]

end CFSG.Quasithin.H.Om4

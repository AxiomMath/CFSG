module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aComm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aInvol
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTensor
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace B42SL3

open CFSG.QuasithinUnique.Setup.X7a Matrix
open scoped MatrixGroups Matrix

section Involutions

variable {F : Type} [Field F] [CharP F 2]

theorem isTransvection_of_involution {t : SL(3, F)} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    CFSG.QuasithinUnique.Setup.X7a.IsTransvection t := by
  obtain ⟨g, hg⟩ := exists_conj_transvection t ht1 ht2
  have h := isTransvection_conj (isTransvection_up3 (one_ne_zero : (1 : F) ≠ 0))
    (Matrix.SpecialLinearGroup.toGL g)
  have heq : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F
      (Matrix.SpecialLinearGroup.toGL g) (up3 0 0 1) = t := by
    apply Subtype.ext
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    change (g : Matrix (Fin 3) (Fin 3) F) * ((up3 0 0 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = t
    rw [← hg, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    exact congrArg _ (by group)
  rwa [heq] at h

theorem trace_eq_one_of_isTransvection {t : SL(3, F)}
    (ht : CFSG.QuasithinUnique.Setup.X7a.IsTransvection t) :
    (t : Matrix (Fin 3) (Fin 3) F).trace = 1 := by
  obtain ⟨v, w, -, -, hwv, htm⟩ := ht
  rw [htm, Matrix.trace_add, Matrix.trace_one, Matrix.trace_vecMulVec, dotProduct_comm, hwv,
    add_zero, Fintype.card_fin]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  norm_num
  linear_combination h2

theorem commute_of_rep {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) SL(3, F) U)
    (hker : ∀ x : SL(3, F), ρ x = 1 →
      x ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F)
    {t t' : SL(3, F)} (ht' : CFSG.QuasithinUnique.Setup.X7a.IsTransvection t')
    (hcomm : ρ t * ρ t' = ρ t' * ρ t) : t * t' = t' * t := by
  set z := t * t' * (t' * t)⁻¹ with hz
  have hz1 : ρ z = 1 := by
    rw [hz, map_mul, show ρ (t * t') = ρ (t' * t) by rw [map_mul, map_mul, hcomm], ← map_mul,
      mul_inv_cancel, map_one]
  obtain ⟨c, -, hcz⟩ := hker z hz1
  have hconj : t * t' * t⁻¹ = z * t' := by
    rw [hz]
    group
  have htr := congrArg (fun s : SL(3, F) => (s : Matrix (Fin 3) (Fin 3) F).trace) hconj
  simp only [Matrix.SpecialLinearGroup.coe_mul] at htr
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, hcz, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, trace_eq_one_of_isTransvection ht',
    smul_eq_mul, mul_one] at htr
  have hc1 : (c : F) = 1 := htr.symm
  have hz' : z = 1 := by
    apply Subtype.ext
    rw [hcz, hc1, map_one]
    rfl
  rw [hz] at hz'
  exact mul_inv_eq_one.mp hz'

omit [CharP F 2] in
theorem vecMulVec_mulVec_eq (u v w : Fin 3 → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [CharP F 2] in
theorem sub_one_mul_sub_one_eq_zero {t t' : SL(3, F)}
    (ht : CFSG.QuasithinUnique.Setup.X7a.IsTransvection t)
    (ht' : CFSG.QuasithinUnique.Setup.X7a.IsTransvection t') (hcomm : t * t' = t' * t) :
    ((t : Matrix (Fin 3) (Fin 3) F) - 1) * ((t' : Matrix (Fin 3) (Fin 3) F) - 1) = 0 := by
  obtain ⟨v, w, hv, -, hwv, htm⟩ := ht
  obtain ⟨v', w', -, -, hwv', htm'⟩ := ht'
  rw [htm, htm', add_sub_cancel_left, add_sub_cancel_left, vecMulVec_mul_vecMulVec]
  have hc : vecMulVec v w * vecMulVec v' w' = vecMulVec v' w' * vecMulVec v w := by
    have := congrArg (fun s : SL(3, F) => (s : Matrix (Fin 3) (Fin 3) F)) hcomm
    simp only [Matrix.SpecialLinearGroup.coe_mul, htm, htm'] at this
    have e : ∀ X Y : Matrix (Fin 3) (Fin 3) F, (1 + X) * (1 + Y) = 1 + X + Y + X * Y := by
      intro X Y
      noncomm_ring
    rw [e, e, add_assoc, add_assoc, add_assoc, add_assoc, add_right_inj, ← add_assoc,
      ← add_assoc, add_comm (vecMulVec v' w') (vecMulVec v w), add_right_inj] at this
    exact this
  rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec] at hc
  have h1 := congrArg (fun M => M *ᵥ v) hc
  simp only [vecMulVec_mulVec_eq, smul_dotProduct, hwv, smul_eq_mul, mul_zero, zero_smul] at h1
  rcases smul_eq_zero.mp h1 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [h3, zero_smul, vecMulVec_zero]
    · rw [hc, h3, zero_smul, vecMulVec_zero]
  · exact absurd h2 hv

end Involutions

section Kron

variable {F : Type} [Field F] [CharP F 2] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [CharP F 2] in
theorem locDim_pos (α β : Bool) : 0 < locDim α β := by
  cases α <;> cases β <;> decide

omit [CharP F 2] in
theorem subsingleton_of_trivial {ℓ : Bool × Bool} (hℓ : ℓ = (false, false)) :
    Subsingleton (Fin (locDim ℓ.1 ℓ.2)) := by
  subst hℓ
  show Subsingleton (Fin 1)
  infer_instance

theorem locRep_trivial_apply {ℓ : Bool × Bool} (hℓ : ℓ = (false, false)) (j : ℕ) (g : SL(3, F))
    (x y : Fin (locDim ℓ.1 ℓ.2)) : locRep F ℓ.1 ℓ.2 j g x y = 1 := by
  subst hℓ
  have hxy : x = y := (subsingleton_of_trivial rfl).elim x y
  subst hxy
  show (1 : Matrix (Fin 1) (Fin 1) F) x x = 1
  exact Matrix.one_apply_eq x

variable (τ : ι → Bool × Bool) (e : ι → ℕ) {i i' : ι}

theorem tensorRepGen_apply_two (hii' : i ≠ i')
    (hrest : ∀ p, p ≠ i → p ≠ i' → τ p = (false, false)) (g : SL(3, F))
    (y z : ∀ p, Fin (locDim (τ p).1 (τ p).2)) :
    tensorRepGen F τ e g y z = locRep F (τ i).1 (τ i).2 (e i) g (y i) (z i) *
      locRep F (τ i').1 (τ i').2 (e i') g (y i') (z i') := by
  rw [tensorRepGen_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _
      (Finset.mem_erase.mpr ⟨hii'.symm, Finset.mem_univ i'⟩)]
  rw [Finset.prod_eq_one, mul_one]
  intro p hp
  obtain ⟨hpi', hp'⟩ := Finset.mem_erase.mp hp
  obtain ⟨hpi, -⟩ := Finset.mem_erase.mp hp'
  exact locRep_trivial_apply (hrest p hpi hpi') (e p) g (y p) (z p)

omit [CharP F 2] in
theorem one_apply_two (hrest : ∀ p, p ≠ i → p ≠ i' → τ p = (false, false))
    (y z : ∀ p, Fin (locDim (τ p).1 (τ p).2)) :
    (1 : Matrix (∀ p, Fin (locDim (τ p).1 (τ p).2)) (∀ p, Fin (locDim (τ p).1 (τ p).2)) F) y z =
      (1 : Matrix (Fin (locDim (τ i).1 (τ i).2)) (Fin (locDim (τ i).1 (τ i).2)) F) (y i) (z i) *
      (1 : Matrix (Fin (locDim (τ i').1 (τ i').2)) (Fin (locDim (τ i').1 (τ i').2)) F)
        (y i') (z i') := by
  classical
  have hiff : y = z ↔ y i = z i ∧ y i' = z i' := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext p
      by_cases hpi : p = i
      · subst hpi
        exact h1
      by_cases hpi' : p = i'
      · subst hpi'
        exact h2
      have := subsingleton_of_trivial (hrest p hpi hpi')
      exact Subsingleton.elim _ _
  simp only [Matrix.one_apply]
  by_cases h1 : y i = z i <;> by_cases h2 : y i' = z i' <;> simp [hiff, h1, h2]

omit [CharP F 2] [DecidableEq ι] [Fintype ι] in
theorem exists_idx_two [DecidableEq ι] (hii' : i ≠ i') (c : Fin (locDim (τ i).1 (τ i).2))
    (c' : Fin (locDim (τ i').1 (τ i').2)) :
    ∃ y : ∀ p, Fin (locDim (τ p).1 (τ p).2), y i = c ∧ y i' = c' := by
  let y₀ : ∀ p, Fin (locDim (τ p).1 (τ p).2) := fun p => ⟨0, locDim_pos _ _⟩
  refine ⟨Function.update (Function.update y₀ i c) i' c', ?_, Function.update_self _ _ _⟩
  rw [Function.update_of_ne hii', Function.update_self]

theorem quadratic_entries (hii' : i ≠ i')
    (hrest : ∀ p, p ≠ i → p ≠ i' → τ p = (false, false)) {t₁ t₂ : SL(3, F)}
    (hMi : (locRep F (τ i).1 (τ i).2 (e i) t₂ - 1) * (locRep F (τ i).1 (τ i).2 (e i) t₁ - 1) = 0)
    (hMi' : (locRep F (τ i').1 (τ i').2 (e i') t₂ - 1) *
      (locRep F (τ i').1 (τ i').2 (e i') t₁ - 1) = 0)
    (hquad : (tensorRepGen F τ e t₂ - 1) * (tensorRepGen F τ e t₁ - 1) = 0)
    (c d : Fin (locDim (τ i).1 (τ i).2)) (c' d' : Fin (locDim (τ i').1 (τ i').2)) :
    (locRep F (τ i).1 (τ i).2 (e i) t₁ - 1) c d *
        (locRep F (τ i').1 (τ i').2 (e i') t₂ - 1) c' d' +
      (locRep F (τ i).1 (τ i).2 (e i) t₂ - 1) c d *
        (locRep F (τ i').1 (τ i').2 (e i') t₁ - 1) c' d' = 0 := by
  obtain ⟨y, hyi, hyi'⟩ := exists_idx_two τ hii' c c'
  obtain ⟨z, hzi, hzi'⟩ := exists_idx_two τ hii' d d'
  have hexp : (tensorRepGen F τ e t₂ - 1) * (tensorRepGen F τ e t₁ - 1) =
      tensorRepGen F τ e (t₂ * t₁) - tensorRepGen F τ e t₂ - tensorRepGen F τ e t₁ + 1 := by
    rw [map_mul]
    noncomm_ring
  have hL : ∀ (M₁ M₂ : Matrix (Fin (locDim (τ i).1 (τ i).2)) (Fin (locDim (τ i).1 (τ i).2)) F),
      (M₂ - 1) * (M₁ - 1) = 0 → M₂ * M₁ = 1 + (M₁ - 1) + (M₂ - 1) := by
    intro M₁ M₂ h
    have : M₂ * M₁ = (M₂ - 1) * (M₁ - 1) + 1 + (M₁ - 1) + (M₂ - 1) := by noncomm_ring
    rw [this, h, zero_add]
  have hL' : ∀ (M₁ M₂ : Matrix (Fin (locDim (τ i').1 (τ i').2))
      (Fin (locDim (τ i').1 (τ i').2)) F),
      (M₂ - 1) * (M₁ - 1) = 0 → M₂ * M₁ = 1 + (M₁ - 1) + (M₂ - 1) := by
    intro M₁ M₂ h
    have : M₂ * M₁ = (M₂ - 1) * (M₁ - 1) + 1 + (M₁ - 1) + (M₂ - 1) := by noncomm_ring
    rw [this, h, zero_add]
  have h0 := congrFun (congrFun hquad y) z
  rw [hexp] at h0
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply] at h0
  rw [tensorRepGen_apply_two τ e hii' hrest, tensorRepGen_apply_two τ e hii' hrest,
    tensorRepGen_apply_two τ e hii' hrest, one_apply_two τ hrest, map_mul, map_mul,
    hL _ _ hMi, hL' _ _ hMi', hyi, hyi', hzi, hzi'] at h0
  simp only [Matrix.add_apply, Matrix.sub_apply] at h0 ⊢
  linear_combination h0

end Kron

section Single

variable {F : Type} [Field F] [CharP F 2]

@[expose] def IsSingle (ℓ : Bool × Bool) : Prop := ℓ = (true, false) ∨ ℓ = (false, true)

theorem frK_injective (j : ℕ) : Function.Injective (frK F j : F →+* F) :=
  fun _ _ h => (frK (F := F) F j).injective h

theorem mapMatrix_sub_one (j : ℕ) (g : SL(3, F)) :
    twistMat F j g - 1 = (frK F j).mapMatrix ((g : Matrix (Fin 3) (Fin 3) F) - 1) := by
  rw [map_sub, map_one]
  rfl

theorem dual_sub_one (j : ℕ) {t : SL(3, F)} (ht : t * t = 1) :
    (twistMat F j t⁻¹)ᵀ - 1 = ((frK F j).mapMatrix ((t : Matrix (Fin 3) (Fin 3) F) - 1))ᵀ := by
  rw [inv_eq_of_mul_eq_one_right ht, ← mapMatrix_sub_one, Matrix.transpose_sub,
    Matrix.transpose_one]

theorem locRep_sub_one_mul {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) (j : ℕ) {t₁ t₂ : SL(3, F)}
    (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1) (hcomm : t₁ * t₂ = t₂ * t₁) :
    (locRep F ℓ.1 ℓ.2 j t₂ - 1) * (locRep F ℓ.1 ℓ.2 j t₁ - 1) = 0 := by
  have hzero : ∀ {s s' : SL(3, F)}, s * s = 1 → s' * s' = 1 → s * s' = s' * s →
      ((s : Matrix (Fin 3) (Fin 3) F) - 1) * ((s' : Matrix (Fin 3) (Fin 3) F) - 1) = 0 := by
    intro s s' hs hs' hss'
    by_cases hs1 : s = 1
    · subst hs1
      simp
    by_cases hs1' : s' = 1
    · subst hs1'
      simp
    exact sub_one_mul_sub_one_eq_zero (isTransvection_of_involution hs1 hs)
      (isTransvection_of_involution hs1' hs') hss'
  rcases hℓ with rfl | rfl
  · show (twistMat F j t₂ - 1) * (twistMat F j t₁ - 1) = 0
    rw [mapMatrix_sub_one, mapMatrix_sub_one, ← map_mul, hzero h2 h1 hcomm.symm, map_zero]
  · show ((twistMat F j t₂⁻¹)ᵀ - 1) * ((twistMat F j t₁⁻¹)ᵀ - 1) = 0
    rw [dual_sub_one j h1, dual_sub_one j h2, ← Matrix.transpose_mul, ← map_mul,
      hzero h1 h2 hcomm, map_zero, Matrix.transpose_zero]

theorem locRep_sub_one_ne_zero {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) (j : ℕ) {t : SL(3, F)}
    (ht1 : t ≠ 1) (ht : t * t = 1) : locRep F ℓ.1 ℓ.2 j t - 1 ≠ 0 := by
  have hne : (t : Matrix (Fin 3) (Fin 3) F) - 1 ≠ 0 := by
    intro h
    apply ht1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.mp h
  have hmap : (frK F j).mapMatrix ((t : Matrix (Fin 3) (Fin 3) F) - 1) ≠ 0 := by
    intro h
    apply hne
    ext a b
    have := congrFun (congrFun h a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] at this
    exact (map_eq_zero_iff _ (frK_injective j)).mp this
  rcases hℓ with rfl | rfl
  · show twistMat F j t - 1 ≠ 0
    rw [mapMatrix_sub_one]
    exact hmap
  · show (twistMat F j t⁻¹)ᵀ - 1 ≠ 0
    rw [dual_sub_one j ht]
    intro h
    exact hmap (Matrix.transpose_eq_zero.mp h)

theorem exists_smul_of_locRep {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) (j : ℕ) {t₁ t₂ : SL(3, F)}
    (ht1 : t₁ ≠ 1) (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1) {lam : F}
    (h : locRep F ℓ.1 ℓ.2 j t₂ - 1 = lam • (locRep F ℓ.1 ℓ.2 j t₁ - 1)) :
    ∃ μ : F, (t₂ : Matrix (Fin 3) (Fin 3) F) - 1 = μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1) := by
  set E₁ := (t₁ : Matrix (Fin 3) (Fin 3) F) - 1 with hE₁
  set E₂ := (t₂ : Matrix (Fin 3) (Fin 3) F) - 1 with hE₂
  have hent : ∀ a b, frK F j (E₂ a b) = lam * frK F j (E₁ a b) := by
    rcases hℓ with rfl | rfl
    · intro a b
      have h' : (frK F j).mapMatrix E₂ = lam • (frK F j).mapMatrix E₁ := by
        rw [← mapMatrix_sub_one, ← mapMatrix_sub_one]
        exact h
      have := congrFun (congrFun h' a) b
      simpa using this
    · intro a b
      have h' : ((frK F j).mapMatrix E₂)ᵀ = lam • ((frK F j).mapMatrix E₁)ᵀ := by
        rw [← dual_sub_one j h1, ← dual_sub_one j h2]
        exact h
      have := congrFun (congrFun h' b) a
      simpa using this
  have hne : E₁ ≠ 0 := by
    intro h0
    apply ht1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact sub_eq_zero.mp h0
  obtain ⟨c, d, hcd⟩ : ∃ c d, E₁ c d ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (Matrix.ext hcon)
  refine ⟨E₂ c d / E₁ c d, ?_⟩
  have hlam : lam = frK F j (E₂ c d / E₁ c d) := by
    have hfc : frK F j (E₁ c d) ≠ 0 := (map_ne_zero_iff _ (frK_injective j)).mpr hcd
    rw [map_div₀, hent c d, mul_div_assoc, div_self hfc, mul_one]
  ext a b
  apply frK_injective j
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, hent a b, hlam]

end Single

section Quadratic

variable {F : Type} [Field F] [CharP F 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_smul_of_quadratic (τ : ι → Bool × Bool) (e : ι → ℕ) {i i' : ι} (hii' : i ≠ i')
    (hτi : IsSingle (τ i)) (hτi' : IsSingle (τ i'))
    (hrest : ∀ p, p ≠ i → p ≠ i' → τ p = (false, false)) {t₁ t₂ : SL(3, F)} (ht1 : t₁ ≠ 1)
    (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1) (hcomm : t₁ * t₂ = t₂ * t₁)
    (hquad : (tensorRepGen F τ e t₂ - 1) * (tensorRepGen F τ e t₁ - 1) = 0) :
    ∃ μ : F, (t₂ : Matrix (Fin 3) (Fin 3) F) - 1 = μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1) := by
  classical
  have hent := quadratic_entries τ e hii' hrest (locRep_sub_one_mul hτi (e i) h1 h2 hcomm)
    (locRep_sub_one_mul hτi' (e i') h1 h2 hcomm) hquad
  have hne := locRep_sub_one_ne_zero hτi' (e i') ht1 h1
  obtain ⟨c', d', hcd⟩ : ∃ c' d', (locRep F (τ i').1 (τ i').2 (e i') t₁ - 1) c' d' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (Matrix.ext hcon)
  set lam : F := -((locRep F (τ i').1 (τ i').2 (e i') t₂ - 1) c' d') /
    (locRep F (τ i').1 (τ i').2 (e i') t₁ - 1) c' d' with hlam
  refine exists_smul_of_locRep hτi (e i) ht1 h1 h2 (lam := lam) ?_
  ext c d
  have h := hent c d c' d'
  rw [Matrix.smul_apply, smul_eq_mul, hlam]
  field_simp
  linear_combination h

end Quadratic

end B42SL3

end CFSG.Quasithin

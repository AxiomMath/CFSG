module

public import CFSG.Quasithin.Vol2.Ch11SecB414D

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.QuasithinUnique.Setup.X7a
open scoped Matrix

variable {F : Type} [Field F] [CharP F 2] {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

noncomputable abbrev adG (g : GL (Fin 3) F) : (Fin 8 → F) →ₗ[F] (Fin 8 → F) :=
  adjAd F (g : Matrix (Fin 3) (Fin 3) F) ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem adG_mul (g h : GL (Fin 3) F) (v : Fin 8 → F) : adG (g * h) v = adG g (adG h v) := by
  rw [adG, adG, adG, adjAd_comp F _ _ _ _ (by rw [← Units.val_mul, inv_mul_cancel,
    Units.val_one]), mul_inv_rev, Units.val_mul, Units.val_mul]

omit [CharP F 2] in
theorem adG_one (v : Fin 8 → F) : adG (1 : GL (Fin 3) F) v = v := by
  rw [adG, inv_one, Units.val_one, adjAd_one]

theorem adG_inv_adG (g : GL (Fin 3) F) (v : Fin 8 → F) : adG g⁻¹ (adG g v) = v := by
  rw [← adG_mul, inv_mul_cancel, adG_one]

section Diag

variable [Fintype F]

theorem pow_three_eq_one (hF : Fintype.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ω ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hωω := sq_eq_add_one hF h0 h1
  linear_combination (ω + 1) * hωω + ω * h2

theorem exists_pow_eq (hF : Fintype.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) {u : F}
    (hu : u ≠ 0) : ∃ i < 3, u = ω ^ i := by
  rcases mem_four hF h0 h1 u with h | h | h | h
  · exact absurd h hu
  · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
  · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
  · exact ⟨2, by norm_num, by rw [h, sq, sq_eq_add_one hF h0 h1]⟩

@[expose] noncomputable def dGL (ω : F) (h0 : ω ≠ 0) : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![ω, 1, 1]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h0)

omit [CharP F 2] [Fintype F] in
theorem dGL_val (ω : F) (h0 : ω ≠ 0) :
    ((dGL ω h0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![ω, 1, 1] := rfl

omit [CharP F 2] [Fintype F] in
theorem det_dGL_pow (ω : F) (h0 : ω ≠ 0) (i : ℕ) :
    ((dGL ω h0 ^ i : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = ω ^ i := by
  rw [Units.val_pow_eq_pow_val, Matrix.det_pow, dGL_val, Matrix.det_diagonal,
    Fin.prod_univ_three]
  simp

theorem dGL_pow_three (hF : Fintype.card F = 4) {ω : F} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    dGL ω h0 ^ 3 = 1 := by
  have hω3 := pow_three_eq_one hF h0 h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, dGL_val, Matrix.diagonal_pow, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hω3]

end Diag

section Proj

variable (ρ : Representation (ZMod 2) (GL (Fin 3) F) U) (Φ₀ : (Fin 8 → F) →+ U)
  {ω : F} (h0 : ω ≠ 0)

@[expose] noncomputable def termD (i : ℕ) (c' : F) : (Fin 8 → F) →+ U where
  toFun v := ρ (dGL ω h0 ^ i) (Φ₀ (adG (dGL ω h0 ^ i)⁻¹ (c' • v)))
  map_zero' := by rw [smul_zero, map_zero, map_zero, map_zero]
  map_add' v w := by rw [smul_add, map_add, map_add, map_add]

omit [CharP F 2] in
theorem termD_apply (i : ℕ) (c' : F) (v : Fin 8 → F) :
    termD ρ Φ₀ h0 i c' v = ρ (dGL ω h0 ^ i) (Φ₀ (adG (dGL ω h0 ^ i)⁻¹ (c' • v))) := rfl

omit [CharP F 2] in
theorem termD_zero_one (v : Fin 8 → F) : termD ρ Φ₀ h0 0 1 v = Φ₀ v := by
  rw [termD_apply, pow_zero, inv_one, one_smul, adG_one, map_one, Module.End.one_apply]

omit [CharP F 2] in
theorem termD_smul (i : ℕ) (a b : F) (v : Fin 8 → F) :
    termD ρ Φ₀ h0 i a (b • v) = termD ρ Φ₀ h0 i (a * b) v := by
  rw [termD_apply, termD_apply, smul_smul]

omit [CharP F 2] in
theorem termD_add (i : ℕ) (a b : F) (v : Fin 8 → F) :
    termD ρ Φ₀ h0 i a v + termD ρ Φ₀ h0 i b v = termD ρ Φ₀ h0 i (a + b) v := by
  rw [termD_apply, termD_apply, termD_apply, add_smul, map_add, map_add, map_add]

omit [CharP F 2] in
theorem termD_zero (i : ℕ) (v : Fin 8 → F) : termD ρ Φ₀ h0 i 0 v = 0 := by
  rw [termD_apply, zero_smul, map_zero, map_zero, map_zero]

theorem termD_shift (i : ℕ) (c' : F) (w : Fin 8 → F) :
    ρ (dGL ω h0) (termD ρ Φ₀ h0 i c' (adG (dGL ω h0)⁻¹ w)) = termD ρ Φ₀ h0 (i + 1) c' w := by
  have h : adG (dGL ω h0 ^ i)⁻¹ (c' • adG (dGL ω h0)⁻¹ w) =
      adG (dGL ω h0 ^ (i + 1))⁻¹ (c' • w) := by
    rw [LinearMap.map_smul, LinearMap.map_smul, ← adG_mul, ← mul_inv_rev, ← pow_succ']
  rw [termD_apply, termD_apply, h, ← Module.End.mul_apply, ← map_mul, ← pow_succ']

theorem termD_three [Fintype F] (hF : Fintype.card F = 4) (h1 : ω ≠ 1) (c' : F) (v : Fin 8 → F) :
    termD ρ Φ₀ h0 3 c' v = termD ρ Φ₀ h0 0 c' v := by
  rw [termD_apply, termD_apply, dGL_pow_three hF h0 h1, pow_zero]

theorem termD_equivariant
    (hΦ₀ : ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∀ v, Φ₀ (adG g v) = ρ g (Φ₀ v))
    (i : ℕ) (c' : F) {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F).det = 1)
    (v : Fin 8 → F) : termD ρ Φ₀ h0 i c' (adG g v) = ρ g (termD ρ Φ₀ h0 i c' v) := by
  rw [termD_apply, termD_apply]
  generalize dGL ω h0 ^ i = e
  have h1 : adG e⁻¹ (c' • adG g v) = adG (e⁻¹ * g * e) (adG e⁻¹ (c' • v)) := by
    rw [LinearMap.map_smul, ← adG_mul, ← adG_mul, LinearMap.map_smul,
      show e⁻¹ * g * e * e⁻¹ = e⁻¹ * g by group]
  have hdet : ((e⁻¹ * g * e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      mul_comm _ (Matrix.GeneralLinearGroup.det e), ← mul_assoc, mul_inv_cancel, one_mul,
      Matrix.GeneralLinearGroup.val_det_apply, hg]
  rw [h1, hΦ₀ _ hdet, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

@[expose] noncomputable def projC (c : F) : (Fin 8 → F) →+ U :=
  termD ρ Φ₀ h0 0 1 + termD ρ Φ₀ h0 1 (c ^ 2) + termD ρ Φ₀ h0 2 c

theorem projC_d [Fintype F] (hF : Fintype.card F = 4) (h1 : ω ≠ 1) {c : F} (hc : c ^ 3 = 1)
    (w : Fin 8 → F) :
    ρ (dGL ω h0) (projC ρ Φ₀ h0 c (adG (dGL ω h0)⁻¹ w)) = projC ρ Φ₀ h0 c (c • w) := by
  simp only [projC, AddMonoidHom.add_apply, map_add]
  rw [termD_shift, termD_shift, termD_shift]
  simp only [Nat.reduceAdd, zero_add]
  rw [termD_three ρ Φ₀ h0 hF h1, termD_smul, termD_smul, termD_smul, one_mul, ← pow_succ, hc,
    ← sq]
  abel

theorem projC_sum [Fintype F] (hF : Fintype.card F = 4) (h1 : ω ≠ 1) (v : Fin 8 → F) :
    projC ρ Φ₀ h0 1 v + projC ρ Φ₀ h0 ω v + projC ρ Φ₀ h0 (ω ^ 2) v = Φ₀ v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hωω := sq_eq_add_one hF h0 h1
  have hs1 : (1 : F) ^ 2 + ω ^ 2 + (ω ^ 2) ^ 2 = 0 := by
    have hω3 := pow_three_eq_one hF h0 h1
    linear_combination hωω + (ω + 1) * h2 + ω * hω3
  have hs2 : (1 : F) + ω + ω ^ 2 = 0 := by linear_combination hωω + (ω + 1) * h2
  have hU : ∀ u : U, u + u = 0 := fun u => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  simp only [projC, AddMonoidHom.add_apply]
  have e1 : termD ρ Φ₀ h0 1 ((1 : F) ^ 2) v + termD ρ Φ₀ h0 1 (ω ^ 2) v +
      termD ρ Φ₀ h0 1 ((ω ^ 2) ^ 2) v = 0 := by
    rw [termD_add, termD_add, hs1, termD_zero]
  have e2 : termD ρ Φ₀ h0 2 1 v + termD ρ Φ₀ h0 2 ω v + termD ρ Φ₀ h0 2 (ω ^ 2) v = 0 := by
    rw [termD_add, termD_add, hs2, termD_zero]
  rw [termD_zero_one]
  calc Φ₀ v + termD ρ Φ₀ h0 1 ((1 : F) ^ 2) v + termD ρ Φ₀ h0 2 1 v +
        (Φ₀ v + termD ρ Φ₀ h0 1 (ω ^ 2) v + termD ρ Φ₀ h0 2 ω v) +
        (Φ₀ v + termD ρ Φ₀ h0 1 ((ω ^ 2) ^ 2) v + termD ρ Φ₀ h0 2 (ω ^ 2) v) =
      (Φ₀ v + Φ₀ v) + Φ₀ v + (termD ρ Φ₀ h0 1 ((1 : F) ^ 2) v + termD ρ Φ₀ h0 1 (ω ^ 2) v +
        termD ρ Φ₀ h0 1 ((ω ^ 2) ^ 2) v) +
        (termD ρ Φ₀ h0 2 1 v + termD ρ Φ₀ h0 2 ω v + termD ρ Φ₀ h0 2 (ω ^ 2) v) := by abel
    _ = Φ₀ v := by rw [e1, e2, hU, zero_add, add_zero, add_zero]

end Proj

theorem exists_twAdj_equiv [Fintype F] (hF : Fintype.card F = 4) [Finite U]
    (ρ : Representation (ZMod 2) (GL (Fin 3) F) U) (hirr : ρ.IsIrreducible)
    (Φ₀ : (Fin 8 → F) →+ U) (hinj : Function.Injective Φ₀)
    (hΦ₀ : ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∀ v, Φ₀ (adG g v) = ρ g (Φ₀ v)) :
    ∃ k < 3, ∃ Φ : (Fin 8 → F) ≃+ U, ∀ (g : GL (Fin 3) F) (v : Fin 8 → F),
      ρ g (Φ v) = Φ (((g : Matrix (Fin 3) (Fin 3) F).det) ^ k • adG g v) := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hF
  have hω3 := pow_three_eq_one hF hω0 hω1
  have : Nontrivial U := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
  obtain ⟨k, hk, hne⟩ : ∃ k < 3, ∃ v, projC ρ Φ₀ hω0 (ω ^ k) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv⟩ : ∃ v : Fin 8 → F, v ≠ 0 := ⟨Pi.single 0 1, by simp⟩
    apply hv
    apply hinj
    have h1 := hcon 0 (by norm_num) v
    have h2 := hcon 1 (by norm_num) v
    have h3 := hcon 2 (by norm_num) v
    rw [pow_zero] at h1
    rw [pow_one] at h2
    rw [map_zero, ← projC_sum ρ Φ₀ hω0 hF hω1 v, h1, h2, h3, add_zero, add_zero]
  set c := ω ^ k with hcdef
  have hc3 : c ^ 3 = 1 := by rw [hcdef, ← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  set Φ := projC ρ Φ₀ hω0 c with hΦdef
  set d := dGL ω hω0 with hd
  have hsl : ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∀ v, Φ (adG g v) = ρ g (Φ v) := by
    intro g hg v
    simp only [hΦdef, projC, AddMonoidHom.add_apply, termD_equivariant ρ Φ₀ hω0 hΦ₀ _ _ hg,
      map_add]
  have hdv : ∀ v, ρ d (Φ v) = Φ (c • adG d v) := by
    intro v
    have := projC_d ρ Φ₀ hω0 hF hω1 hc3 (adG d v)
    rwa [adG_inv_adG] at this
  have hpow : ∀ (i : ℕ) v, ρ (d ^ i) (Φ v) = Φ (c ^ i • adG (d ^ i) v) := by
    intro i
    induction i with
    | zero =>
      intro v
      rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul, adG_one]
    | succ i ih =>
      intro v
      rw [pow_succ' d, map_mul, Module.End.mul_apply, ih, hdv, LinearMap.map_smul, smul_smul,
        ← pow_succ', adG_mul]
  have hall : ∀ (g : GL (Fin 3) F) v,
      ρ g (Φ v) = Φ (((g : Matrix (Fin 3) (Fin 3) F).det) ^ k • adG g v) := by
    intro g v
    have hdet0 : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact (Matrix.GeneralLinearGroup.det g).ne_zero
    obtain ⟨i, -, hgi⟩ := exists_pow_eq hF hω0 hω1 hdet0
    have hs : (((d ^ i)⁻¹ * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, hgi, ← Matrix.GeneralLinearGroup.val_det_apply,
        map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, hd,
        det_dGL_pow]
      exact inv_mul_cancel₀ (pow_ne_zero i hω0)
    have hg : g = d ^ i * ((d ^ i)⁻¹ * g) := (mul_inv_cancel_left _ _).symm
    rw [hg, map_mul, Module.End.mul_apply, ← hsl _ hs, hpow, ← adG_mul, ← hg, hgi, hcdef,
      ← pow_mul, ← pow_mul, mul_comm]
  have hsurj : Function.Surjective Φ := by
    have hR : ∀ g, ∀ u ∈ Φ.range, ρ g u ∈ Φ.range := by
      rintro g _ ⟨v, rfl⟩
      exact ⟨_, (hall g v).symm⟩
    rcases addSubgroup_eq_bot_or_top hirr Φ.range hR with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hne
      have : Φ v ∈ Φ.range := ⟨v, rfl⟩
      rw [h, AddSubgroup.mem_bot] at this
      exact hv this
    · exact AddMonoidHom.range_eq_top.mp h
  have hbij := hsurj.bijective_of_nat_card_le (Nat.card_le_card_of_injective Φ₀ hinj)
  exact ⟨k, hk, AddEquiv.ofBijective Φ hbij, hall⟩

end CFSG.Quasithin.H13.Ch4.B414

module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3SL3Lin
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.L1293S

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem charP_seven [Finite F] {e : ℕ} (hF : Nat.card F = 7 ^ e) : CharP F 7 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hdvd : ringChar F ∣ 7 ^ e := by
    rw [← hF, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
    (hp.dvd_of_dvd_pow hdvd))

theorem two_ne_zero_of_charP [CharP F 7] : (2 : F) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F 7] at this
  omega

@[expose] def herm (v w : Fin 3 → F) : F := ∑ i, v i ^ 7 * w i

section Herm

variable [CharP F 7]

theorem herm_mulVec {A : Matrix (Fin 3) (Fin 3) F} (hA : (A.map (· ^ 7))ᵀ * A = 1)
    (v w : Fin 3 → F) : herm (A *ᵥ v) (A *ᵥ w) = herm v w := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have herm_eq : ∀ v w : Fin 3 → F, herm v w = (frobenius F 7 ∘ v) ⬝ᵥ w := fun v w => by
    simp only [herm, dotProduct, Function.comp_apply, frobenius_def]
  have hσ : A.map (· ^ 7) = A.map (frobenius F 7) := by
    ext i j
    simp [frobenius_def]
  have hv : frobenius F 7 ∘ (A *ᵥ v) = (A.map (frobenius F 7)) *ᵥ (frobenius F 7 ∘ v) := by
    funext i
    exact RingHom.map_mulVec (frobenius F 7) A v i
  rw [herm_eq, herm_eq, hv, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, ← hσ, hA,
    one_mulVec]

theorem det_herm_of_mem {A : GL (Fin 3) F} (hA : A ∈ StatedSU 3 7 F) :
    (A : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      ∀ v w, herm ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ v) ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ w) =
        herm v w := by
  induction hA using Subgroup.closure_induction with
  | mem A hA => exact ⟨hA.1, herm_mulVec hA.2⟩
  | one => exact ⟨by simp, fun v w => by simp⟩
  | mul A B _ _ hA hB =>
    refine ⟨by rw [Units.val_mul, det_mul, hA.1, hB.1, one_mul], fun v w => ?_⟩
    rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hA.2, hB.2]
  | inv A _ hA =>
    refine ⟨by rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hA.1, Ring.inverse_one],
      fun v w => ?_⟩
    have hAA : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← hA.2, mulVec_mulVec, mulVec_mulVec, hAA, one_mulVec, one_mulVec]

end Herm

section Centralizer

variable {H : Subgroup (GL (Fin 3) F)}

@[expose] noncomputable def toGL (H : Subgroup (GL (Fin 3) F)) :
    ↥H →* LinearMap.GeneralLinearGroup F (Fin 3 → F) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp H.subtype

theorem toGL_apply (h : ↥H) (v : Fin 3 → F) :
    ((toGL H h : LinearMap.GeneralLinearGroup F (Fin 3 → F)) : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) v =
      (((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) *ᵥ v := by
  rw [toGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Matrix.GeneralLinearGroup.toLin_apply, mulVecLin_apply]
  rfl

theorem toGL_injective : Function.Injective (toGL H) := by
  intro a b h
  apply Subtype.ext
  exact Matrix.GeneralLinearGroup.toLin.injective h

theorem det_toGL (h : ↥H) :
    LinearMap.det ((toGL H h : LinearMap.GeneralLinearGroup F (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = (((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det := by
  have e : ((toGL H h : LinearMap.GeneralLinearGroup F (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = Matrix.toLin' ((h : GL (Fin 3) F) : Matrix _ _ F) := by
    refine LinearMap.ext fun v => ?_
    rw [toGL_apply, Matrix.toLin'_apply]
  rw [e, LinearMap.det_toLin']

variable (h2 : (2 : F) ≠ 0) (hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1)
  {B₀ : Subgroup ↥H} (hperf : ⁅B₀, B₀⁆ = B₀) {z : ↥H} (hzB : z ∈ B₀) (hz1 : z ≠ 1)
  (hzz : z * z = 1) (hzc : ∀ x ∈ B₀, x * z = z * x)

include h2 hH hperf hzB hz1 hzz hzc in
theorem exists_hom_centralizer :
    ∃ α : ↥(Subgroup.centralizer (B₀ : Set ↥H)) →* Fˣ, Function.Injective α ∧
      eNeg (((toGL H z : LinearMap.GeneralLinearGroup F (Fin 3 → F))) :
        (Fin 3 → F) →ₗ[F] (Fin 3 → F)) ≠ ⊥ ∧
      ∀ (c : ↥(Subgroup.centralizer (B₀ : Set ↥H))),
        ∀ v ∈ eNeg (((toGL H z : LinearMap.GeneralLinearGroup F (Fin 3 → F))) :
          (Fin 3 → F) →ₗ[F] (Fin 3 → F)),
          ((((c : ↥H) : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ((α c : Fˣ) : F) • v := by
  set φ := toGL H with hφ
  set P := B₀.map φ with hP
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hperf]
  have hzP : φ z ∈ P := Subgroup.mem_map_of_mem φ hzB
  have hzz' : φ z * φ z = 1 := by rw [← map_mul, hzz, map_one]
  have hz1' : φ z ≠ 1 := fun h => hz1 (toGL_injective (h.trans (map_one φ).symm))
  have hzc' : ∀ g ∈ P, g * φ z = φ z * g := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hzc x hx]
  have hdet : LinearMap.det ((φ z : LinearMap.GeneralLinearGroup F (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = 1 := by
    rw [hφ, det_toGL]
    exact hH _ z.2
  set C := (Subgroup.centralizer (B₀ : Set ↥H)).map φ with hC
  have hCP : ∀ c ∈ C, LinearMap.det (c : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = 1 ∧
      ∀ g ∈ P, c * g = g * c := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨by rw [hφ, det_toGL]; exact hH _ c.2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc x hx]
  have hV : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  obtain ⟨α, hαinj, hα⟩ := exists_injective_hom hV h2 hPperf hzP hzz' hz1' hzc' hdet C hCP
  set e := (Subgroup.centralizer (B₀ : Set ↥H)).equivMapOfInjective φ toGL_injective with he
  have hdim := finrank_eNeg hV h2 (apply_apply_of_mul_self hzz')
    (fun h => hz1' (Units.ext h)) hdet
  refine ⟨α.comp e.toMonoidHom, hαinj.comp e.injective, fun h => ?_, fun c v hv => ?_⟩
  · rw [h, finrank_bot] at hdim
    omega
  · have := hα (e c) v hv
    rw [← toGL_apply]
    exact this

include h2 hH hperf hzB hz1 hzz hzc in
theorem card_centralizer_dvd [Finite F] :
    Nat.card ↥(Subgroup.centralizer (B₀ : Set ↥H)) ∣ Nat.card F - 1 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨α, hαinj, -, -⟩ := exists_hom_centralizer h2 hH hperf hzB hz1 hzz hzc
  rw [Nat.card_congr (MonoidHom.ofInjective hαinj).toEquiv]
  have h := Subgroup.card_subgroup_dvd_card α.range
  rwa [Nat.card_eq_fintype_card (α := Fˣ), Fintype.card_units, ← Nat.card_eq_fintype_card] at h

include h2 hperf hzB hz1 hzz hzc in
theorem card_centralizer_le_eight [Finite F] [CharP F 7] (hSU : H ≤ StatedSU 3 7 F) :
    Nat.card ↥(Subgroup.centralizer (B₀ : Set ↥H)) ≤ 8 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hH : ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).det = 1 := fun g hg =>
    (det_herm_of_mem (hSU hg)).1
  obtain ⟨α, hαinj, hne, hα⟩ := exists_hom_centralizer h2 hH hperf hzB hz1 hzz hzc
  have hzz' := apply_apply_of_mul_self (z := toGL H z) (by rw [← map_mul, hzz, map_one])
  have hroot : α.range ≤ rootsOfUnity 8 F := by
    rintro _ ⟨c, rfl⟩
    rw [mem_rootsOfUnity]
    apply Units.ext
    have h1 := sigma_mul_eq_one h2 hzz' (h := herm) (frobenius F 7)
      (fun v w w' => by simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun a b v w => by
        simp only [herm, Pi.smul_apply, smul_eq_mul, frobenius_def, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun v hv => by
        obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
          by_contra h
          exact hv (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
        refine ⟨Pi.single i 1, ?_⟩
        simp only [herm, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        exact pow_ne_zero 7 hi)
      (fun v w => by
        rw [toGL_apply, toGL_apply]
        exact (det_herm_of_mem (hSU z.2)).2 v w) hne
      (c := ((toGL H (c : ↥H) : LinearMap.GeneralLinearGroup F (Fin 3 → F)) :
        (Fin 3 → F) →ₗ[F] (Fin 3 → F)))
      (fun v w => by
        rw [toGL_apply, toGL_apply]
        exact (det_herm_of_mem (hSU (c : ↥H).2)).2 v w)
      (fun v hv => by rw [toGL_apply]; exact hα c v hv)
    rw [frobenius_def, ← pow_succ] at h1
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h1
  rw [Nat.card_congr (MonoidHom.ofInjective hαinj).toEquiv]
  exact (Subgroup.card_le_of_le hroot).trans (card_rootsOfUnity F 8)

end Centralizer

end CFSG.Quasithin.H13.L1293S

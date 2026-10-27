module

public import CFSG.Quasithin.Background.RonanG51F4Data
public import CFSG.Quasithin.Background.RonanG51Tensor
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix FieldFour
  CFSG.Quasithin.H13.A6.G52 Matrix Equiv
open scoped TensorProduct

abbrev F4 : Type := GaloisField 2 2

noncomputable def ι : FieldFour ≃ₐ[ZMod 2] F4 :=
  GaloisField.algEquivGaloisField 2 2 (by simpa using natCard_eq)

noncomputable def φ : FieldFour →+* F4 := (ι : FieldFour →+* F4)

theorem φ_ofPrime (a : ZMod 2) : φ (ofPrime a) = algebraMap (ZMod 2) F4 a := ι.commutes a

theorem φ_frob (x : FieldFour) : φ (frob x) = frobenius F4 2 (φ x) := by
  rw [frob_apply, map_pow]
  rfl

theorem frob_ofPrime (a : ZMod 2) : frob (ofPrime a) = ofPrime a := by
  revert a
  decide

theorem frobenius_frobenius (z : F4) : frobenius F4 2 (frobenius F4 2 z) = z := by
  obtain ⟨x, rfl⟩ := ι.surjective z
  have h : φ x = ι x := rfl
  rw [← h, ← φ_frob, ← φ_frob, frob_frob]

noncomputable def B1 : Matrix (Fin 16) (Fin 8) F4 := basis8.map φ

noncomputable def B2 : Matrix (Fin 16) (Fin 8) F4 := basis8'.map φ

noncomputable def P1 : Matrix (Fin 8) (Fin 16) F4 := proj8.map φ

noncomputable def P2 : Matrix (Fin 8) (Fin 16) F4 := proj8'.map φ

noncomputable def KK (g : Equiv.Perm (Fin 6)) : Matrix (Fin 16) (Fin 16) F4 :=
  (kronHom g).map (algebraMap (ZMod 2) F4)

theorem P1_B1 : P1 * B1 = 1 := by
  rw [P1, B1, ← Matrix.map_mul, proj8_mul_basis8, Matrix.map_one φ (map_zero φ) (map_one φ)]

theorem P1_B2 : P1 * B2 = 0 := by
  rw [P1, B2, ← Matrix.map_mul, proj8_mul_basis8', Matrix.map_zero φ (map_zero φ)]

theorem B_sum : B1 * P1 + B2 * P2 = 1 := by
  rw [B1, P1, B2, P2, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add φ (map_add φ), basis8_add,
    Matrix.map_one φ (map_zero φ) (map_one φ)]

theorem B2_eq : B2 = B1.map (frobenius F4 2) := by
  ext i j
  simp only [B2, B1, basis8', Matrix.map_apply, φ_frob]

theorem B1_eq : B1 = B2.map (frobenius F4 2) := by
  rw [B2_eq]
  ext i j
  simp only [Matrix.map_apply, frobenius_frobenius]

theorem KK_eq_map (g : Equiv.Perm (Fin 6)) :
    ((kronHom g).map ofPrime).map φ = KK g := by
  ext i j
  simp only [KK, Matrix.map_apply, φ_ofPrime]

theorem KK_mul (g h : Equiv.Perm (Fin 6)) : KK (g * h) = KK g * KK h := by
  rw [KK, KK, KK, map_mul]
  exact Matrix.map_mul (f := algebraMap (ZMod 2) F4)

theorem KK_B1 (g : ↥(alternatingGroup (Fin 6))) :
    KK (g : Equiv.Perm (Fin 6)) * B1 = B1 * (rep8aMat g).map φ := by
  have h := congrArg (fun M => M.map φ) (kron16F_mul_basis8 g)
  simp only [Matrix.map_mul] at h
  rw [← KK_eq_map]
  exact h

theorem KK_B2 (g : ↥(alternatingGroup (Fin 6))) :
    KK (g : Equiv.Perm (Fin 6)) * B2 = B2 * ((rep8aMat g).map frob).map φ := by
  have h := congrArg (fun M => M.map frob) (kron16F_mul_basis8 g)
  simp only [Matrix.map_mul] at h
  have e : (kron16F g).map frob = kron16F g := by
    refine Matrix.ext fun i j => ?_
    simp only [kron16F, Matrix.map_apply, frob_ofPrime]
  rw [e] at h
  have h2 := congrArg (fun M => M.map φ) h
  simp only [Matrix.map_mul] at h2
  rw [← KK_eq_map]
  exact h2

section Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))

noncomputable def U1 : Submodule F4 (F4 ⊗[ZMod 2] V) :=
  (LinearMap.range (Matrix.mulVecLin B1)).comap (theta F4 e).toLinearMap

noncomputable def U2 : Submodule F4 (F4 ⊗[ZMod 2] V) :=
  (LinearMap.range (Matrix.mulVecLin B2)).comap (theta F4 e).toLinearMap

theorem mem_U1 {x : F4 ⊗[ZMod 2] V} : x ∈ U1 e ↔ ∃ y, B1 *ᵥ y = theta F4 e x := by
  simp [U1, LinearMap.mem_range]

theorem mem_U2 {x : F4 ⊗[ZMod 2] V} : x ∈ U2 e ↔ ∃ y, B2 *ᵥ y = theta F4 e x := by
  simp [U2, LinearMap.mem_range]

variable (τ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
  (hτ : ∀ g v, e (τ g v) = kronHom g *ᵥ e v)

include hτ in
theorem theta_lTensor_KK (g : Equiv.Perm (Fin 6)) (x : F4 ⊗[ZMod 2] V) :
    theta F4 e (LinearMap.lTensor F4 (τ g) x) = KK g *ᵥ theta F4 e x :=
  theta_lTensor F4 e (τ g) (kronHom g) (hτ g) x

include hτ in
theorem lTensor_mem_U1 (g : ↥(alternatingGroup (Fin 6)))
    {x : F4 ⊗[ZMod 2] V} (hx : x ∈ U1 e) :
    LinearMap.lTensor F4 (τ (g : Equiv.Perm (Fin 6))) x ∈ U1 e := by
  obtain ⟨y, hy⟩ := (mem_U1 e).mp hx
  refine (mem_U1 e).mpr ⟨(rep8aMat g).map φ *ᵥ y, ?_⟩
  rw [theta_lTensor_KK e τ hτ, ← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, KK_B1]

include hτ in
theorem lTensor_mem_U2 (g : ↥(alternatingGroup (Fin 6)))
    {x : F4 ⊗[ZMod 2] V} (hx : x ∈ U2 e) :
    LinearMap.lTensor F4 (τ (g : Equiv.Perm (Fin 6))) x ∈ U2 e := by
  obtain ⟨y, hy⟩ := (mem_U2 e).mp hx
  refine (mem_U2 e).mpr ⟨((rep8aMat g).map frob).map φ *ᵥ y, ?_⟩
  rw [theta_lTensor_KK e τ hτ, ← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, KK_B2]

theorem isCompl_U1_U2 : IsCompl (U1 e) (U2 e) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨y, hy⟩ := (mem_U1 e).mp hx1
    obtain ⟨y', hy'⟩ := (mem_U2 e).mp hx2
    have h0 : y = 0 := by
      calc y = (P1 * B1) *ᵥ y := by rw [P1_B1, Matrix.one_mulVec]
        _ = P1 *ᵥ (B1 *ᵥ y) := by rw [Matrix.mulVec_mulVec]
        _ = P1 *ᵥ (B2 *ᵥ y') := by rw [hy, hy']
        _ = (P1 * B2) *ᵥ y' := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [P1_B2, Matrix.zero_mulVec]
    apply (theta F4 e).injective
    rw [← hy, h0, Matrix.mulVec_zero, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨(theta F4 e).symm (B1 *ᵥ (P1 *ᵥ theta F4 e x)), ?_,
      (theta F4 e).symm (B2 *ᵥ (P2 *ᵥ theta F4 e x)), ?_, ?_⟩
    · exact (mem_U1 e).mpr ⟨P1 *ᵥ theta F4 e x, by rw [LinearEquiv.apply_symm_apply]⟩
    · exact (mem_U2 e).mpr ⟨P2 *ᵥ theta F4 e x, by rw [LinearEquiv.apply_symm_apply]⟩
    · apply (theta F4 e).injective
      rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, B_sum, Matrix.one_mulVec]

theorem finrank_U1 : Module.finrank F4 (U1 e) = 8 := by
  have h1 : U1 e = (LinearMap.range (Matrix.mulVecLin B1)).map (theta F4 e).symm.toLinearMap :=
    Submodule.comap_equiv_eq_map_symm _ _
  rw [h1, LinearEquiv.finrank_map_eq]
  have hinj : Function.Injective (Matrix.mulVecLin B1) := by
    intro y z hyz
    have h : P1 *ᵥ (B1 *ᵥ y) = P1 *ᵥ (B1 *ᵥ z) := by
      simpa only [Matrix.mulVecLin_apply] using congrArg (fun w => P1 *ᵥ w) hyz
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, P1_B1, Matrix.one_mulVec,
      Matrix.one_mulVec] at h
    exact h
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

theorem KK_one : KK 1 = 1 := by
  rw [KK, map_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem KK_swap : KK (swap 0 1) = kSwF.map φ := by
  rw [← KK_eq_map, kSwF, kron_swap]

theorem KK_swap_B1 : KK (swap 0 1) * B1 = B2 * (P2 * KK (swap 0 1) * B1) := by
  have h := congrArg (fun M => M.map φ) kSwF_basis8
  simp only [Matrix.map_mul] at h
  rw [KK_swap]
  exact h

theorem KK_swap_B2 : KK (swap 0 1) * B2 = B1 * (P1 * KK (swap 0 1) * B2) := by
  have h := congrArg (fun M => M.map φ) kSwF_basis8'
  simp only [Matrix.map_mul] at h
  rw [KK_swap]
  exact h

include hτ in
theorem lTensor_comp_eq (g h : Equiv.Perm (Fin 6)) (x : F4 ⊗[ZMod 2] V) :
    LinearMap.lTensor F4 (τ (g * h)) x =
      LinearMap.lTensor F4 (τ g) (LinearMap.lTensor F4 (τ h) x) := by
  apply (theta F4 e).injective
  rw [theta_lTensor_KK e τ hτ, theta_lTensor_KK e τ hτ, theta_lTensor_KK e τ hτ, KK_mul,
    Matrix.mulVec_mulVec]

include hτ in
theorem lTensor_one_apply (x : F4 ⊗[ZMod 2] V) : LinearMap.lTensor F4 (τ 1) x = x := by
  apply (theta F4 e).injective
  rw [theta_lTensor_KK e τ hτ, KK_one, Matrix.one_mulVec]

include hτ in
theorem lTensor_swap_mem_U2 {x : F4 ⊗[ZMod 2] V} (hx : x ∈ U1 e) :
    LinearMap.lTensor F4 (τ (swap 0 1)) x ∈ U2 e := by
  obtain ⟨y, hy⟩ := (mem_U1 e).mp hx
  refine (mem_U2 e).mpr ⟨(P2 * KK (swap 0 1) * B1) *ᵥ y, ?_⟩
  rw [theta_lTensor_KK e τ hτ, ← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, KK_swap_B1]

include hτ in
theorem lTensor_swap_mem_U1 {x : F4 ⊗[ZMod 2] V} (hx : x ∈ U2 e) :
    LinearMap.lTensor F4 (τ (swap 0 1)) x ∈ U1 e := by
  obtain ⟨y, hy⟩ := (mem_U2 e).mp hx
  refine (mem_U1 e).mpr ⟨(P1 * KK (swap 0 1) * B2) *ᵥ y, ?_⟩
  rw [theta_lTensor_KK e τ hτ, ← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, KK_swap_B2]

theorem sign_swap_mul_of_not_mem {t : Equiv.Perm (Fin 6)} (ht : t ∉ alternatingGroup (Fin 6)) :
    swap (0 : Fin 6) 1 * t ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup] at ht ⊢
  rw [map_mul, Equiv.Perm.sign_swap (by decide)]
  rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h
  · exact absurd h ht
  · rw [h]
    decide

include hτ in
theorem U2_eq_image_odd {t : Equiv.Perm (Fin 6)}
    (ht : t ∉ alternatingGroup (Fin 6)) :
    (U2 e : Set (F4 ⊗[ZMod 2] V)) = (LinearMap.lTensor F4 (τ t)) '' (U1 e : Set _) := by
  set a : ↥(alternatingGroup (Fin 6)) := ⟨swap 0 1 * t, sign_swap_mul_of_not_mem ht⟩ with ha
  have hta : t = swap 0 1 * (a : Equiv.Perm (Fin 6)) := by
    rw [ha]
    show t = swap 0 1 * (swap 0 1 * t)
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  ext x'
  constructor
  · intro hx'
    refine ⟨LinearMap.lTensor F4 (τ ((a : Equiv.Perm (Fin 6))⁻¹))
      (LinearMap.lTensor F4 (τ (swap 0 1)) x'), ?_, ?_⟩
    · exact lTensor_mem_U1 e τ hτ a⁻¹ (lTensor_swap_mem_U1 e τ hτ hx')
    · show LinearMap.lTensor F4 (τ t) (LinearMap.lTensor F4 (τ ((a : Equiv.Perm (Fin 6))⁻¹))
        (LinearMap.lTensor F4 (τ (swap 0 1)) x')) = x'
      have hprod : t * (a : Equiv.Perm (Fin 6))⁻¹ * swap 0 1 = 1 := by
        have hav : (a : Equiv.Perm (Fin 6)) = swap 0 1 * t := rfl
        rw [hav, _root_.mul_inv_rev, Equiv.swap_inv]
        simp [mul_assoc, Equiv.swap_mul_self]
      rw [← lTensor_comp_eq e τ hτ, ← lTensor_comp_eq e τ hτ, hprod]
      exact lTensor_one_apply e τ hτ x'
  · rintro ⟨x, hx, rfl⟩
    show LinearMap.lTensor F4 (τ t) x ∈ U2 e
    rw [hta, lTensor_comp_eq e τ hτ]
    exact lTensor_swap_mem_U2 e τ hτ (lTensor_mem_U1 e τ hτ a hx)

@[expose] noncomputable def frobLin : F4 →ₗ[ZMod 2] F4 :=
  AddMonoidHom.toZModLinearMap 2 (frobeniusEquiv F4 2).toAddEquiv.toAddMonoidHom

theorem theta_rTensor_frob (x : F4 ⊗[ZMod 2] V) :
    theta F4 e (LinearMap.rTensor V frobLin x) = fun i => frobenius F4 2 (theta F4 e x i) := by
  rw [theta_rTensor]
  rfl

theorem frobenius_mulVec {n : ℕ} (B : Matrix (Fin 16) (Fin n) F4) (y : Fin n → F4) :
    (fun i => frobenius F4 2 ((B *ᵥ y) i)) =
      (B.map (frobenius F4 2)) *ᵥ (fun j => frobenius F4 2 (y j)) := by
  funext i
  exact RingHom.map_mulVec (frobenius F4 2) B y i

theorem rTensor_frob_mem_U2 {x : F4 ⊗[ZMod 2] V} (hx : x ∈ U1 e) :
    LinearMap.rTensor V frobLin x ∈ U2 e := by
  obtain ⟨y, hy⟩ := (mem_U1 e).mp hx
  refine (mem_U2 e).mpr ⟨fun j => frobenius F4 2 (y j), ?_⟩
  rw [theta_rTensor_frob, ← hy, frobenius_mulVec, ← B2_eq]

theorem rTensor_frob_mem_U1 {x : F4 ⊗[ZMod 2] V} (hx : x ∈ U2 e) :
    LinearMap.rTensor V frobLin x ∈ U1 e := by
  obtain ⟨y, hy⟩ := (mem_U2 e).mp hx
  refine (mem_U1 e).mpr ⟨fun j => frobenius F4 2 (y j), ?_⟩
  rw [theta_rTensor_frob, ← hy, frobenius_mulVec, ← B1_eq]

include e in
theorem rTensor_frob_rTensor_frob (x : F4 ⊗[ZMod 2] V) :
    LinearMap.rTensor V frobLin (LinearMap.rTensor V frobLin x) = x := by
  apply (theta F4 e).injective
  rw [theta_rTensor_frob, theta_rTensor_frob]
  funext i
  exact frobenius_frobenius _

theorem U2_eq_image_frob :
    (U2 e : Set (F4 ⊗[ZMod 2] V)) = (LinearMap.rTensor V frobLin) '' (U1 e : Set _) := by
  ext x'
  constructor
  · intro hx'
    exact ⟨LinearMap.rTensor V frobLin x', rTensor_frob_mem_U1 e hx',
      rTensor_frob_rTensor_frob e x'⟩
  · rintro ⟨x, hx, rfl⟩
    exact rTensor_frob_mem_U2 e hx

end Tensor

theorem f4_decomposition {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (e : V ≃ₗ[ZMod 2] (Fin 16 → ZMod 2))
    (τ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hτ : ∀ g v, e (τ g v) = kronHom g *ᵥ e v) :
    ∃ U₁ U₂ : Submodule (GaloisField 2 2) (TensorProduct (ZMod 2) (GaloisField 2 2) V),
      (∀ g : ↥(alternatingGroup (Fin 6)), ∀ x ∈ U₁,
        LinearMap.lTensor (GaloisField 2 2) (τ (g : Equiv.Perm (Fin 6))) x ∈ U₁) ∧
      (∀ g : ↥(alternatingGroup (Fin 6)), ∀ x ∈ U₂,
        LinearMap.lTensor (GaloisField 2 2) (τ (g : Equiv.Perm (Fin 6))) x ∈ U₂) ∧
      IsCompl U₁ U₂ ∧ Module.finrank (GaloisField 2 2) U₁ = 8 ∧
      (∀ t : Equiv.Perm (Fin 6), t ∉ alternatingGroup (Fin 6) →
        (U₂ : Set (TensorProduct (ZMod 2) (GaloisField 2 2) V)) =
          (LinearMap.lTensor (GaloisField 2 2) (τ t)) '' (U₁ : Set _)) ∧
      (U₂ : Set (TensorProduct (ZMod 2) (GaloisField 2 2) V)) =
        (LinearMap.rTensor V
          (AddMonoidHom.toZModLinearMap 2
            (frobeniusEquiv (GaloisField 2 2) 2).toAddEquiv.toAddMonoidHom)) '' (U₁ : Set _) :=
  ⟨U1 e, U2 e, fun g x hx => lTensor_mem_U1 e τ hτ g hx, fun g x hx => lTensor_mem_U2 e τ hτ g hx,
    isCompl_U1_U2 e, finrank_U1 e, fun t ht => U2_eq_image_odd e τ hτ ht, U2_eq_image_frob e⟩

end CFSG.Quasithin.RonanG51

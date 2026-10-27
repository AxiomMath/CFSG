module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Mat
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix
open scoped MatrixGroups

theorem s9c_card_of_IsPSL3 {Ks : Type} [Group Ks] (h : IsPSL 3 2 1 Ks) :
    Nat.card Ks = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

noncomputable def s9cF (E : Type) [Field E] [CharP E 2] : ZMod 2 →+* E :=
  ZMod.castHom (dvd_refl 2) E

theorem s9cF_apply {E : Type} [Field E] [CharP E 2] (a : ZMod 2) :
    s9cF E a = ((a.val : ℕ) : E) := by
  rw [s9cF, ZMod.castHom_apply, ZMod.cast_eq_val]

noncomputable def s9cPsi {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3) :
    Matrix (Fin 3) (Fin 3) (ZMod 2) →+* Matrix (Fin n) (Fin n) E :=
  (Matrix.reindexRingEquiv E (finCongr hn.symm)).toRingHom.comp
    (RingHom.mapMatrix (s9cF E))

theorem s9cPsi_apply {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3)
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    s9cPsi (E := E) hn X =
      (X.map (fun a : ZMod 2 => ((a.val : ℕ) : E))).submatrix (Fin.cast hn) (Fin.cast hn) := by
  ext i j
  simp [s9cPsi, s9cF_apply, Matrix.reindexRingEquiv, Matrix.reindex_apply, finCongr_apply]

@[expose] noncomputable def s9cJ {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3) :
    SL(3, ZMod 2) →* GL (Fin n) E :=
  (Units.map (s9cPsi (E := E) hn).toMonoidHom).comp Matrix.SpecialLinearGroup.toGL

theorem s9cJ_val {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3) (M : SL(3, ZMod 2)) :
    ((s9cJ (E := E) hn M : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)).map (fun a : ZMod 2 => ((a.val : ℕ) : E))).submatrix
        (Fin.cast hn) (Fin.cast hn) := by
  rw [← s9cPsi_apply]
  rfl

theorem s9cJ_injective {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3) :
    Function.Injective (s9cJ (E := E) hn) := by
  intro M M' h
  have hv := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) h
  simp only [s9cJ_val] at hv
  have key : ∀ X : Matrix (Fin 3) (Fin 3) E,
      (X.submatrix (Fin.cast hn) (Fin.cast hn)).submatrix (Fin.cast hn.symm) (Fin.cast hn.symm) = X := by
    intro X
    ext i j
    simp
  have h2 := congrArg (fun X : Matrix (Fin n) (Fin n) E =>
    X.submatrix (Fin.cast hn.symm) (Fin.cast hn.symm)) hv
  simp only [key] at h2
  have hfun : (fun a : ZMod 2 => ((a.val : ℕ) : E)) = s9cF E := funext fun a => (s9cF_apply a).symm
  rw [hfun] at h2
  exact Subtype.ext (Matrix.map_injective (s9cF E).injective h2)

theorem s9cJ_s9P1 {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3) (M : SL(3, ZMod 2)) :
    s9P1 ((s9cJ (E := E) hn M : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((s9P1 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)))).map
        (fun a : ZMod 2 => ((a.val : ℕ) : E))).submatrix (Fin.cast hn) (Fin.cast hn) := by
  rw [s9cJ_val, ← s9cPsi_apply, ← s9cPsi_apply]
  simp [s9P1, map_add, map_mul, map_one]

theorem s9cJ_s9P2 {E : Type} [Field E] [CharP E 2] {n : ℕ} (hn : n = 3) (M : SL(3, ZMod 2)) :
    s9P2 ((s9cJ (E := E) hn M : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((s9P2 ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)))).map
        (fun a : ZMod 2 => ((a.val : ℕ) : E))).submatrix (Fin.cast hn) (Fin.cast hn) := by
  rw [s9cJ_val, ← s9cPsi_apply, ← s9cPsi_apply]
  simp [s9P2, map_add, map_mul, map_one]

theorem s9c_lift_hom {K₀ : Type} [Group K₀] {n : ℕ} {E : Type} [Field E] [CharP E 2]
    (ρK : K₀ →* GL (Fin n) E) (P : GL (Fin n) E) (J : SL(3, ZMod 2) →* GL (Fin n) E)
    (hJ : Function.Injective J) (hran : ∀ x : K₀, P * ρK x * P⁻¹ ∈ J.range) :
    ∃ θ : K₀ →* SL(3, ZMod 2), ∀ x : K₀, J (θ x) = P * ρK x * P⁻¹ := by
  choose θ hθ using fun x : K₀ => (MonoidHom.mem_range.mp (hran x))
  refine ⟨MonoidHom.mk' θ fun x y => hJ ?_, fun x => hθ x⟩
  simp only [map_mul, hθ]
  group

theorem s9c_theta_of_card {K₀ Ks : Type} [Group K₀] [Group Ks] [Finite K₀] [Finite Ks]
    (σ : K₀ →* Ks) (hσ : Function.Surjective σ) (hKs : Nat.card Ks = 168)
    {n : ℕ} {E : Type} [Field E] [CharP E 2]
    (ρK : K₀ →* GL (Fin n) E) (hker : ρK.ker ≤ σ.ker)
    (P : GL (Fin n) E) (J : SL(3, ZMod 2) →* GL (Fin n) E) (hJ : Function.Injective J)
    (hSL : Nat.card SL(3, ZMod 2) = 168) (hran : ∀ x : K₀, P * ρK x * P⁻¹ ∈ J.range) :
    ∃ θ : K₀ →* SL(3, ZMod 2), (∀ x : K₀, J (θ x) = P * ρK x * P⁻¹) ∧
      Function.Surjective θ ∧ θ.ker = σ.ker := by
  obtain ⟨θ, hθ⟩ := s9c_lift_hom ρK P J hJ hran
  have hidxσ : σ.ker.index = 168 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hσ, Subgroup.card_top, hKs]
  let T : Subgroup (GL (Fin n) E) := J.range.comap (MulAut.conj P).toMonoidHom
  have hT : Nat.card T = 168 := by
    rw [← hSL]
    exact (Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj P).toEquiv (fun g => Iff.rfl))).trans
      (Nat.card_congr (MonoidHom.ofInjective hJ).toEquiv.symm)
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have hle : ρK.range ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact hran x
  have hdvd : σ.ker.index ∣ ρK.ker.index := Subgroup.index_dvd_of_le hker
  have hidxρ : ρK.ker.index = Nat.card ρK.range := Subgroup.index_ker ρK
  haveI : Finite ρK.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective ρK)
  have hpos : 0 < Nat.card ρK.range := Nat.card_pos
  have hge : 168 ≤ Nat.card ρK.range := by
    have hdvd' : 168 ∣ Nat.card ρK.range := by
      rw [← hidxσ, ← hidxρ]
      exact hdvd
    exact Nat.le_of_dvd hpos hdvd'
  have hKbar : ρK.range = T := Subgroup.eq_of_le_of_card_ge hle (by rw [hT]; exact hge)
  have hidxρ' : ρK.ker.index = 168 := by
    rw [hidxρ, hKbar, hT]
  have hsurj : Function.Surjective θ := by
    intro M
    have hmem : P⁻¹ * J M * P ∈ ρK.range := by
      rw [hKbar]
      have hc : (MulAut.conj P) (P⁻¹ * J M * P) = J M := by
        simp [MulAut.conj_apply, mul_assoc]
      show (MulAut.conj P) (P⁻¹ * J M * P) ∈ J.range
      rw [hc]
      exact ⟨M, rfl⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
    refine ⟨x, hJ ?_⟩
    rw [hθ x, hx]
    group
  have hkerθρ : θ.ker = ρK.ker := by
    ext x
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : J (θ x) = 1 := by rw [h, map_one]
      rw [hθ x] at h1
      calc ρK x = P⁻¹ * (P * ρK x * P⁻¹) * P := by group
        _ = 1 := by rw [h1]; group
    · intro h
      apply hJ
      rw [map_one, hθ x, h]
      group
  have hcardeq : Nat.card ρK.ker = Nat.card σ.ker := by
    have h1 := Subgroup.card_mul_index ρK.ker
    have h2 := Subgroup.card_mul_index σ.ker
    rw [hidxρ'] at h1
    rw [hidxσ] at h2
    omega
  refine ⟨θ, hθ, hsurj, ?_⟩
  rw [hkerθρ]
  exact Subgroup.eq_of_le_of_card_ge hker (le_of_eq hcardeq.symm)

theorem s9c_conj_s9P1 {E : Type} [Field E] {n : ℕ} (P : GL (Fin n) E)
    (X : Matrix (Fin n) (Fin n) E) :
    s9P1 ((P : Matrix (Fin n) (Fin n) E) * X * ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) =
      (P : Matrix (Fin n) (Fin n) E) * s9P1 X *
        ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  have hBA : ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (P : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAB : (P : Matrix (Fin n) (Fin n) E) * ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set A : Matrix (Fin n) (Fin n) E := (P : Matrix (Fin n) (Fin n) E) with hA
  set B : Matrix (Fin n) (Fin n) E := ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hB
  have h2 : (A * X * B) * (A * X * B) = A * (X * X) * B := by
    calc A * X * B * (A * X * B) = A * X * (B * A) * X * B := by
          simp only [Matrix.mul_assoc]
      _ = A * (X * X) * B := by
          rw [hBA]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
  have h3 : (A * X * B) * (A * X * B) * (A * X * B) = A * (X * X * X) * B := by
    calc (A * X * B) * (A * X * B) * (A * X * B) = (A * (X * X) * B) * (A * X * B) := by
          rw [h2]
      _ = A * (X * X) * (B * A) * X * B := by
          simp only [Matrix.mul_assoc]
      _ = A * (X * X * X) * B := by
          rw [hBA]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
  unfold s9P1
  rw [h3]
  calc A * (X * X * X) * B + A * X * B + 1 = A * (X * X * X) * B + A * X * B + A * B := by
        rw [hAB]
    _ = A * (X * X * X + X + 1) * B := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc]

theorem s9c_P1_sub_one {E : Type} [Field E] [CharP E 2] {d : ℕ} (M : Matrix (Fin d) (Fin d) E) :
    s9P1 M - 1 = M * (M - 1) * (M - 1) := by
  have hxx : ∀ x : Matrix (Fin d) (Fin d) E, x + x = 0 := by
    intro x
    ext i j
    have h2E : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
    simp only [Matrix.add_apply, Matrix.zero_apply]
    rw [← two_mul, h2E, zero_mul]
  have h1 : (M - 1) * (M - 1) = M * M + 1 := by
    calc (M - 1) * (M - 1) = M * M - (M + M) + 1 := by noncomm_ring
      _ = M * M + 1 := by rw [hxx M, sub_zero]
  rw [mul_assoc, h1]
  unfold s9P1
  noncomm_ring

theorem s9c_trivial_step_P1 {E : Type} [Field E] [CharP E 2] {d : ℕ}
    (Y0 Y1 : Submodule E (Fin d → E)) (M : Matrix (Fin d) (Fin d) E)
    (hMinv : ∀ v ∈ Y0, M *ᵥ v ∈ Y0) (hstep : ∀ v ∈ Y1, M *ᵥ v - v ∈ Y0) :
    ∀ v ∈ Y1, s9P1 M *ᵥ v - v ∈ Y0 := by
  intro v hv
  have hw : M *ᵥ v - v ∈ Y0 := hstep v hv
  have hw2 : M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v) ∈ Y0 := Y0.sub_mem (hMinv _ hw) hw
  have e : s9P1 M *ᵥ v - v = M *ᵥ (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) := by
    calc s9P1 M *ᵥ v - v = (s9P1 M - 1) *ᵥ v := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = (M * (M - 1) * (M - 1)) *ᵥ v := by rw [s9c_P1_sub_one M]
      _ = M *ᵥ ((M - 1) *ᵥ ((M - 1) *ᵥ v)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = M *ᵥ (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) := by
          simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  exact hMinv _ hw2

end CFSG.Quasithin.H13.L829N

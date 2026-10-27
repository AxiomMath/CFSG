module

public import CFSG.LieType.Steinberg.CentralExt.HermitianBasis

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

variable {L : Type} [Field L]

@[expose] noncomputable def glTwist (n : ℕ) (σ : L →+* L) : GL (Fin n) L →* GL (Fin n) L where
  toFun A := ⟨(((A⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σ)ᵀ,
    ((A : Matrix (Fin n) (Fin n) L).map σ)ᵀ, by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.map_one _ σ.map_zero σ.map_one, Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.map_one _ σ.map_zero σ.map_one, Matrix.transpose_one]⟩
  map_one' := Units.ext (by
    simp only [inv_one, Units.val_one, Matrix.map_one _ σ.map_zero σ.map_one,
      Matrix.transpose_one])
  map_mul' A B := Units.ext (by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul])

theorem coe_glTwist {n : ℕ} (σ : L →+* L) (A : GL (Fin n) L) :
    (glTwist n σ A : Matrix (Fin n) (Fin n) L) =
      (((A⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σ)ᵀ :=
  rfl

theorem coe_glTwist_inv {n : ℕ} (σ : L →+* L) (A : GL (Fin n) L) :
    ((glTwist n σ A)⁻¹ : GL (Fin n) L) = ((A : Matrix (Fin n) (Fin n) L).map σ)ᵀ :=
  rfl

theorem conjTr_eq_glTwist_inv {n : ℕ} (σ : L ≃+* L) (A : GL (Fin n) L) :
    conjTr σ (A : Matrix (Fin n) (Fin n) L) =
      ((glTwist n (σ : L →+* L) A)⁻¹ : GL (Fin n) L) :=
  rfl

theorem glTwist_glTwist {n : ℕ} {σ : L →+* L} (hσ : ∀ c, σ (σ c) = c) (A : GL (Fin n) L) :
    glTwist n σ (glTwist n σ A) = A := by
  apply Units.ext
  rw [coe_glTwist, coe_glTwist_inv, Matrix.transpose_map, Matrix.transpose_transpose,
    Matrix.map_map]
  ext i j
  simp [hσ]

@[expose] noncomputable def glScalar (n : ℕ) : Lˣ →* GL (Fin n) L :=
  Units.map (Matrix.scalar (Fin n) : L →+* Matrix (Fin n) (Fin n) L).toMonoidHom

theorem coe_glScalar (n : ℕ) (u : Lˣ) :
    (glScalar n u : Matrix (Fin n) (Fin n) L) = Matrix.scalar (Fin n) (u : L) :=
  rfl

theorem glScalar_commute (n : ℕ) (u : Lˣ) (A : GL (Fin n) L) :
    glScalar n u * A = A * glScalar n u :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, coe_glScalar]
    exact Matrix.scalar_commute (u : L) (fun _ => Commute.all _ _) _)

theorem glScalar_injective {n : ℕ} (hn : 0 < n) : Function.Injective (glScalar (L := L) n) := by
  intro u v h
  have h1 := congrArg (fun A : GL (Fin n) L => (A : Matrix (Fin n) (Fin n) L) ⟨0, hn⟩ ⟨0, hn⟩) h
  have h2 : (u : L) = v := by simpa [coe_glScalar] using h1
  exact Units.ext h2

theorem glTwist_glScalar {n : ℕ} (σ : L →+* L) (u : Lˣ) :
    glTwist n σ (glScalar n u) = glScalar n (Units.map σ.toMonoidHom u)⁻¹ := by
  apply Units.ext
  rw [coe_glTwist, ← map_inv, coe_glScalar, coe_glScalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij)]

theorem exists_unit_pow_mul_eq [Finite L] {q : ℕ} (hq : Nat.card L = q ^ 2) (hq1 : 1 ≤ q)
    {c : Lˣ} (hc : c ^ (q + 1) = 1) : ∃ κ : Lˣ, κ ^ q * c = κ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  have hcard : Nat.card Lˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_units, hq]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hord : orderOf g = (q - 1) * (q + 1) :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg c⁻¹)
  have h1 : ((orderOf g : ℕ) : ℤ) ∣ j * ((q + 1 : ℕ) : ℤ) := by
    rw [orderOf_dvd_iff_zpow_eq_one, _root_.zpow_mul, hj, zpow_natCast, inv_pow, hc, inv_one]
  rw [hord, Nat.cast_mul] at h1
  have hq0 : ((q + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  obtain ⟨k, hk⟩ : ((q - 1 : ℕ) : ℤ) ∣ j := (mul_dvd_mul_iff_right hq0).1 h1
  refine ⟨g ^ k, ?_⟩
  have hgk : (g ^ k) ^ q = g ^ k * c⁻¹ := by
    rw [← hj, hk, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add]
    congr 1
    push_cast [Nat.cast_sub hq1]
    ring
  rw [hgk, mul_assoc, inv_mul_cancel, mul_one]

abbrev slToGL {n : ℕ} (X : SL(n, L)) : GL (Fin n) L := Matrix.SpecialLinearGroup.toGL X

variable [Finite L] {p f : ℕ} [Fact p.Prime] [CharP L p]

theorem exists_hermitian_of_twist (hL : Nat.card L = (p ^ f) ^ 2) (Ψ : SL(3, L) →* SL(3, L))
    (W : GL (Fin 3) L)
    (hW : ∀ X, slToGL (Ψ X) = W * glTwist 3 (unitaryInvolution L p f : L →+* L) (slToGL X) * W⁻¹)
    (hΨ2 : ∀ X, Ψ (Ψ X) = X) :
    ∃ G : GL (Fin 3) L,
      conjTr (unitaryInvolution L p f) (G : Matrix (Fin 3) (Fin 3) L) = G ∧
      ∀ X : SL(3, L), Ψ X = X ↔
        (glTwist 3 (unitaryInvolution L p f : L →+* L) (slToGL X))⁻¹ * G * slToGL X = G := by
  set σ := unitaryInvolution L p f with hσdef
  have hσσ : ∀ c, (σ : L →+* L) ((σ : L →+* L) c) = c := unitaryInvolution_involutive hL
  have hσapp : ∀ c, σ c = c ^ p ^ f := unitaryInvolution_apply L p f
  set ψ := glTwist 3 (σ : L →+* L) with hψ
  set M := W * ψ W with hMdef
  have hMX : ∀ X : SL(3, L), M * slToGL X = slToGL X * M := by
    intro X
    have h := hW (Ψ X)
    rw [hΨ2, hW X, map_mul, map_mul, map_inv, glTwist_glTwist hσσ] at h
    have h' : slToGL X = M * slToGL X * M⁻¹ := by
      calc slToGL X = W * (ψ W * slToGL X * (ψ W)⁻¹) * W⁻¹ := h
        _ = M * slToGL X * M⁻¹ := by rw [hMdef]; group
    calc M * slToGL X = M * slToGL X * M⁻¹ * M := by group
      _ = slToGL X * M := by rw [← h']
  obtain ⟨c, hc⟩ : (M : Matrix (Fin 3) (Fin 3) L) ∈ Set.range (Matrix.scalar (Fin 3)) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j hij => ?_
    have h : (M : Matrix (Fin 3) (Fin 3) L) * Matrix.transvection i j 1 =
        Matrix.transvection i j 1 * (M : Matrix (Fin 3) (Fin 3) L) :=
      congrArg (fun A : GL (Fin 3) L => (A : Matrix (Fin 3) (Fin 3) L))
        (hMX (Matrix.SpecialLinearGroup.transvection hij 1))
    simp only [Matrix.transvection] at h
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact (add_left_cancel h).symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
    rw [← hc, map_zero, Matrix.det_zero] at h
    exact not_isUnit_zero h
  set cu : Lˣ := Units.mk0 c hc0 with hcu
  have hM : M = glScalar 3 cu := Units.ext (by rw [coe_glScalar, ← hc]; rfl)
  have hψW : ψ W = W⁻¹ * M := by rw [hMdef]; group
  have hψM : ψ M = M := by
    have h1 : ψ M = ψ W * W := by rw [hMdef, map_mul, glTwist_glTwist hσσ]
    rw [h1, hψW, mul_assoc, hM, glScalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcq : cu ^ (p ^ f + 1) = 1 := by
    rw [hM, glTwist_glScalar] at hψM
    have h1 := glScalar_injective (by norm_num) hψM
    have h2 : Units.map (σ : L →+* L).toMonoidHom cu = cu ^ p ^ f :=
      Units.ext (by simp [hσapp])
    rw [h2, inv_eq_iff_eq_inv] at h1
    rw [pow_succ, h1, inv_mul_cancel]
  obtain ⟨κ, hκ⟩ := exists_unit_pow_mul_eq (q := p ^ f) hL (Nat.one_le_pow _ _ (Fact.out :
    p.Prime).pos) hcq
  have hσκ : Units.map (σ : L →+* L).toMonoidHom κ = κ ^ p ^ f := Units.ext (by simp [hσapp])
  set G := W⁻¹ * glScalar 3 κ with hGdef
  have hψG : ψ G = (glScalar 3 cu)⁻¹ * W * (glScalar 3 (κ ^ p ^ f))⁻¹ := by
    rw [hGdef, map_mul, map_inv, hψW, glTwist_glScalar, hσκ, hM, map_inv]
    group
  refine ⟨G, ?_, fun X => ?_⟩
  ·
    rw [conjTr_eq_glTwist_inv, ← hψ]
    congr 1
    rw [hψG]
    calc ((glScalar 3 cu)⁻¹ * W * (glScalar 3 (κ ^ p ^ f))⁻¹)⁻¹ =
        glScalar 3 (κ ^ p ^ f) * W⁻¹ * glScalar 3 cu := by group
      _ = W⁻¹ * glScalar 3 (κ ^ p ^ f) * glScalar 3 cu := by rw [glScalar_commute]
      _ = G := by rw [mul_assoc, ← map_mul, hκ]
  ·
    set Y := slToGL X with hYdef
    constructor
    · intro h
      have hY : Y = W * ψ Y * W⁻¹ := by
        rw [hYdef, ← hW, h]
      have hψY : ψ Y = W⁻¹ * Y * W := by
        calc ψ Y = W⁻¹ * (W * ψ Y * W⁻¹) * W := by group
          _ = W⁻¹ * Y * W := by rw [← hY]
      rw [hψY, hGdef]
      calc (W⁻¹ * Y * W)⁻¹ * (W⁻¹ * glScalar 3 κ) * Y = W⁻¹ * Y⁻¹ * (glScalar 3 κ * Y) := by
            group
        _ = W⁻¹ * Y⁻¹ * (Y * glScalar 3 κ) := by rw [glScalar_commute]
        _ = W⁻¹ * glScalar 3 κ := by group
    · intro h
      rw [hGdef] at h
      have h1 : (ψ Y)⁻¹ * W⁻¹ * Y = W⁻¹ := by
        have h2 : (ψ Y)⁻¹ * W⁻¹ * Y * glScalar 3 κ = W⁻¹ * glScalar 3 κ := by
          calc (ψ Y)⁻¹ * W⁻¹ * Y * glScalar 3 κ = (ψ Y)⁻¹ * W⁻¹ * (glScalar 3 κ * Y) := by
                rw [glScalar_commute 3 κ Y]; group
            _ = W⁻¹ * glScalar 3 κ := by rw [← h]; group
        exact mul_right_cancel h2
      apply Matrix.SpecialLinearGroup.toGL_injective
      change slToGL (Ψ X) = Y
      rw [hW]
      calc W * ψ Y * W⁻¹ = W * ψ Y * ((ψ Y)⁻¹ * W⁻¹ * Y) := by rw [h1]
        _ = Y := by group

theorem nonempty_eqLocus_mulEquiv_statedSU (hL : Nat.card L = (p ^ f) ^ 2)
    (Ψ : SL(3, L) →* SL(3, L)) (W : GL (Fin 3) L)
    (hW : ∀ X, slToGL (Ψ X) = W * glTwist 3 (unitaryInvolution L p f : L →+* L) (slToGL X) * W⁻¹)
    (hΨ2 : ∀ X, Ψ (Ψ X) = X) :
    Nonempty (Ψ.eqLocus (MonoidHom.id _) ≃* StatedSU 3 (p ^ f) L) := by
  set σ := unitaryInvolution L p f with hσdef
  set ψ := glTwist 3 (σ : L →+* L) with hψ
  obtain ⟨G, hherm, hfix⟩ := exists_hermitian_of_twist hL Ψ W hW hΨ2
  have hdet : (G : Matrix (Fin 3) (Fin 3) L).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp G.isUnit).ne_zero
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one hL hherm hdet
  have hP' : (ψ P)⁻¹ * G * P = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_mul, ← conjTr_eq_glTwist_inv]
    exact hP)
  have hGP : G = ψ P * P⁻¹ := by
    calc G = ψ P * ((ψ P)⁻¹ * G * P) * P⁻¹ := by group
      _ = ψ P * P⁻¹ := by rw [hP']; group
  have hmem : ∀ A : GL (Fin 3) L, A ∈ StatedSU 3 (p ^ f) L ↔
      (A : Matrix (Fin 3) (Fin 3) L).det = 1 ∧ (ψ A)⁻¹ * A = 1 := by
    intro A
    rw [← SUid_eq_statedSU hL, mem_SUid, conjTr_eq_glTwist_inv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Units.ext (by rw [Units.val_mul]; exact h2)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← Units.val_mul, h2, Units.val_one]
  have hkey : ∀ X : SL(3, L), Ψ X = X ↔ P⁻¹ * slToGL X * P ∈ StatedSU 3 (p ^ f) L := by
    intro X
    rw [hfix, hmem]
    have hdetY : ((P⁻¹ * slToGL X * P : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm,
        ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one, one_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact X.2
    have hψY : (ψ (P⁻¹ * slToGL X * P))⁻¹ * (P⁻¹ * slToGL X * P) =
        (ψ P)⁻¹ * ((ψ (slToGL X))⁻¹ * (ψ P * P⁻¹) * slToGL X) * P := by
      rw [map_mul, map_mul, map_inv]
      group
    rw [hψY, ← hGP]
    constructor
    · intro h
      refine ⟨hdetY, ?_⟩
      rw [h, hP']
    · rintro ⟨-, h⟩
      calc (ψ (slToGL X))⁻¹ * G * slToGL X =
          ψ P * ((ψ P)⁻¹ * ((ψ (slToGL X))⁻¹ * G * slToGL X) * P) * P⁻¹ := by group
        _ = ψ P * P⁻¹ := by rw [h]; group
        _ = G := hGP.symm
  set k : Ψ.eqLocus (MonoidHom.id _) →* StatedSU 3 (p ^ f) L :=
    { toFun := fun X => ⟨P⁻¹ * slToGL (X : SL(3, L)) * P, (hkey X).1 X.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun X Y => Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul]
        group) } with hk
  have hinj : Function.Injective k := by
    intro X Y h
    have h1 : P⁻¹ * slToGL (X : SL(3, L)) * P = P⁻¹ * slToGL (Y : SL(3, L)) * P :=
      congrArg Subtype.val h
    have h2 : slToGL (X : SL(3, L)) = slToGL (Y : SL(3, L)) := by
      have := congrArg (fun A => P * A * P⁻¹) h1
      simpa [mul_assoc] using this
    exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective h2)
  have hsurj : Function.Surjective k := by
    rintro ⟨A, hA⟩
    have hdetA := ((hmem A).1 hA).1
    set B := P * A * P⁻¹ with hBdef
    have hdetB : (B : Matrix (Fin 3) (Fin 3) L).det = 1 := by
      rw [hBdef, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm,
        ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.det_one, one_mul, hdetA]
    set X : SL(3, L) := ⟨(B : Matrix (Fin 3) (Fin 3) L), hdetB⟩ with hXdef
    have hXB : slToGL X = B := Units.ext rfl
    have hXA : P⁻¹ * slToGL X * P = A := by rw [hXB, hBdef]; group
    have hXfix : Ψ X = X := (hkey X).2 (by rw [hXA]; exact hA)
    exact ⟨⟨X, hXfix⟩, Subtype.ext hXA⟩
  exact ⟨MulEquiv.ofBijective k ⟨hinj, hsurj⟩⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

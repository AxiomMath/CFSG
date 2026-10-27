module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURich

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LieType.Universal.Unitary

namespace UFusion

open InnerDiagSU

section Twist

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def twistVec (a b : Fin (m + 1)) (c : Fˣ) : Fin (m + 1) → Fˣ :=
  Pi.mulSingle b c * Pi.mulSingle a c⁻¹

theorem twistVec_left {a b : Fin (m + 1)} (hab : a ≠ b) (c : Fˣ) : twistVec a b c a = c⁻¹ := by
  simp [twistVec, Pi.mulSingle_eq_of_ne hab]

theorem twistVec_right {a b : Fin (m + 1)} (hab : a ≠ b) (c : Fˣ) : twistVec a b c b = c := by
  simp [twistVec, Pi.mulSingle_eq_of_ne hab.symm]

theorem twistVec_other {a b k : Fin (m + 1)} (hka : k ≠ a) (hkb : k ≠ b) (c : Fˣ) :
    twistVec a b c k = 1 := by
  simp [twistVec, Pi.mulSingle_eq_of_ne hka, Pi.mulSingle_eq_of_ne hkb]

theorem norm_twistVec {a b : Fin (m + 1)} {c : Fˣ} (hc : σ (c : F) * c = 1) (k : Fin (m + 1)) :
    σ ((twistVec a b c k : Fˣ) : F) * ((twistVec a b c k : Fˣ) : F) = 1 := by
  have h1 : ∀ (d : Fˣ), σ (d : F) * d = 1 → ∀ l : Fin (m + 1),
      σ (((Pi.mulSingle l d : Fin (m + 1) → Fˣ) k : Fˣ) : F) *
        (((Pi.mulSingle l d : Fin (m + 1) → Fˣ) k : Fˣ) : F) = 1 := by
    intro d hd l
    by_cases hkl : k = l
    · rw [hkl, Pi.mulSingle_eq_same, hd]
    · rw [Pi.mulSingle_eq_of_ne hkl, Units.val_one, map_one, one_mul]
  rw [twistVec, Pi.mul_apply]
  exact norm_one_mul (h1 c hc b) (h1 c⁻¹ (norm_one_inv hc) a)

theorem prod_twistVec (a b : Fin (m + 1)) (c : Fˣ) : ∏ k, twistVec a b c k = 1 := by
  classical
  simp only [twistVec, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
    Finset.mem_univ, ite_true, mul_inv_cancel]

theorem isIdUnitary_mul {n : ℕ} {A B : GL (Fin n) F} (hA : IsIdUnitary σ A)
    (hB : IsIdUnitary σ B) : IsIdUnitary σ (A * B) := by
  unfold IsIdUnitary at hA hB ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr σ (B : Matrix (Fin n) (Fin n) F) * conjTr σ (A : Matrix (Fin n) (Fin n) F) *
        ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F))
      = conjTr σ (B : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

variable [CharP F 2]

noncomputable abbrev twistGL (a b : Fin (m + 1)) (c : Fˣ) : GL (Fin (m + 1)) F :=
  permGL (Equiv.swap a b) * InnerDiagA.diagGL (twistVec a b c)

theorem isIdUnitary_twistGL (a b : Fin (m + 1)) {c : Fˣ} (hc : σ (c : F) * c = 1) :
    IsIdUnitary σ (twistGL (F := F) a b c) :=
  isIdUnitary_mul (isIdUnitary_permGL _) (isIdUnitary_diagGL (norm_twistVec hc))

theorem det_twistGL (a b : Fin (m + 1)) (c : Fˣ) :
    ((twistGL (F := F) a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det =
      1 := by
  rw [Units.val_mul, det_mul, coe_permGL, det_permMatrix_charTwo, one_mul,
    InnerDiagA.coe_diagGL, det_diagonal, ← Units.coe_prod, prod_twistVec, Units.val_one]

theorem twistGL_mul_self {a b : Fin (m + 1)} (hab : a ≠ b) (c : Fˣ) :
    twistGL (F := F) a b c * twistGL a b c = 1 := by
  have hππ : permGL (F := F) (Equiv.swap a b) * permGL (Equiv.swap a b) = 1 := by
    have h := ggPermSL_mul_inv (F := F) (Equiv.swap a b)
    rw [Equiv.swap_inv] at h
    rw [permGL, ← map_mul, h, map_one]
  have h1 := LinFusion.toGL_ggPermSL_conj_diagGL (F := F) (Equiv.swap a b) (twistVec a b c)
  have hπi : (permGL (F := F) (Equiv.swap a b))⁻¹ = permGL (Equiv.swap a b) :=
    inv_eq_of_mul_eq_one_right hππ
  change (permGL (Equiv.swap a b))⁻¹ * _ * permGL (Equiv.swap a b) = _ at h1
  rw [hπi] at h1
  calc twistGL (F := F) a b c * twistGL a b c =
      permGL (Equiv.swap a b) * permGL (Equiv.swap a b) *
        (permGL (Equiv.swap a b) * InnerDiagA.diagGL (twistVec a b c) *
          permGL (Equiv.swap a b)) * InnerDiagA.diagGL (twistVec a b c) := by
        rw [hππ, one_mul]
        group
    _ = 1 := by
        rw [hππ, one_mul, h1, ← LinFusion.diagGL_mul]
        convert LinFusion.diagGL_one (F := F) (m := m) using 2
        funext k
        rw [Pi.mul_apply, Pi.one_apply, Equiv.swap_inv]
        by_cases hka : k = a
        · rw [hka, Equiv.swap_apply_left, twistVec_left hab, twistVec_right hab, mul_inv_cancel]
        · by_cases hkb : k = b
          · rw [hkb, Equiv.swap_apply_right, twistVec_left hab, twistVec_right hab,
              inv_mul_cancel]
          · rw [Equiv.swap_apply_of_ne_of_ne hka hkb, twistVec_other hka hkb, one_mul]

end Twist

section Comm

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}

theorem comm_twistGL_apply {X : Matrix (Fin (m + 1)) (Fin (m + 1)) F} {a b : Fin (m + 1)}
    (c : Fˣ)
    (h : X * ((twistGL a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      ((twistGL a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * X)
    (i j : Fin (m + 1)) :
    X i (Equiv.swap a b j) * ((twistVec a b c j : Fˣ) : F) =
      ((twistVec a b c (Equiv.swap a b i) : Fˣ) : F) * X (Equiv.swap a b i) j := by
  have h1 := congrFun (congrFun h i) j
  rw [Units.val_mul, coe_permGL, InnerDiagA.coe_diagGL, ← Matrix.mul_assoc X,
    Matrix.mul_assoc ((Equiv.swap a b).permMatrix F)] at h1
  simp only [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul,
    mul_diagonal, diagonal_mul, submatrix_apply, id, Equiv.symm_swap] at h1
  exact h1

theorem eq_of_comm_twistGL {X : Matrix (Fin (m + 1)) (Fin (m + 1)) F} {a b : Fin (m + 1)}
    (hab : a ≠ b) (c : Fˣ)
    (h : X * ((twistGL a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      ((twistGL a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * X) :
    X a b * ((c⁻¹ : Fˣ) : F) = (c : F) * X b a ∧ X a a = X b b := by
  have h1 := comm_twistGL_apply c h a a
  have h2 := comm_twistGL_apply c h a b
  rw [Equiv.swap_apply_left, twistVec_left hab, twistVec_right hab] at h1
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left, twistVec_right hab] at h2
  refine ⟨h1, ?_⟩
  rw [mul_comm] at h2
  exact mul_left_cancel₀ c.ne_zero h2

theorem eq_zero_of_comm_twistGL {X : Matrix (Fin (m + 1)) (Fin (m + 1)) F} {a b : Fin (m + 1)}
    (hab : a ≠ b) {c₁ c₂ : Fˣ} (hc : c₁ ≠ c₂)
    (h₁ : X * ((twistGL a b c₁ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      ((twistGL a b c₁ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * X)
    (h₂ : X * ((twistGL a b c₂ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      ((twistGL a b c₂ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * X) :
    X b a = 0 := by
  have e : ∀ c : Fˣ, X a b * ((c⁻¹ : Fˣ) : F) = (c : F) * X b a →
      X a b = (c : F) * c * X b a := by
    intro c hc'
    calc X a b = X a b * ((c⁻¹ : Fˣ) : F) * c := by
          rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      _ = (c : F) * c * X b a := by rw [hc']; ring
  have e1 := e c₁ (eq_of_comm_twistGL hab c₁ h₁).1
  have e2 := e c₂ (eq_of_comm_twistGL hab c₂ h₂).1
  have hsq : ((c₁ : F) - c₂) * (c₁ - c₂) * X b a = 0 := by
    have h3 : ((c₁ : F) - c₂) * (c₁ - c₂) =
        (c₁ : F) * c₁ - c₂ * c₂ + 2 * (c₂ * c₂ - c₁ * c₂) := by ring
    rw [h3, CharTwo.two_eq_zero, zero_mul, add_zero, sub_mul, ← e1, ← e2, sub_self]
  have hne : ((c₁ : F) - c₂) * (c₁ - c₂) ≠ 0 := by
    have h4 : (c₁ : F) - c₂ ≠ 0 := sub_ne_zero.mpr fun h => hc (Units.ext h)
    exact mul_ne_zero h4 h4
  exact (mul_eq_zero.mp hsq).resolve_left hne

@[expose] noncomputable def frameSU {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    (M : GL (Fin (m + 1)) F) (hM : IsIdUnitary σ M)
    (hdet : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1) : SU σ (m + 1) :=
  ⟨Q⁻¹ * M * Q, mem_SU.mpr ⟨by rw [det_frame_conj, hdet], isJUnitary_frame hQ hM⟩⟩

omit [CharP F 2] in
theorem coe_frameSU {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q) (M : GL (Fin (m + 1)) F)
    (hM : IsIdUnitary σ M) (hdet : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1) :
    ((frameSU hQ M hM hdet : SU σ (m + 1)) : GL (Fin (m + 1)) F) = Q⁻¹ * M * Q :=
  rfl

noncomputable abbrev twistSU {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q) (a b : Fin (m + 1))
    {c : Fˣ} (hc : σ (c : F) * c = 1) : SU σ (m + 1) :=
  frameSU hQ (twistGL a b c) (isIdUnitary_twistGL a b hc) (det_twistGL a b c)

omit [CharP F 2] in
theorem comm_of_comm_frameSU {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    {M : GL (Fin (m + 1)) F} (hM : IsIdUnitary σ M)
    (hdet : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det = 1) {u : SU σ (m + 1)}
    (h : u * frameSU hQ M hM hdet = frameSU hQ M hM hdet * u) :
    ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  have h' := congrArg (fun x : SU σ (m + 1) => (x : GL (Fin (m + 1)) F)) h
  simp only [Subgroup.coe_mul, coe_frameSU] at h'
  have h'' : Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ * M = M * (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) :=
    calc Q * (u : GL (Fin (m + 1)) F) * Q⁻¹ * M =
        Q * ((u : GL (Fin (m + 1)) F) * (Q⁻¹ * M * Q)) * Q⁻¹ := by group
      _ = Q * ((Q⁻¹ * M * Q) * (u : GL (Fin (m + 1)) F)) * Q⁻¹ := by rw [h']
      _ = M * (Q * (u : GL (Fin (m + 1)) F) * Q⁻¹) := by group
  have := congrArg (fun A : GL (Fin (m + 1)) F => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) h''
  simpa only [Units.val_mul] using this

end Comm

section Center

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}

theorem eq_one_of_mem_center_of_mul_self_eq_one {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζσ : σ (ζ : F) * ζ = 1) {z : SU σ (m + 1)}
    (hz : z ∈ Subgroup.center (SU σ (m + 1))) (hz2 : z * z = 1) : z = 1 := by
  have h1σ : σ ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1 := by
    rw [Units.val_one, map_one, one_mul]
  set Z := ((Q * (z : GL (Fin (m + 1)) F) * Q⁻¹ : GL (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hZ
  have hcomm : ∀ a b : Fin (m + 1), ∀ c : Fˣ, ∀ hc : σ (c : F) * c = 1,
      Z * ((twistGL a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        ((twistGL a b c : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Z := by
    intro a b c hc
    exact comm_of_comm_frameSU hQ (isIdUnitary_twistGL a b hc) (det_twistGL a b c)
      (Subgroup.mem_center_iff.mp hz (twistSU hQ a b hc)).symm
  have hoff : ∀ a b : Fin (m + 1), a ≠ b → Z b a = 0 := fun a b hab =>
    eq_zero_of_comm_twistGL hab (Ne.symm hζ1) (hcomm a b 1 h1σ) (hcomm a b ζ hζσ)
  have hdiag : ∀ a b : Fin (m + 1), Z a a = Z b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · exact (eq_of_comm_twistGL hab 1 (hcomm a b 1 h1σ)).2
  have hZZ : Z * Z = 1 := by
    have h2 := congrArg (fun x : SU σ (m + 1) => Q * (x : GL (Fin (m + 1)) F) * Q⁻¹) hz2
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h2
    have h3 : (Q * (z : GL (Fin (m + 1)) F) * Q⁻¹) * (Q * (z : GL (Fin (m + 1)) F) * Q⁻¹) = 1 :=
      calc (Q * (z : GL (Fin (m + 1)) F) * Q⁻¹) * (Q * (z : GL (Fin (m + 1)) F) * Q⁻¹) =
          Q * ((z : GL (Fin (m + 1)) F) * (z : GL (Fin (m + 1)) F)) * Q⁻¹ := by group
        _ = 1 := by rw [h2]; group
    have := congrArg (fun A : GL (Fin (m + 1)) F => (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) h3
    rw [Units.val_mul, Units.val_one] at this
    exact this
  have h00 : Z 0 0 * Z 0 0 = 1 := by
    have h4 := congrFun (congrFun hZZ 0) 0
    rw [mul_apply, Finset.sum_eq_single 0 (fun k _ hk => by rw [hoff k 0 hk, zero_mul])
      (fun h => absurd (Finset.mem_univ 0) h), one_apply_eq] at h4
    exact h4
  have h0 : Z 0 0 = 1 := by
    rcases mul_self_eq_one_iff.mp h00 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  have hZ1 : Q * (z : GL (Fin (m + 1)) F) * Q⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    ext a b
    change Z a b = _
    by_cases hab : a = b
    · rw [hab, hdiag b 0, h0, one_apply_eq]
    · rw [hoff b a (Ne.symm hab), one_apply_ne hab]
  apply Subtype.ext
  rw [Subgroup.coe_one]
  calc (z : GL (Fin (m + 1)) F) = Q⁻¹ * (Q * (z : GL (Fin (m + 1)) F) * Q⁻¹) * Q := by group
    _ = 1 := by rw [hZ1]; group

theorem commute_of_commutator_mem_center {Q : GL (Fin (m + 1)) F} (hQ : IsUFrame σ Q)
    {ζ : Fˣ} (hζ1 : ζ ≠ 1) (hζσ : σ (ζ : F) * ζ = 1) {u s : SU σ (m + 1)} (hs : s * s = 1)
    (hc : u * s * u⁻¹ * s⁻¹ ∈ Subgroup.center (SU σ (m + 1))) : u * s = s * u := by
  set c := u * s * u⁻¹ * s⁻¹ with hcdef
  have hcs : u * s * u⁻¹ = c * s := by rw [hcdef]; group
  have hcc : c * c = 1 := by
    have h1 : (u * s * u⁻¹) * (u * s * u⁻¹) = 1 := by
      calc (u * s * u⁻¹) * (u * s * u⁻¹) = u * (s * s) * u⁻¹ := by group
        _ = 1 := by rw [hs]; group
    rw [hcs] at h1
    have h2 : c * s * (c * s) = c * c * (s * s) := by
      rw [show c * s * (c * s) = c * (s * c) * s by group, Subgroup.mem_center_iff.mp hc s]
      group
    rw [h2, hs, mul_one] at h1
    exact h1
  have hc1 := eq_one_of_mem_center_of_mul_self_eq_one hQ hζ1 hζσ hc hcc
  calc u * s = c * s * u := by rw [← hcs]; group
    _ = s * u := by rw [hc1, one_mul]

end Center

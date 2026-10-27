module

public import CFSG.Quasithin.H13.GoldschmidtU43EVR3

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

@[expose] def X3m : M16 := ⟨0, 1, 2, 0, 2, 2, 2, 0, 2, 1, 1, 0, 0, 0, 0, 1⟩

@[expose] def Rho3mat : Mat3 := M16.toMat X3m

@[expose] def X4m : M16 := ⟨0, 1, 0, 2, 2, 2, 0, 2, 0, 0, 1, 0, 2, 1, 0, 1⟩

@[expose] def Rho4mat : Mat3 := M16.toMat X4m

theorem Vmat_pow_four : Vmat * Vmat * Vmat * Vmat = 1 := by
  rw [← toMat_gen_one, ← M16.toMat_mul, ← M16.toMat_mul, ← M16.toMat_mul, ← M16.toMat_one]
  congr 1

theorem Vmat_Rho3mat : Vmat * Rho3mat * (Vmat * Vmat * Vmat) = Rho4mat := by
  rw [← toMat_gen_one, Rho3mat, Rho4mat, ← M16.toMat_mul, ← M16.toMat_mul, ← M16.toMat_mul,
    ← M16.toMat_mul]
  congr 1

@[expose] def sig1v : V4 := ⟨2, 2, 0, 0⟩

@[expose] def sig2v : V4 := ⟨2, 1, 0, 0⟩

set_option maxRecDepth 100000 in
theorem unique_X3 : ∀ a ∈ ord3, V4.mulV a sig1v = sig1v → (V4.mulV a sig2v).v2 = 2 →
    (V4.mulV a sig2v).v3 = 0 → a = X3m := by decide +kernel

theorem toVec_sig1v : V4.toVec sig1v = ![2, 2, 0, 0] := by
  ext i
  fin_cases i <;> simp [V4.toVec, sig1v]

theorem toVec_sig2v : V4.toVec sig2v = ![2, 1, 0, 0] := by
  ext i
  fin_cases i <;> simp [V4.toVec, sig2v]

theorem eq_Rho3mat_of {X : Mat3} (hX : X ∈ Lset) (h3 : X ^ 3 = 1)
    (h1 : X.mulVec ![2, 2, 0, 0] = ![2, 2, 0, 0]) (h2 : (X.mulVec ![2, 1, 0, 0]) 2 = 2)
    (h2' : (X.mulVec ![2, 1, 0, 0]) 3 = 0) : X = Rho3mat := by
  have hX1 : X ≠ 1 := by
    intro h
    rw [h] at h2
    simp at h2
    exact absurd h2 (by decide)
  obtain ⟨a, ha, rfl⟩ := mem_ord3 hX h3 hX1
  have hv1 : V4.Valid sig1v := by decide
  have hv2 : V4.Valid sig2v := by decide
  have e1 : V4.mulV a sig1v = sig1v := by
    apply V4.toVec_inj (V4.valid_mulV a sig1v) hv1
    rw [V4.toVec_mulV, toVec_sig1v]
    exact h1
  have hw : V4.Valid (V4.mulV a sig2v) := V4.valid_mulV a sig2v
  have e2 := V4.toVec_mulV a sig2v
  rw [toVec_sig2v] at e2
  have c2 : (((V4.mulV a sig2v).v2 : ℕ) : ZMod 3) = 2 := by
    have := congrFun e2 2
    simp only [V4.toVec] at this
    simpa [h2] using this
  have c3 : (((V4.mulV a sig2v).v3 : ℕ) : ZMod 3) = 0 := by
    have := congrFun e2 3
    simp only [V4.toVec] at this
    simpa [h2'] using this
  have key : ∀ n : ℕ, n < 3 → ((n : ℕ) : ZMod 3) = 2 → n = 2 := by decide
  have key0 : ∀ n : ℕ, n < 3 → ((n : ℕ) : ZMod 3) = 0 → n = 0 := by decide
  obtain ⟨-, -, hw2, hw3⟩ := hw
  have := unique_X3 a ha e1 (key _ hw2 c2) (key0 _ hw3 c3)
  rw [this]
  rfl

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem crd_conjM (n : ↥S.Ng) (m : ↥S.Mg) :
    S.crd r (S.conjM n n.2 m) = (S.chiN r n).mulVec (S.crd r m) := by
  have h := S.chiN_rep r n (S.crd r m)
  rw [S.evC_crd] at h
  rw [h, S.crd_evC]

@[expose] noncomputable def crdHom : ↥S.Mg →* Multiplicative (Fin 4 → ZMod 3) where
  toFun m := Multiplicative.ofAdd (S.crd r m)
  map_one' := by simp [S.crd_one]
  map_mul' a b := by simp [S.crd_mul]

theorem crd_zpow (x : ↥S.Mg) (m : ℤ) (i : Fin 4) :
    S.crd r (x ^ m) i = (m : ZMod 3) * S.crd r x i := by
  have h := map_zpow (S.crdHom r) x m
  have h2 : Multiplicative.ofAdd (S.crd r (x ^ m)) =
      Multiplicative.ofAdd (m • S.crd r x) := h
  have h3 := congrFun (Multiplicative.ofAdd.injective h2) i
  simpa [zsmul_eq_mul] using h3

omit [Finite G] in
theorem rho3_pow_three {ρ : G} (hρ : ρ ^ 3 = 1) : S.rho3 ρ ^ 3 = 1 := by
  have h : (S.a₂G⁻¹ * ρ * S.a₂G⁻¹⁻¹) ^ 3 = S.a₂G⁻¹ * ρ ^ 3 * S.a₂G⁻¹⁻¹ := conj_pow
  unfold rho3
  rw [inv_inv] at h
  rw [h, hρ]
  group

theorem rho3_comm_σ₁ : S.rho3 r.ρ * (S.σ₁ : G) = (S.σ₁ : G) * S.rho3 r.ρ := by
  have hρσ : r.ρ * (S.σ₁ : G) = (S.σ₁ : G) * r.ρ :=
    S.abelian_Mg _ r.mem_Mg _ (S.Tg_le_Mg S.σ₁G_mem_Tg)
  have haσ : S.a₂G * (S.σ₁ : G) = (S.σ₁ : G) * S.a₂G := congrArg Subtype.val S.a₂_comm_σ₁
  have haσ' : S.a₂G⁻¹ * (S.σ₁ : G) = (S.σ₁ : G) * S.a₂G⁻¹ := by
    calc S.a₂G⁻¹ * (S.σ₁ : G) = S.a₂G⁻¹ * ((S.σ₁ : G) * S.a₂G) * S.a₂G⁻¹ := by group
      _ = S.a₂G⁻¹ * (S.a₂G * (S.σ₁ : G)) * S.a₂G⁻¹ := by rw [haσ]
      _ = (S.σ₁ : G) * S.a₂G⁻¹ := by group
  unfold rho3
  calc S.a₂G⁻¹ * r.ρ * S.a₂G * (S.σ₁ : G)
      = S.a₂G⁻¹ * r.ρ * (S.a₂G * (S.σ₁ : G)) := by group
    _ = S.a₂G⁻¹ * r.ρ * ((S.σ₁ : G) * S.a₂G) := by rw [haσ]
    _ = S.a₂G⁻¹ * (r.ρ * (S.σ₁ : G)) * S.a₂G := by group
    _ = S.a₂G⁻¹ * ((S.σ₁ : G) * r.ρ) * S.a₂G := by rw [hρσ]
    _ = (S.a₂G⁻¹ * (S.σ₁ : G)) * r.ρ * S.a₂G := by group
    _ = ((S.σ₁ : G) * S.a₂G⁻¹) * r.ρ * S.a₂G := by rw [haσ']
    _ = (S.σ₁ : G) * (S.a₂G⁻¹ * r.ρ * S.a₂G) := by group

theorem chiN_rho3 (e : S.Nbar ≃* alternatingGroup (Fin 6)) {V₃ : Subgroup G} (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    S.chiN r ⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩ = Rho3mat := by
  set n : ↥S.Ng := ⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩ with hn
  have hL : S.chiN r n ∈ Lset := by
    have := S.chiBar_mem_Lset r e (S.piN n)
    rwa [S.chiBar_piN] at this
  have hρ3 : r.ρ ^ 3 = 1 := S.rho_pow_three r.mem r.inv
  have h3 : S.chiN r n ^ 3 = 1 := by
    have hn3 : n ^ 3 = 1 := Subtype.ext (S.rho3_pow_three hρ3)
    rw [pow_three, ← S.chiN_mul, ← S.chiN_mul, ← pow_three, hn3, S.chiN_one]
  have h1 : (S.chiN r n).mulVec ![2, 2, 0, 0] = ![2, 2, 0, 0] := by
    have h := S.fixed_of_comm r n S.σ₁M (S.rho3_comm_σ₁ r)
    have e1 : S.crd r S.σ₁M = ![2, 2, 0, 0] := S.crd_σ₁M r
    have e2 : (Equiv.ofBijective _ (evC_basis_bijective r)).symm S.σ₁M = S.crd r S.σ₁M := rfl
    rw [e2, e1] at h
    exact h
  obtain ⟨m, hm⟩ := S.comm_sigma2_rho3 r e hV hAU
  have hμ : S.σ₂M * (S.conjM n n.2 S.σ₂M)⁻¹ = S.σ₁M ^ m * S.ρM r := by
    apply Subtype.ext
    have e1 : (((S.σ₂M * (S.conjM n n.2 S.σ₂M)⁻¹ : ↥S.Mg)) : G) =
        (S.σ₂ : G) * S.rho3 r.ρ * (S.σ₂ : G)⁻¹ * (S.rho3 r.ρ)⁻¹ := by
      show (S.σ₂ : G) * (S.rho3 r.ρ * (S.σ₂ : G) * (S.rho3 r.ρ)⁻¹)⁻¹ = _
      group
    have e2 : (((S.σ₁M ^ m * S.ρM r : ↥S.Mg)) : G) = (S.σ₁ : G) ^ m * r.ρ := by
      simp [σ₁M, ρM]
    rw [e1, e2]
    exact hm
  have hc : ∀ i, S.crd r (S.σ₂M * (S.conjM n n.2 S.σ₂M)⁻¹) i =
      S.crd r (S.σ₁M ^ m * S.ρM r) i := fun i => by rw [hμ]
  have h2 := hc 2
  have h3' := hc 3
  simp only [S.crd_mul, S.crd_inv, S.crd_conjM, S.crd_σ₂M, S.crd_σ₁M, S.crd_ρM, S.crd_zpow,
    Pi.add_apply, Pi.neg_apply] at h2 h3'
  refine eq_Rho3mat_of hL h3 h1 ?_ ?_
  · have key : ∀ x m : ZMod 3, ![2, 1, 0, 0] 2 + -x = m * ![2, 2, 0, 0] 2 + ![0, 0, 1, 0] 2 →
        x = 2 := by decide
    exact key _ (m : ZMod 3) h2
  · have key : ∀ x m : ZMod 3, ![2, 1, 0, 0] 3 + -x = m * ![2, 2, 0, 0] 3 + ![0, 0, 1, 0] 3 →
        x = 0 := by decide
    exact key _ (m : ZMod 3) h3'

omit [Finite G] in
theorem conj_v_a₂G : (S.v : G) * S.a₂G * (S.v : G)⁻¹ = S.a₂G⁻¹ := by
  have h1 : S.v⁻¹ * S.a₂ * S.v = S.v * S.a₂ * S.v⁻¹ := S.conj_v_inv S.a₂
  have h2 : S.v⁻¹ * S.a₂ * S.v = S.a₂⁻¹ := S.jw.r6
  have h3 : S.v * S.a₂ * S.v⁻¹ = S.a₂⁻¹ := by rw [← h1, h2]
  exact congrArg Subtype.val h3

theorem conj_v_rho3 : (S.v : G) * S.rho3 r.ρ * (S.v : G)⁻¹ = S.rho4 r.ρ := by
  unfold rho3 rho4
  calc (S.v : G) * (S.a₂G⁻¹ * r.ρ * S.a₂G) * (S.v : G)⁻¹
      = ((S.v : G) * S.a₂G * (S.v : G)⁻¹)⁻¹ * ((S.v : G) * r.ρ * (S.v : G)⁻¹) *
          ((S.v : G) * S.a₂G * (S.v : G)⁻¹) := by group
    _ = (S.a₂G⁻¹)⁻¹ * (S.rho2 r.ρ)⁻¹ * S.a₂G⁻¹ := by rw [S.conj_v_a₂G, S.conj_v_rho r]
    _ = (S.a₂G * S.rho2 r.ρ * S.a₂G⁻¹)⁻¹ := by group
    _ = S.a₂G⁻¹ * S.rho2 r.ρ * S.a₂G := by rw [S.conj_a₂G_rho2 r.inv, inv_inv]; unfold rho4; rfl

theorem chiN_rho4 (e : S.Nbar ≃* alternatingGroup (Fin 6)) {V₃ : Subgroup G} (hV : S.IsV3 V₃)
    (hAU : (S.A : G) ∈ Uz z) :
    S.chiN r ⟨S.rho4 r.ρ, S.rho4_mem_Ng e hV hAU r⟩ = Rho4mat := by
  set n₄ : ↥S.Ng := ⟨S.rho4 r.ρ, S.rho4_mem_Ng e hV hAU r⟩ with hn₄
  set n₃ : ↥S.Ng := ⟨S.rho3 r.ρ, S.rho3_mem_Ng e hV hAU r⟩ with hn₃
  set nv : ↥S.Ng := ⟨(S.v : G), S.v_mem_Ng⟩ with hnv
  have h : n₄ * nv = nv * n₃ := by
    apply Subtype.ext
    show S.rho4 r.ρ * (S.v : G) = (S.v : G) * S.rho3 r.ρ
    rw [← S.conj_v_rho3 r]
    group
  have h1 : S.chiN r n₄ * Vmat = Vmat * Rho3mat := by
    rw [← S.chiN_v r, ← S.chiN_rho3 r e hV hAU, ← S.chiN_mul, h, S.chiN_mul]
  calc S.chiN r n₄ = S.chiN r n₄ * (Vmat * Vmat * Vmat * Vmat) := by
        rw [Vmat_pow_four, mul_one]
    _ = (S.chiN r n₄ * Vmat) * (Vmat * Vmat * Vmat) := by simp only [mul_assoc]
    _ = Vmat * Rho3mat * (Vmat * Vmat * Vmat) := by rw [h1]
    _ = Rho4mat := Vmat_Rho3mat

end JWSetup

end CFSG.Quasithin.H13.U43

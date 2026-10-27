module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags
public import CFSG.LieType.Universal.Spin.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

namespace L1294E

open QuadraticMap Module Matrix CFSG.ClassicalGroups.Orthogonal

section Coordinates

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

@[expose] noncomputable def crd (P₁ P₂ : HypPair Q) (w : V) : Fin 4 → ZMod 2 :=
  ![polar Q w P₁.f, polar Q w P₂.f, polar Q w P₂.e, polar Q w P₁.e]

@[expose] noncomputable def cmb (P₁ P₂ : HypPair Q) (t : Fin 4 → ZMod 2) : V :=
  (t 0 • P₁.e + t 3 • P₁.f) + (t 1 • P₂.e + t 2 • P₂.f)

variable (P₁ P₂ : HypPair Q)

theorem crd_add (u w : V) : crd P₁ P₂ (u + w) = crd P₁ P₂ u + crd P₁ P₂ w := by
  funext i
  fin_cases i <;> simp [crd, polar_add_left]

theorem crd_smul (c : ZMod 2) (w : V) : crd P₁ P₂ (c • w) = c • crd P₁ P₂ w := by
  funext i
  fin_cases i <;> simp [crd]

theorem cmb_add (s t : Fin 4 → ZMod 2) : cmb P₁ P₂ (s + t) = cmb P₁ P₂ s + cmb P₁ P₂ t := by
  simp only [cmb, Pi.add_apply, add_smul]
  abel

theorem cmb_smul (c : ZMod 2) (t : Fin 4 → ZMod 2) :
    cmb P₁ P₂ (c • t) = c • cmb P₁ P₂ t := by
  simp only [cmb, Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]

theorem cmb_zero : cmb P₁ P₂ 0 = 0 := by
  simp [cmb]

variable {P₁ P₂}

theorem crd_cmb (h : P₁.Orth P₂) (t : Fin 4 → ZMod 2) : crd P₁ P₂ (cmb P₁ P₂ t) = t := by
  have h1 : polar Q P₂.e P₁.f = 0 := h.symm.ef
  have h2 : polar Q P₂.f P₁.f = 0 := h.symm.ff
  have h3 : polar Q P₂.e P₁.e = 0 := h.symm.ee
  have h4 : polar Q P₂.f P₁.e = 0 := h.symm.fe
  funext i
  fin_cases i <;> simp [crd, cmb, polar_add_left, P₁.polar_ef, P₁.polar_ff,
    P₁.polar_fe, P₁.polar_ee, P₂.polar_ef, P₂.polar_ff, P₂.polar_fe, P₂.polar_ee, h.ee, h.ef, h.fe,
    h.ff, h1, h2, h3, h4]

theorem crd_e (h : P₁.Orth P₂) : crd P₁ P₂ P₁.e = ![1, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [crd, P₁.polar_ef, P₁.polar_ee, h.ef, h.ee]

theorem Q_pair (P : HypPair Q) (α δ : ZMod 2) : Q (α • P.e + δ • P.f) = α * δ := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f, polar_smul_left_eq,
    polar_smul_right_eq, P.polar_ef]
  ring

theorem polar_pair_pair (h : P₁.Orth P₂) (α δ β γ : ZMod 2) :
    polar Q (α • P₁.e + δ • P₁.f) (β • P₂.e + γ • P₂.f) = 0 := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h.ee, h.ef,
    h.fe, h.ff, mul_zero, add_zero]

theorem Q_cmb (h : P₁.Orth P₂) (t : Fin 4 → ZMod 2) :
    Q (cmb P₁ P₂ t) = t 0 * t 3 + t 1 * t 2 := by
  rw [cmb, QuadraticMap.map_add Q, Q_pair, Q_pair, polar_pair_pair h, add_zero]

theorem polar_cmb_of_crd_eq_zero {r : V} (hr : crd P₁ P₂ r = 0) (t : Fin 4 → ZMod 2) :
    polar Q (cmb P₁ P₂ t) r = 0 := by
  have h0 : polar Q r P₁.f = 0 := by simpa [crd] using congrFun hr 0
  have h1 : polar Q r P₂.f = 0 := by simpa [crd] using congrFun hr 1
  have h2 : polar Q r P₂.e = 0 := by simpa [crd] using congrFun hr 2
  have h3 : polar Q r P₁.e = 0 := by simpa [crd] using congrFun hr 3
  simp only [cmb, polar_add_left, polar_smul_left_eq, polar_comm Q P₁.e r, polar_comm Q P₁.f r,
    polar_comm Q P₂.e r, polar_comm Q P₂.f r, h0, h1, h2, h3, mul_zero, add_zero]

variable (P₁ P₂) in
@[expose] noncomputable def gLin (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : V →ₗ[ZMod 2] V where
  toFun w := w + cmb P₁ P₂ ((M - 1) *ᵥ crd P₁ P₂ w)
  map_add' u w := by
    rw [crd_add, Matrix.mulVec_add, cmb_add]
    abel
  map_smul' c w := by
    rw [crd_smul, Matrix.mulVec_smul, cmb_smul, RingHom.id_apply, smul_add]

variable (P₁ P₂) in
theorem gLin_apply (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w : V) :
    gLin P₁ P₂ M w = w + cmb P₁ P₂ ((M - 1) *ᵥ crd P₁ P₂ w) := rfl

theorem crd_gLin (h : P₁.Orth P₂) (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w : V) :
    crd P₁ P₂ (gLin P₁ P₂ M w) = M *ᵥ crd P₁ P₂ w := by
  rw [gLin_apply, crd_add, crd_cmb h, Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

theorem gLin_gLin (h : P₁.Orth P₂) (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) (w : V) :
    gLin P₁ P₂ M (gLin P₁ P₂ N w) = gLin P₁ P₂ (M * N) w := by
  rw [gLin_apply P₁ P₂ M, crd_gLin h, gLin_apply, gLin_apply, add_assoc, ← cmb_add]
  congr 2
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_mulVec]
  abel

variable (P₁ P₂) in
theorem gLin_one (w : V) : gLin P₁ P₂ 1 w = w := by
  rw [gLin_apply, sub_self, Matrix.zero_mulVec, cmb_zero, add_zero]

variable (P₁ P₂) in
theorem gLin_of_crd_eq_zero (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) {w : V}
    (hw : crd P₁ P₂ w = 0) : gLin P₁ P₂ M w = w := by
  rw [gLin_apply, hw, Matrix.mulVec_zero, cmb_zero, add_zero]

theorem Q_gLin (h : P₁.Orth P₂) (M : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hM : ∀ t : Fin 4 → ZMod 2,
      (M *ᵥ t) 0 * (M *ᵥ t) 3 + (M *ᵥ t) 1 * (M *ᵥ t) 2 = t 0 * t 3 + t 1 * t 2)
    (w : V) : Q (gLin P₁ P₂ M w) = Q w := by
  have hcr : crd P₁ P₂ (w - cmb P₁ P₂ (crd P₁ P₂ w)) = 0 := by
    rw [sub_eq_add_neg, crd_add, ← neg_one_smul (ZMod 2) (cmb P₁ P₂ (crd P₁ P₂ w)), crd_smul,
      crd_cmb h, neg_one_smul, add_neg_cancel]
  have hw : Q w = Q (cmb P₁ P₂ (crd P₁ P₂ w) + (w - cmb P₁ P₂ (crd P₁ P₂ w))) := by
    congr 1
    abel
  have hg : gLin P₁ P₂ M w =
      cmb P₁ P₂ (M *ᵥ crd P₁ P₂ w) + (w - cmb P₁ P₂ (crd P₁ P₂ w)) := by
    have e1 : cmb P₁ P₂ (M *ᵥ crd P₁ P₂ w) =
        cmb P₁ P₂ ((M - 1) *ᵥ crd P₁ P₂ w) + cmb P₁ P₂ (crd P₁ P₂ w) := by
      rw [← cmb_add, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    rw [gLin_apply, e1]
    abel
  rw [hg, hw, QuadraticMap.map_add Q, QuadraticMap.map_add Q, polar_cmb_of_crd_eq_zero hcr,
    polar_cmb_of_crd_eq_zero hcr, Q_cmb h, Q_cmb h, hM]

variable (P₁ P₂) in
@[expose] noncomputable def gEquiv (h : P₁.Orth P₂) (M : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hM : M * M * M = 1) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofLinearMap (gLin P₁ P₂ M) (gLin P₁ P₂ (M * M))
    (LinearMap.ext fun w => by
      rw [LinearMap.comp_apply, gLin_gLin h, ← mul_assoc, hM, gLin_one, LinearMap.id_apply])
    (LinearMap.ext fun w => by
      rw [LinearMap.comp_apply, gLin_gLin h, hM, gLin_one, LinearMap.id_apply])

end Coordinates

@[expose] def matL : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1]

@[expose] def matR : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

theorem matL_cube : matL * matL * matL = 1 := by decide

theorem matR_cube : matR * matR * matR = 1 := by decide

theorem matL_mul_matR : matL * matR = matR * matL := by decide

theorem forall_fin_four {P : (Fin 4 → ZMod 2) → Prop}
    (h : ∀ a b c d : ZMod 2, P ![a, b, c, d]) (t : Fin 4 → ZMod 2) : P t := by
  have ht : t = ![t 0, t 1, t 2, t 3] := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  exact h _ _ _ _

theorem matL_det (t : Fin 4 → ZMod 2) :
    (matL *ᵥ t) 0 * (matL *ᵥ t) 3 + (matL *ᵥ t) 1 * (matL *ᵥ t) 2 = t 0 * t 3 + t 1 * t 2 :=
  forall_fin_four (P := fun t =>
    (matL *ᵥ t) 0 * (matL *ᵥ t) 3 + (matL *ᵥ t) 1 * (matL *ᵥ t) 2 = t 0 * t 3 + t 1 * t 2)
    (by decide) t

theorem matR_det (t : Fin 4 → ZMod 2) :
    (matR *ᵥ t) 0 * (matR *ᵥ t) 3 + (matR *ᵥ t) 1 * (matR *ᵥ t) 2 = t 0 * t 3 + t 1 * t 2 :=
  forall_fin_four (P := fun t =>
    (matR *ᵥ t) 0 * (matR *ᵥ t) 3 + (matR *ᵥ t) 1 * (matR *ᵥ t) 2 = t 0 * t 3 + t 1 * t 2)
    (by decide) t

theorem mulVec_ne :
    matL *ᵥ ![1, 0, 0, 0] ≠ ![1, 0, 0, 0] ∧ matR *ᵥ ![1, 0, 0, 0] ≠ ![1, 0, 0, 0] ∧
      matL *ᵥ ![1, 0, 0, 0] ≠ matR *ᵥ ![1, 0, 0, 0] ∧
      (matL * matL) *ᵥ ![1, 0, 0, 0] ≠ matR *ᵥ ![1, 0, 0, 0] := by
  decide

section E9

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem exists_e9_of_hypPairs {P₁ P₂ : HypPair Q} (h : P₁.Orth P₂) {v : V}
    (hv : crd P₁ P₂ v = 0) :
    ∃ x y : V ≃ₗ[ZMod 2] V, (∀ w, Q (x w) = Q w) ∧ (∀ w, Q (y w) = Q w) ∧ x ^ 3 = 1 ∧
      y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x ^ 2 ≠ y ∧ x v = v ∧ y v = v := by
  set x := gEquiv P₁ P₂ h matL matL_cube with hx
  set y := gEquiv P₁ P₂ h matR matR_cube with hy
  have hxw : ∀ w, x w = gLin P₁ P₂ matL w := fun w => rfl
  have hyw : ∀ w, y w = gLin P₁ P₂ matR w := fun w => rfl
  obtain ⟨n1, n2, n3, n4⟩ := mulVec_ne
  refine ⟨x, y, fun w => by rw [hxw, Q_gLin h matL matL_det],
    fun w => by rw [hyw, Q_gLin h matR matR_det], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hxw, gLin_of_crd_eq_zero P₁ P₂ matL hv], by rw [hyw, gLin_of_crd_eq_zero P₁ P₂ matR hv]⟩
  · refine LinearEquiv.ext fun w => ?_
    rw [pow_three]
    show gLin P₁ P₂ matL (gLin P₁ P₂ matL (gLin P₁ P₂ matL w)) = w
    rw [gLin_gLin h, gLin_gLin h, matL_cube, gLin_one]
  · refine LinearEquiv.ext fun w => ?_
    rw [pow_three]
    show gLin P₁ P₂ matR (gLin P₁ P₂ matR (gLin P₁ P₂ matR w)) = w
    rw [gLin_gLin h, gLin_gLin h, matR_cube, gLin_one]
  · refine LinearEquiv.ext fun w => ?_
    show gLin P₁ P₂ matL (gLin P₁ P₂ matR w) = gLin P₁ P₂ matR (gLin P₁ P₂ matL w)
    rw [gLin_gLin h, gLin_gLin h, matL_mul_matR]
  · intro h1
    have h2 : crd P₁ P₂ (x P₁.e) = crd P₁ P₂ P₁.e := by rw [h1]; rfl
    rw [hxw, crd_gLin h, crd_e h] at h2
    exact n1 h2
  · intro h1
    have h2 : crd P₁ P₂ (y P₁.e) = crd P₁ P₂ P₁.e := by rw [h1]; rfl
    rw [hyw, crd_gLin h, crd_e h] at h2
    exact n2 h2
  · intro h1
    have h2 : crd P₁ P₂ (x P₁.e) = crd P₁ P₂ (y P₁.e) := by rw [h1]
    rw [hxw, hyw, crd_gLin h, crd_gLin h, crd_e h] at h2
    exact n3 h2
  · intro h1
    have h2 : crd P₁ P₂ ((x ^ 2) P₁.e) = crd P₁ P₂ (y P₁.e) := by rw [h1]
    have h3 : (x ^ 2) P₁.e = gLin P₁ P₂ (matL * matL) P₁.e := by
      rw [pow_two]
      show gLin P₁ P₂ matL (gLin P₁ P₂ matL P₁.e) = _
      rw [gLin_gLin h]
    rw [h3, hyw, crd_gLin h, crd_gLin h, crd_e h] at h2
    exact n4 h2

theorem exists_two_hypPairs_perp [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    {T : Submodule (ZMod 2) V} (hT : finrank (ZMod 2) T = 3) (hTs : ∀ x ∈ T, Q x = 0)
    {v : V} (hv : v ≠ 0) : ∃ P₁ P₂ : HypPair Q, P₁.Orth P₂ ∧ crd P₁ P₂ v = 0 := by
  obtain ⟨b, hbQ, -, -, -, -⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.orthogonal_geometry_split_Witt_flags hQ (r := 3)
      (by omega) ⟨T, hT, hTs⟩).1 0 (Nat.zero_le 3) (fun _ => ⊥)
      (fun i hi => by simp only [finrank_bot]; omega)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx, QuadraticMap.map_zero])
  obtain ⟨j, hj⟩ : ∃ j, polar Q v (b j) ≠ 0 := by
    by_contra! hall
    apply hv
    apply eq_zero_of_polar_eq_zero hQ
    intro y
    have h0 : polarBilin Q v = 0 := b.ext fun j => by simpa using hall j
    simpa using LinearMap.congr_fun h0 y
  have hbj : Q (b j) = 0 := by
    rcases j with i | i
    exacts [(hbQ i).1, (hbQ i).2]
  have h1 : polar Q (b j) v = 1 := by
    rw [polar_comm]
    exact (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hj
  set P₀ := HypPair.ofPolarEqOne hbj h1 with hP₀
  have hv₀ : v = P₀.f + Q v • P₀.e := by
    rw [hP₀, HypPair.ofPolarEqOne_f, HypPair.ofPolarEqOne_e]
    abel
  have hS := HypPair.polarNondegOn_perp hQ P₀
  have hSd : finrank (ZMod 2) P₀.perp = 2 * 2 := by
    have h2 := CFSG.LocalAnalysis.ComponentInitial.finrank_inf_perp_add_two P₀ (S := ⊤)
      Submodule.mem_top Submodule.mem_top
    rw [top_inf_eq, finrank_top, hV] at h2
    omega
  obtain ⟨T', hT'p, hT's, hT'r, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.quadratic_singular_subspace_descent Q P₀.Q_e P₀.polar_ef T
      hTs hT
  have hT'S : T' ≤ P₀.perp := fun x hx => HypPair.mem_perp.2
    ⟨by rw [polar_comm]; exact (hT'p x hx).1, by rw [polar_comm]; exact (hT'p x hx).2⟩
  obtain ⟨P, hPS, hPo, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_hypPairs_of_flag 2 P₀.perp hS hSd T' hT'S hT's
      (by omega) 0 (Nat.zero_le 2) (fun _ => ⊥) bot_le
      (fun i hi => by simp only [finrank_bot]; omega)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
      (fun x hx => by rw [(Submodule.mem_bot _).1 hx, QuadraticMap.map_zero])
  refine ⟨P 0, P 1, hPo 0 1 (by decide), ?_⟩
  have hperp : ∀ x ∈ P₀.perp, polar Q v x = 0 := fun x hx => by
    obtain ⟨he, hf⟩ := HypPair.mem_perp.1 hx
    rw [hv₀, polar_add_left, polar_smul_left_eq, he, hf, mul_zero, add_zero]
  funext i
  fin_cases i <;> simp [crd, hperp _ (hPS 0).1, hperp _ (hPS 0).2, hperp _ (hPS 1).1,
    hperp _ (hPS 1).2]

end E9

theorem mem_of_relIndex_le_two {G : Type*} [Group G] [Finite G] {Γ O : Subgroup G}
    (hidx : Γ.relIndex O ≤ 2) {x : G} (hxO : x ∈ O) (hx3 : x ^ 3 = 1) : x ∈ Γ := by
  have h0 : (Γ.subgroupOf O).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (Γ.subgroupOf O).index ≤ 2 := hidx
  have hmem : (⟨x, hxO⟩ : O) ∈ Γ.subgroupOf O := by
    rcases (by omega : (Γ.subgroupOf O).index = 1 ∨ (Γ.subgroupOf O).index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      exact Subgroup.mem_top _
    · have h4 := Subgroup.sq_mem_of_index_two h2 ((⟨x, hxO⟩ : O) ^ 2)
      have e : ((⟨x, hxO⟩ : O) ^ 2) ^ 2 = ⟨x, hxO⟩ := by
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow]
        rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hx3, one_mul]
      rwa [e] at h4
  exact Subgroup.mem_subgroupOf.1 hmem

theorem exists_e9 {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (h5 : G112Concl5 B Γ) {v : V} (hv : v ≠ 0) :
    ∃ x ∈ Γ, ∃ y ∈ Γ, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧
      x ^ 2 ≠ y ∧ x v = v ∧ y v = v := by
  obtain ⟨hdim, q, hqadd, hqsmul, ⟨S, hSd, hSq⟩, hΓO, hidx⟩ := h5
  have hFD : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hfin : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  have hpolar : ∀ x y, QuadraticMap.polar q x y = B x y := fun x y => by
    rw [QuadraticMap.polar, hqadd]
    ring
  let Q : QuadraticForm (ZMod 2) V := QuadraticMap.ofPolar q
    (fun a x => by rw [hqsmul, smul_eq_mul])
    (fun x x' y => by rw [hpolar, hpolar, hpolar, LinearMap.map_add₂])
    (fun a x y => by rw [hpolar, hpolar, LinearMap.map_smul₂])
  have hQnd : (polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx =>
      hB x fun w => by rw [← hpolar]; exact hx w
  obtain ⟨P₁, P₂, hP, hv0⟩ := exists_two_hypPairs_perp hQnd hdim hSd (fun x hx => hSq x hx) hv
  obtain ⟨x, y, hxQ, hyQ, hx3, hy3, hxy, hx1, hy1, hxy1, hxy2, hxv, hyv⟩ :=
    exists_e9_of_hypPairs hP hv0
  have hxO : x ∈ orthogonalSubgroupOf q := fun w => hxQ w
  have hyO : y ∈ orthogonalSubgroupOf q := fun w => hyQ w
  exact ⟨x, mem_of_relIndex_le_two hidx hxO hx3, y, mem_of_relIndex_le_two hidx hyO hy3, hx3, hy3,
    hxy, hx1, hy1, hxy1, hxy2, hxv, hyv⟩

end L1294E

end CFSG.Quasithin.H13

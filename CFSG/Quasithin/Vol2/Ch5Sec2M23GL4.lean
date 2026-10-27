module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Gamma

public section

namespace CFSG.Quasithin.H13

open CFSG.Fischer
open scoped Matrix

theorem F4.eq_of_code {a b : F4} (h : a.code = b.code) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem F4.cases (c : F4) : c = 0 ∨ c = 1 ∨ c = F4.ω ∨ c = F4.ω + 1 := by
  have h : ∀ c : F4, c.code = (0 : F4).code ∨ c.code = (1 : F4).code ∨ c.code = F4.ω.code ∨
      c.code = (F4.ω + 1).code := by decide
  rcases h c with h | h | h | h
  · exact Or.inl (F4.eq_of_code h)
  · exact Or.inr (Or.inl (F4.eq_of_code h))
  · exact Or.inr (Or.inr (Or.inl (F4.eq_of_code h)))
  · exact Or.inr (Or.inr (Or.inr (F4.eq_of_code h)))

@[expose] def frobF4 : F4 ≃+* F4 where
  toFun a := a * a
  invFun a := a * a
  left_inv a := F4.eq_of_code (by revert a; decide)
  right_inv a := F4.eq_of_code (by revert a; decide)
  map_mul' a b := F4.eq_of_code (by revert a b; decide)
  map_add' a b := F4.eq_of_code (by revert a b; decide)

theorem frobF4_apply (a : F4) : frobF4 a = a * a := rfl

theorem card_GL_F4 : Nat.card (GL (Fin 2) F4) = 180 := by
  rw [Matrix.card_GL_field, F4.card]
  simp [Fin.prod_univ_two]

theorem card_gammaL2_F4_le : Nat.card (GammaL2 F4) ≤ 360 := by
  have hK : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  choose A σ hAσ using fun f : GammaL2 F4 => exists_isSemilin f.2
  let ι : GammaL2 F4 → GL (Fin 2) F4 × Bool := fun f => (A f, decide ((σ f F4.ω).code = F4.ω.code))
  have hι : Function.Injective ι := by
    intro f g hfg
    simp only [ι, Prod.mk.injEq] at hfg
    obtain ⟨hA, hb⟩ := hfg
    have hσ : σ f = σ g := by
      rcases ringEquiv_eq_refl_or_sq hK (σ f) with h1 | h1 <;>
        rcases ringEquiv_eq_refl_or_sq hK (σ g) with h2 | h2
      · rw [h1, h2]
      · exfalso
        rw [h1, h2, RingEquiv.refl_apply, pow_two] at hb
        revert hb
        decide
      · exfalso
        rw [h1, h2, RingEquiv.refl_apply, pow_two] at hb
        revert hb
        decide
      · exact RingEquiv.ext fun c => by rw [h1, h2]
    apply Subtype.ext
    apply Equiv.ext
    intro v
    rw [hAσ f v, hAσ g v, hA, hσ]
  have h := Nat.card_le_card_of_injective ι hι
  rw [Nat.card_prod, card_GL_F4, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

section Semilinear

variable {K : Type} [Field K]

@[expose] def fieldPerm (σ : K ≃+* K) : Equiv.Perm (Fin 2 → K) where
  toFun v i := σ (v i)
  invFun v i := σ.symm (v i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp

theorem fieldPerm_mem (σ : K ≃+* K) : fieldPerm σ ∈ GammaL2 K :=
  Subgroup.subset_closure (Or.inr ⟨σ, fun _ => rfl⟩)

theorem mem_gammaL2_of_semilinear (f : Equiv.Perm (Fin 2 → K)) (σ : K ≃+* K)
    (hadd : ∀ v w, f (v + w) = f v + f w) (hsmul : ∀ (c : K) v, f (c • v) = σ c • f v) :
    f ∈ GammaL2 K := by
  classical
  set g : Equiv.Perm (Fin 2 → K) := f * (fieldPerm σ)⁻¹ with hg
  have hgv : ∀ v, g v = f (fun i => σ.symm (v i)) := fun v => rfl
  let gl : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := g
      map_add' := fun v w => by
        rw [hgv, hgv, hgv, ← hadd]
        congr 1
        funext i
        simp
      map_smul' := fun c v => by
        rw [hgv, hgv, RingHom.id_apply]
        have e : (fun i => σ.symm ((c • v) i)) = σ.symm c • (fun i => σ.symm (v i)) := by
          funext i
          simp
        rw [e, hsmul, RingEquiv.apply_symm_apply] }
  have hBv : ∀ v, LinearMap.toMatrix' gl *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec gl v
  have hdet : (LinearMap.toMatrix' gl).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hBv] at hv
    have h00 : g 0 = 0 := gl.map_zero
    exact hv0 (g.injective (hv.trans h00.symm))
  have hgmem : g ∈ GammaL2 K := by
    have e : g = linPerm (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) := by
      ext v i
      rw [← hBv]
      rfl
    rw [e]
    exact linPerm_mem _
  have hf : f = g * fieldPerm σ := by
    rw [hg, inv_mul_cancel_right]
  rw [hf]
  exact Subgroup.mul_mem _ hgmem (fieldPerm_mem σ)

end Semilinear

theorem smul_of_add_of_omega (f : Equiv.Perm (Fin 2 → F4)) (σ : F4 ≃+* F4)
    (hadd : ∀ v w, f (v + w) = f v + f w) (hω : ∀ v, f (F4.ω • v) = σ F4.ω • f v) :
    ∀ (c : F4) v, f (c • v) = σ c • f v := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    calc f 0 = f 0 + f 0 - f 0 := by rw [add_sub_cancel_right]
      _ = f 0 - f 0 := by rw [← h]
      _ = 0 := sub_self _
  intro c v
  rcases F4.cases c with rfl | rfl | rfl | rfl
  · rw [zero_smul, h0, map_zero, zero_smul]
  · rw [one_smul, map_one, one_smul]
  · exact hω v
  · rw [add_smul, one_smul, hadd, hω, map_add, map_one, add_smul, one_smul]

@[expose] def f4b0 (a : F4) : Bool := a.code.val % 2 == 1

@[expose] def f4b1 (a : F4) : Bool := a.code.val / 2 == 1

theorem f4b0_add : ∀ a b : F4, f4b0 (a + b) = xor (f4b0 a) (f4b0 b) := by decide

theorem f4b1_add : ∀ a b : F4, f4b1 (a + b) = xor (f4b1 a) (f4b1 b) := by decide

theorem f4b0_omega_mul : ∀ a : F4, f4b0 (F4.ω * a) = f4b1 a := by decide

theorem f4b1_omega_mul : ∀ a : F4, f4b1 (F4.ω * a) = xor (f4b0 a) (f4b1 a) := by decide

theorem eq_zero_of_f4b (a : F4) (h0 : f4b0 a = false) (h1 : f4b1 a = false) : a = 0 := by
  have h : ∀ a : F4, f4b0 a = false → f4b1 a = false → a.code = (0 : F4).code := by decide
  exact F4.eq_of_code (h a h0 h1)

variable {G : Type} [Group G]

@[expose] def cnd (p : Bool) (t : G) : G := bif p then t else 1

theorem cnd_xor {t : G} (ht : t * t = 1) (p q : Bool) :
    cnd (xor p q) t = cnd p t * cnd q t := by
  cases p <;> cases q <;> simp [cnd, ht]

theorem cnd_mul (p : Bool) (t s : G) : cnd p (t * s) = cnd p t * cnd p s := by
  cases p <;> simp [cnd]

theorem cnd_conj (p : Bool) (g t : G) : g * cnd p t * g⁻¹ = cnd p (g * t * g⁻¹) := by
  cases p <;> simp [cnd]

theorem cnd_mem {V : Subgroup G} (p : Bool) {t : G} (ht : t ∈ V) : cnd p t ∈ V := by
  cases p
  · exact V.one_mem
  · exact ht

structure IsFpfThree (V : Subgroup G) (x : G) : Prop where
  sq : ∀ v ∈ V, v * v = 1
  comm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  conj_mem : ∀ v ∈ V, x * v * x⁻¹ ∈ V
  fpf : ∀ v ∈ V, x * v = v * x → v = 1
  cube : x ^ 3 = 1

@[expose] def smV (x : G) (a : F4) (v : G) : G := cnd (f4b0 a) v * cnd (f4b1 a) (x * v * x⁻¹)

theorem smV_zero (x v : G) : smV x 0 v = 1 := by
  rw [smV, show f4b0 (0 : F4) = false by decide, show f4b1 (0 : F4) = false by decide]
  simp [cnd]

theorem smV_one (x v : G) : smV x 1 v = v := by
  rw [smV, show f4b0 (1 : F4) = true by decide, show f4b1 (1 : F4) = false by decide]
  simp [cnd]

theorem smV_omega (x v : G) : smV x F4.ω v = x * v * x⁻¹ := by
  rw [smV, show f4b0 F4.ω = false by decide, show f4b1 F4.ω = true by decide]
  simp [cnd]

namespace IsFpfThree

variable {V : Subgroup G} {x : G}

theorem cube3 (h : IsFpfThree V x) : x * x * x = 1 := by
  rw [← pow_three']
  exact h.cube

theorem conj_conj (h : IsFpfThree V x) {v : G} (hv : v ∈ V) :
    x * (x * v * x⁻¹) * x⁻¹ = v * (x * v * x⁻¹) := by
  have hw1 : x * v * x⁻¹ ∈ V := h.conj_mem v hv
  have hw2 : x * (x * v * x⁻¹) * x⁻¹ ∈ V := h.conj_mem _ hw1
  have hw3 : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v := by
    have e : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * v * (x * x * x)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [e, h.cube3]
    simp
  have hwV : v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) ∈ V :=
    V.mul_mem (V.mul_mem hv hw1) hw2
  have hxw : x * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) =
      v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * x := by
    have e : x * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) =
        (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) * x := by
      group
    rw [e, hw3, h.comm _ (V.mul_mem hw1 hw2) v hv, ← mul_assoc]
  have h1 := h.fpf _ hwV hxw
  have hinv : (v * (x * v * x⁻¹))⁻¹ = v * (x * v * x⁻¹) :=
    inv_eq_of_mul_eq_one_right (h.sq _ (V.mul_mem hv hw1))
  rw [← hinv]
  exact eq_inv_of_mul_eq_one_right h1

theorem smV_mem (h : IsFpfThree V x) {v : G} (hv : v ∈ V) (a : F4) : smV x a v ∈ V :=
  V.mul_mem (cnd_mem _ hv) (cnd_mem _ (h.conj_mem v hv))

theorem smV_add (h : IsFpfThree V x) {v : G} (hv : v ∈ V) (a b : F4) :
    smV x (a + b) v = smV x a v * smV x b v := by
  have hw : x * v * x⁻¹ ∈ V := h.conj_mem v hv
  rw [smV, smV, smV, f4b0_add, f4b1_add, cnd_xor (h.sq v hv), cnd_xor (h.sq _ hw)]
  calc cnd (f4b0 a) v * cnd (f4b0 b) v *
        (cnd (f4b1 a) (x * v * x⁻¹) * cnd (f4b1 b) (x * v * x⁻¹))
      = cnd (f4b0 a) v * (cnd (f4b0 b) v * cnd (f4b1 a) (x * v * x⁻¹)) *
          cnd (f4b1 b) (x * v * x⁻¹) := by simp only [mul_assoc]
    _ = cnd (f4b0 a) v * (cnd (f4b1 a) (x * v * x⁻¹) * cnd (f4b0 b) v) *
          cnd (f4b1 b) (x * v * x⁻¹) := by
        rw [h.comm _ (cnd_mem (f4b0 b) hv) _ (cnd_mem (f4b1 a) hw)]
    _ = cnd (f4b0 a) v * cnd (f4b1 a) (x * v * x⁻¹) *
          (cnd (f4b0 b) v * cnd (f4b1 b) (x * v * x⁻¹)) := by simp only [mul_assoc]

theorem smV_omega_mul (h : IsFpfThree V x) {v : G} (hv : v ∈ V) (a : F4) :
    smV x (F4.ω * a) v = x * smV x a v * x⁻¹ := by
  have hw : x * v * x⁻¹ ∈ V := h.conj_mem v hv
  have e1 : x * smV x a v * x⁻¹ =
      (x * cnd (f4b0 a) v * x⁻¹) * (x * cnd (f4b1 a) (x * v * x⁻¹) * x⁻¹) := by
    rw [smV]
    group
  rw [e1, cnd_conj, cnd_conj, h.conj_conj hv, cnd_mul (f4b1 a) v (x * v * x⁻¹), smV,
    f4b0_omega_mul, f4b1_omega_mul,
    cnd_xor (h.sq _ hw), ← mul_assoc, h.comm _ (cnd_mem (f4b1 a) hv) _ (cnd_mem (f4b0 a) hw),
    mul_assoc]

theorem smV_mul (h : IsFpfThree V x) {v : G} (hv : v ∈ V) (a b : F4) :
    smV x a (smV x b v) = smV x (a * b) v := by
  have hbv := h.smV_mem hv b
  rcases F4.cases a with rfl | rfl | rfl | rfl
  · rw [smV_zero, zero_mul, smV_zero]
  · rw [smV_one, one_mul]
  · rw [smV_omega, h.smV_omega_mul hv]
  · rw [h.smV_add hbv, smV_omega, smV_one, add_mul, one_mul, h.smV_add hv, h.smV_omega_mul hv]

theorem eq_zero_of_smV_eq_one (h : IsFpfThree V x) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) {a : F4}
    (ha : smV x a v = 1) : a = 0 := by
  rw [smV] at ha
  cases h0 : f4b0 a <;> cases h1 : f4b1 a <;> rw [h0, h1] at ha
  · exact eq_zero_of_f4b a h0 h1
  · exfalso
    apply hv1
    have e : x * v * x⁻¹ = 1 := by simpa [cnd] using ha
    calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  · exfalso
    exact hv1 (by simpa [cnd] using ha)
  · exfalso
    apply hv1
    have e : v * (x * v * x⁻¹) = 1 := by simpa [cnd] using ha
    have e2 : x * v * x⁻¹ = v := by
      rw [eq_inv_of_mul_eq_one_right e, inv_eq_of_mul_eq_one_right (h.sq v hv)]
    exact h.fpf v hv (by
      calc x * v = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [e2])

end IsFpfThree

@[expose] def phiV (x v₁ v₂ : G) (c : Fin 2 → F4) : G := smV x (c 0) v₁ * smV x (c 1) v₂

namespace IsFpfThree

variable {V : Subgroup G} {x v₁ v₂ : G}

theorem phiV_mem (h : IsFpfThree V x) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (c : Fin 2 → F4) :
    phiV x v₁ v₂ c ∈ V :=
  V.mul_mem (h.smV_mem hv₁ _) (h.smV_mem hv₂ _)

theorem phiV_add (h : IsFpfThree V x) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (c d : Fin 2 → F4) :
    phiV x v₁ v₂ (c + d) = phiV x v₁ v₂ c * phiV x v₁ v₂ d := by
  rw [phiV, phiV, phiV, Pi.add_apply, Pi.add_apply, h.smV_add hv₁, h.smV_add hv₂]
  calc smV x (c 0) v₁ * smV x (d 0) v₁ * (smV x (c 1) v₂ * smV x (d 1) v₂)
      = smV x (c 0) v₁ * (smV x (d 0) v₁ * smV x (c 1) v₂) * smV x (d 1) v₂ := by
        simp only [mul_assoc]
    _ = smV x (c 0) v₁ * (smV x (c 1) v₂ * smV x (d 0) v₁) * smV x (d 1) v₂ := by
        rw [h.comm _ (h.smV_mem hv₁ _) _ (h.smV_mem hv₂ _)]
    _ = smV x (c 0) v₁ * smV x (c 1) v₂ * (smV x (d 0) v₁ * smV x (d 1) v₂) := by
        simp only [mul_assoc]

theorem phiV_omega (h : IsFpfThree V x) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (c : Fin 2 → F4) :
    phiV x v₁ v₂ (F4.ω • c) = x * phiV x v₁ v₂ c * x⁻¹ := by
  rw [phiV, phiV, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, h.smV_omega_mul hv₁,
    h.smV_omega_mul hv₂]
  group

theorem eq_zero_of_phiV_eq_one (h : IsFpfThree V x) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V)
    (hv₁1 : v₁ ≠ 1) (hline : ∀ a : F4, smV x a v₁ ≠ v₂) {c : Fin 2 → F4}
    (hc : phiV x v₁ v₂ c = 1) : c = 0 := by
  rw [phiV] at hc
  have hc' : smV x (c 1) v₂ = smV x (c 0) v₁ := by
    rw [eq_inv_of_mul_eq_one_right hc, inv_eq_of_mul_eq_one_right (h.sq _ (h.smV_mem hv₁ _))]
  have hc1 : c 1 = 0 := by
    by_contra hne
    apply hline ((c 1)⁻¹ * c 0)
    rw [← h.smV_mul hv₁, ← hc', h.smV_mul hv₂, inv_mul_cancel₀ hne, smV_one]
  have hc0 : c 0 = 0 := by
    rw [hc1, smV_zero] at hc'
    exact h.eq_zero_of_smV_eq_one hv₁ hv₁1 hc'.symm
  funext i
  fin_cases i
  · exact hc0
  · exact hc1

theorem phiV_injective (h : IsFpfThree V x) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (hv₁1 : v₁ ≠ 1)
    (hline : ∀ a : F4, smV x a v₁ ≠ v₂) : Function.Injective (phiV x v₁ v₂) := by
  intro c d hcd
  have h1 : phiV x v₁ v₂ (c + d) = 1 := by
    rw [h.phiV_add hv₁ hv₂, hcd]
    exact h.sq _ (h.phiV_mem hv₁ hv₂ d)
  have h2 := h.eq_zero_of_phiV_eq_one hv₁ hv₂ hv₁1 hline h1
  exact (eq_neg_of_add_eq_zero_left h2).trans (funext fun _ => rfl)

theorem exists_basis (_h : IsFpfThree V x) (hV : Nat.card V = 16) :
    ∃ v₁ ∈ V, ∃ v₂ ∈ V, v₁ ≠ 1 ∧ ∀ a : F4, smV x a v₁ ≠ v₂ := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : ↥V, v₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card V ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => by rw [hcon a, hcon b]⟩
    omega
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : ↥V, ∀ a : F4, smV x a (v₁ : G) ≠ v₂ := by
    by_contra hcon
    push Not at hcon
    choose f hf using hcon
    have hinj : Function.Injective f := fun u w huw =>
      Subtype.ext (by rw [← hf u, ← hf w, huw])
    have h1 := Nat.card_le_card_of_injective f hinj
    rw [hV, Nat.card_eq_fintype_card (α := F4), F4.card] at h1
    omega
  exact ⟨v₁, v₁.2, v₂, v₂.2, fun h1 => hv₁ (Subtype.ext h1), hv₂⟩

@[expose] noncomputable def phiEquiv (h : IsFpfThree V x) (hV : Nat.card V = 16)
    (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V) (hv₁1 : v₁ ≠ 1) (hline : ∀ a : F4, smV x a v₁ ≠ v₂) :
    (Fin 2 → F4) ≃ ↥V :=
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  Equiv.ofBijective (fun c => ⟨phiV x v₁ v₂ c, h.phiV_mem hv₁ hv₂ c⟩) (by
    refine Function.Injective.bijective_of_nat_card_le ?_ ?_
    · intro c d hcd
      exact h.phiV_injective hv₁ hv₂ hv₁1 hline (congrArg Subtype.val hcd)
    · rw [hV, Nat.card_eq_fintype_card]
      simp [F4.card])

end IsFpfThree

@[expose] noncomputable def actHom {V N : Subgroup G} (e : (Fin 2 → F4) ≃ ↥V)
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) : ↥N →* Equiv.Perm (Fin 2 → F4) :=
  (e.symm.permCongrHom.toMonoidHom).comp
    ((MulAut.toPerm ↥V).comp (V.normalizerMonoidHom.comp (Subgroup.inclusion hNV)))

theorem coe_e_actHom {V N : Subgroup G} (e : (Fin 2 → F4) ≃ ↥V)
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) (n : ↥N) (c : Fin 2 → F4) :
    ((e (actHom e hNV n c) : ↥V) : G) = (n : G) * (e c : G) * (n : G)⁻¹ := by
  have e1 : actHom e hNV n c =
      e.symm (V.normalizerMonoidHom (Subgroup.inclusion hNV n) (e c)) := rfl
  rw [e1, Equiv.apply_symm_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem nonempty_mulEquiv_gammaL2 {V N : Subgroup G} {x : G} (h : IsFpfThree V x)
    (hV : Nat.card V = 16) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (hNx : ∀ n ∈ N, n * x * n⁻¹ = x ∨ n * x * n⁻¹ = x⁻¹)
    (hinj : ∀ n ∈ N, (∀ v ∈ V, n * v = v * n) → n = 1) (hN : Nat.card N = 360) :
    Nonempty (↥N ≃* ↥(GammaL2 F4)) := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hv₁1, hline⟩ := h.exists_basis hV
  set e := h.phiEquiv hV hv₁ hv₂ hv₁1 hline with he
  have hecoe : ∀ c, ((e c : ↥V) : G) = phiV x v₁ v₂ c := fun c => rfl
  have hxx : x * x = x⁻¹ := (inv_eq_of_mul_eq_one_left h.cube3).symm
  have hconj3 : ∀ B : G, x⁻¹ * B * x = x * (x * B * x⁻¹) * x⁻¹ := by
    intro B
    refine (?_ : x * (x * B * x⁻¹) * x⁻¹ = x⁻¹ * B * x).symm
    calc x * (x * B * x⁻¹) * x⁻¹ = (x * x) * B * (x⁻¹ * x⁻¹) := by simp only [mul_assoc]
      _ = x⁻¹ * B * x := by rw [hxx, ← mul_inv_rev, hxx, inv_inv]
  have hρ := coe_e_actHom e hNV
  have hinjE : ∀ c d, ((e c : ↥V) : G) = (e d : G) → c = d := fun c d hcd =>
    e.injective (Subtype.ext hcd)
  have hadd : ∀ (n : ↥N) c d, actHom e hNV n (c + d) = actHom e hNV n c + actHom e hNV n d := by
    intro n c d
    apply hinjE
    rw [hρ, hecoe (c + d), hecoe (actHom e hNV n c + actHom e hNV n d), h.phiV_add hv₁ hv₂,
      h.phiV_add hv₁ hv₂, ← hecoe c, ← hecoe d, ← hecoe (actHom e hNV n c),
      ← hecoe (actHom e hNV n d), hρ, hρ]
    group
  have hmem : ∀ n : ↥N, actHom e hNV n ∈ GammaL2 F4 := by
    intro n
    rcases hNx n n.2 with hn | hn
    · refine mem_gammaL2_of_semilinear _ (RingEquiv.refl F4) (hadd n)
        (smul_of_add_of_omega _ _ (hadd n) fun c => ?_)
      apply hinjE
      rw [RingEquiv.refl_apply, hρ, hecoe (F4.ω • c), hecoe (F4.ω • actHom e hNV n c),
        h.phiV_omega hv₁ hv₂, h.phiV_omega hv₁ hv₂, ← hecoe (actHom e hNV n c), hρ]
      calc (n : G) * (x * phiV x v₁ v₂ c * x⁻¹) * (n : G)⁻¹
          = ((n : G) * x * (n : G)⁻¹) * ((n : G) * phiV x v₁ v₂ c * (n : G)⁻¹) *
              ((n : G) * x * (n : G)⁻¹)⁻¹ := by group
        _ = x * ((n : G) * phiV x v₁ v₂ c * (n : G)⁻¹) * x⁻¹ := by rw [hn]
        _ = x * ((n : G) * (e c : G) * (n : G)⁻¹) * x⁻¹ := by rw [hecoe]
    · refine mem_gammaL2_of_semilinear _ frobF4 (hadd n)
        (smul_of_add_of_omega _ _ (hadd n) fun c => ?_)
      apply hinjE
      rw [frobF4_apply, mul_smul, hρ, hecoe (F4.ω • c), hecoe (F4.ω • F4.ω • actHom e hNV n c),
        h.phiV_omega hv₁ hv₂, h.phiV_omega hv₁ hv₂, h.phiV_omega hv₁ hv₂,
        ← hecoe (actHom e hNV n c), hρ]
      calc (n : G) * (x * phiV x v₁ v₂ c * x⁻¹) * (n : G)⁻¹
          = ((n : G) * x * (n : G)⁻¹) * ((n : G) * phiV x v₁ v₂ c * (n : G)⁻¹) *
              ((n : G) * x * (n : G)⁻¹)⁻¹ := by group
        _ = x⁻¹ * ((n : G) * phiV x v₁ v₂ c * (n : G)⁻¹) * x⁻¹⁻¹ := by rw [hn]
        _ = x * (x * ((n : G) * (e c : G) * (n : G)⁻¹) * x⁻¹) * x⁻¹ := by
          rw [hecoe, inv_inv, hconj3]
  let ρ : ↥N →* ↥(GammaL2 F4) := (actHom e hNV).codRestrict (GammaL2 F4) hmem
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro n hn
    have hn1 : actHom e hNV n = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
      exact this
    have hcent : ∀ v ∈ V, (n : G) * v = v * n := by
      intro v hv
      obtain ⟨c, hc⟩ := e.surjective ⟨v, hv⟩
      have h1 := hρ n c
      rw [hn1, Equiv.Perm.one_apply, hc] at h1
      calc (n : G) * v = (n : G) * v * (n : G)⁻¹ * n := by group
        _ = v * n := by rw [← h1]
    exact Subgroup.mem_bot.mpr (Subtype.ext (hinj n n.2 hcent))
  have hbij : Function.Bijective ρ :=
    hρinj.bijective_of_nat_card_le (by rw [hN]; exact card_gammaL2_F4_le)
  exact ⟨MulEquiv.ofBijective ρ hbij⟩

end CFSG.Quasithin.H13

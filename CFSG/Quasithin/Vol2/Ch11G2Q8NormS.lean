module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Norm

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F]

@[expose] def frobQ (σ : F →+* F) (w : Ix3 → F) : Ix3 → F := fun j => σ (w j)

@[expose] def frobZ (σ : F →+* F) (x : quasithinZorn F) : quasithinZorn F :=
  (σ x.1, fun i => σ (x.2.1 i), fun i => σ (x.2.2.1 i), σ x.2.2.2)

theorem frobZ_zmk (σ : F →+* F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    frobZ σ (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk (σ r) (σ u₀) (σ u₁) (σ u₂) (σ v₀) (σ v₁) (σ v₂) (σ s) := by
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl)) <;> funext i <;> fin_cases i <;> rfl

theorem frobZ_add (σ : F →+* F) (x y : quasithinZorn F) :
    frobZ σ (x + y) = frobZ σ x + frobZ σ y := by
  rw [zorn_eta x, zorn_eta y, zmk_add, frobZ_zmk, frobZ_zmk, frobZ_zmk, zmk_add]
  simp only [map_add]

theorem frobZ_smul (σ : F →+* F) (c : F) (x : quasithinZorn F) :
    frobZ σ (c • x) = σ c • frobZ σ x := by
  rw [zorn_eta x, zmk_smul, frobZ_zmk, frobZ_zmk, zmk_smul]
  simp only [map_mul]

theorem frobZ_mul (σ : F →+* F) (x y : quasithinZorn F) :
    frobZ σ (cayleyMul x y) = cayleyMul (frobZ σ x) (frobZ σ y) := by
  rw [zorn_eta x, zorn_eta y, cayleyMul_zmk, frobZ_zmk, frobZ_zmk, frobZ_zmk, cayleyMul_zmk]
  simp only [map_add, map_mul, map_sub]

theorem frobZ_one (σ : F →+* F) : frobZ σ (cayleyOne F) = cayleyOne F := by
  rw [cayleyOne_eq, frobZ_zmk, map_one, map_zero]

theorem cayleyTr_frobZ (σ : F →+* F) (x : quasithinZorn F) :
    cayleyTr (frobZ σ x) = σ (cayleyTr x) := by
  rw [zorn_eta x, frobZ_zmk, cayleyTr_zmk, cayleyTr_zmk, map_add]

theorem cayleyNorm_frobZ (σ : F →+* F) (x : quasithinZorn F) :
    cayleyNorm (frobZ σ x) = σ (cayleyNorm x) := by
  rw [zorn_eta x, frobZ_zmk, cayleyNorm_zmk, cayleyNorm_zmk]
  simp only [map_add, map_mul]

theorem frobZ_symm (σ : F ≃+* F) (x : quasithinZorn F) :
    frobZ (σ : F →+* F) (frobZ (σ.symm : F →+* F) x) = x := by
  rw [zorn_eta x, frobZ_zmk, frobZ_zmk]
  simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

theorem frobZ_symm' (σ : F ≃+* F) (x : quasithinZorn F) :
    frobZ (σ.symm : F →+* F) (frobZ (σ : F →+* F) x) = x := by
  rw [zorn_eta x, frobZ_zmk, frobZ_zmk]
  simp only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

@[expose] def frobLE (σ : F ≃+* F) (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) :
    quasithinZorn F ≃ₗ[F] quasithinZorn F where
  toFun x := frobZ σ (g (frobZ σ.symm x))
  invFun x := frobZ σ (g.symm (frobZ σ.symm x))
  map_add' x y := by rw [frobZ_add, map_add, frobZ_add]
  map_smul' c x := by
    rw [frobZ_smul, map_smul, frobZ_smul, RingHom.id_apply]
    simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  left_inv x := by
    show frobZ σ (g.symm (frobZ σ.symm (frobZ σ (g (frobZ σ.symm x))))) = x
    rw [frobZ_symm', LinearEquiv.symm_apply_apply, frobZ_symm]
  right_inv x := by
    show frobZ σ (g (frobZ σ.symm (frobZ σ (g.symm (frobZ σ.symm x))))) = x
    rw [frobZ_symm', LinearEquiv.apply_symm_apply, frobZ_symm]

theorem frobLE_apply (σ : F ≃+* F) (g : quasithinZorn F ≃ₗ[F] quasithinZorn F)
    (x : quasithinZorn F) : frobLE σ g x = frobZ σ (g (frobZ σ.symm x)) := rfl

@[expose] def frobConj (σ : F ≃+* F) (γ : ↥(cayleyGroup F)) : ↥(cayleyGroup F) :=
  ⟨frobLE σ γ, by
    obtain ⟨h1, hm, ht, hn⟩ := γ.2
    refine ⟨?_, fun x y => ?_, fun x => ?_, fun x => ?_⟩
    · rw [frobLE_apply, frobZ_one, h1, frobZ_one]
    · rw [frobLE_apply, frobLE_apply, frobLE_apply, frobZ_mul, hm, frobZ_mul]
    · rw [frobLE_apply, cayleyTr_frobZ, ht, cayleyTr_frobZ]
      simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    · rw [frobLE_apply, cayleyNorm_frobZ, hn, cayleyNorm_frobZ]
      simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]⟩

theorem cgE_frobConj (σ : F ≃+* F) (γ : ↥(cayleyGroup F)) (x : quasithinZorn F) :
    cgE (frobConj σ γ) x = frobZ σ (cgE γ (frobZ σ.symm x)) := rfl

theorem frobZ_zI (σ : F →+* F) (w : Ix3 → F) : frobZ σ (zI w) = zI (frobQ σ w) := by
  rw [zI, zI, frobZ_zmk, map_zero]
  rfl

theorem zP_frobZ (σ : F →+* F) (x : quasithinZorn F) : zP (frobZ σ x) = frobQ σ (zP x) := by
  funext j
  rcases j with j | j <;> fin_cases j <;> rfl

variable [CharP F 2]

theorem g2Act_frobConj (σ : F ≃+* F) (γ : ↥(cayleyGroup F)) (w : Ix3 → F) :
    g2Act (frobConj σ γ) (frobQ σ w) = frobQ σ (g2Act γ w) := by
  have h1 : frobZ (σ.symm : F →+* F) (zI (frobQ (σ : F →+* F) w)) = zI w := by
    rw [← frobZ_zI, frobZ_symm']
  rw [g2Act_apply, g2Act_apply, cgE_frobConj, h1, zP_frobZ]

omit [CharP F 2] in
theorem frobQ_smul (σ : F →+* F) (c : F) (w : Ix3 → F) :
    frobQ σ (c • w) = σ c • frobQ σ w := by
  funext j
  simp [frobQ]

omit [CharP F 2] in
theorem frobQ_symm (σ : F ≃+* F) (w : Ix3 → F) :
    frobQ (σ : F →+* F) (frobQ (σ.symm : F →+* F) w) = w := by
  funext j
  simp [frobQ]

omit [CharP F 2] in
theorem frobQ_symm' (σ : F ≃+* F) (w : Ix3 → F) :
    frobQ (σ.symm : F →+* F) (frobQ (σ : F →+* F) w) = w := by
  funext j
  simp [frobQ]

theorem exists_eq_smul_frob_of_normG2 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (T : (Ix3 → F) →+ (Ix3 → F)) (hTb : Function.Bijective T) (σ : F ≃+* F)
    (hTσ : ∀ (c : F) (x : Ix3 → F), T (c • x) = σ c • T x)
    (hT : ∀ γ : ↥(cayleyGroup F), ∃ γ' : ↥(cayleyGroup F), ∀ w, T (g2Act γ w) = g2Act γ' (T w)) :
    ∃ (c : F) (h : ↥(cayleyGroup F)), c ≠ 0 ∧ ∀ w, T w = c • g2Act h (frobQ σ w) := by
  set E := Equiv.ofBijective T hTb with hE
  let T' : (Ix3 → F) ≃ₗ[F] (Ix3 → F) :=
    { toFun := fun w => T (frobQ σ.symm w)
      invFun := fun w => frobQ σ (E.symm w)
      map_add' := fun x y => by
        rw [show frobQ (σ.symm : F →+* F) (x + y) =
          frobQ (σ.symm : F →+* F) x + frobQ (σ.symm : F →+* F) y by funext j; simp [frobQ],
          map_add]
      map_smul' := fun c x => by
        rw [frobQ_smul, hTσ, RingHom.id_apply]
        simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
      left_inv := fun x => by
        show frobQ (σ : F →+* F) (E.symm (T (frobQ (σ.symm : F →+* F) x))) = x
        rw [show E.symm (T (frobQ (σ.symm : F →+* F) x)) = frobQ (σ.symm : F →+* F) x from
          E.symm_apply_apply _, frobQ_symm]
      right_inv := fun x => by
        show T (frobQ (σ.symm : F →+* F) (frobQ (σ : F →+* F) (E.symm x))) = x
        rw [frobQ_symm']
        exact E.apply_symm_apply x }
  have hT'app : ∀ w, T' w = T (frobQ σ.symm w) := fun w => rfl
  have hT' : ∀ γ : ↥(cayleyGroup F), ∃ γ' : ↥(cayleyGroup F),
      ∀ w, T' (g2Act γ w) = g2Act γ' (T' w) := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hT (frobConj σ.symm γ)
    refine ⟨γ', fun w => ?_⟩
    rw [hT'app, hT'app, ← hγ', ← g2Act_frobConj]
  obtain ⟨c, h, hc0, hch⟩ := exists_eq_smul_of_normG2 hF hn T' hT'
  refine ⟨c, h, hc0, fun w => ?_⟩
  have h1 := hch (frobQ σ w)
  rwa [hT'app, frobQ_symm'] at h1

end CFSG.Quasithin.Vol2.Ch11.G2Q8

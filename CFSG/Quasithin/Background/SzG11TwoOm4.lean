module

public import CFSG.Quasithin.Background.SzG11TwoCommon
public import CFSG.Quasithin.Background.SzG11TwoOm4Quad

public section

namespace CFSG.Quasithin.G11.SzG11S.Two.Om4

open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K] [Fintype K]

theorem no_semilinear_involution (hK : Fintype.card K = 4) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (G : Subgroup (GL Idx K))
    (hGQ : ∀ g ∈ G, ∀ v, StatedQuadMinus 2 K b c ((g : Matrix Idx Idx K) *ᵥ v) =
      StatedQuadMinus 2 K b c v)
    (hSchur : ∀ A : (Idx → K) →+ (Idx → K),
      (∀ g ∈ G, ∀ v, A ((g : Matrix Idx Idx K) *ᵥ v) = (g : Matrix Idx Idx K) *ᵥ A v) →
        ∃ κ : K, ∀ v, A v = κ • v)
    (x : (Idx → K) →+ (Idx → K)) (hx : ∀ (κ : K) v, x (κ • v) = κ ^ 2 • x v)
    (hxx : ∀ v, x (x v) = v)
    (hnorm : ∀ g ∈ G, ∃ g' ∈ G, ∀ v,
      x ((g : Matrix Idx Idx K) *ᵥ x v) = (g' : Matrix Idx Idx K) *ᵥ v) : False := by
  classical
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_four (by rw [Nat.card_eq_fintype_card, hK])
  have h4 : ∀ κ : K, κ ^ 4 = κ := fun κ => by simpa [hK] using FiniteField.pow_card κ
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨t, ht⟩ := (sq_bijective h2).2 c
    apply hbc t
    rw [hb0, zero_mul, add_zero, ← ht]
    linear_combination (t ^ 2) * h2
  obtain ⟨β, hQ, hβ⟩ := quad_polar h2 b c hb
  have hQs : ∀ (κ : K) v, StatedQuadMinus 2 K b c (κ • v) = κ ^ 2 * StatedQuadMinus 2 K b c v := by
    intro κ v
    simp only [quad_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let Gs : Set ((Idx → K) → (Idx → K)) :=
    {f | ∃ g ∈ G, f = fun v => (g : Matrix Idx Idx K) *ᵥ v}
  have hGs : ∀ f ∈ Gs, ∃ g ∈ G, ∀ v, f v = (g : Matrix Idx Idx K) *ᵥ v := by
    rintro f ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun v => rfl⟩
  obtain ⟨μ, hμ⟩ := exists_scalar_of_invariant h2 h4 (StatedQuadMinus 2 K b c) β hQ hQs hβ x hx Gs
    (fun f hf u v => by
      obtain ⟨g, -, hg⟩ := hGs f hf
      rw [hg, hg, hg, Matrix.mulVec_add])
    (fun f hf κ v => by
      obtain ⟨g, -, hg⟩ := hGs f hf
      rw [hg, hg, Matrix.mulVec_smul])
    (fun f hf y => by
      obtain ⟨g, -, hg⟩ := hGs f hf
      refine ⟨((g⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ y, ?_⟩
      rw [hg, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec])
    (fun f hf v => by
      obtain ⟨g, hg, hfg⟩ := hGs f hf
      rw [hfg]
      exact hGQ g hg v)
    (fun f hf => by
      obtain ⟨g, hg, hfg⟩ := hGs f hf
      obtain ⟨g', hg', hxg⟩ := hnorm g hg
      refine ⟨fun v => (g' : Matrix Idx Idx K) *ᵥ v, ⟨g', hg', rfl⟩, fun v => ?_⟩
      rw [hfg]
      have := hxg (x v)
      rwa [hxx] at this)
    (fun A hA => hSchur A (fun g hg v => hA _ ⟨g, hg, rfl⟩ v))
    not_span_one
  have hμ0 : μ ≠ 0 := by
    intro h0
    have hw : StatedQuadMinus 2 K b c
        (Pi.single (.inl 0) 1 + Pi.single (.inr (.inl 0)) 1 : Idx → K) ≠ 0 := by
      rw [quad_apply]
      simp
    apply hw
    have h := hμ (x (Pi.single (.inl 0) 1 + Pi.single (.inr (.inl 0)) 1))
    rw [hxx, h0, zero_mul] at h
    exact (pow_eq_zero_iff two_ne_zero).1 h
  have hμ3 : μ ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rw [hK] at this
    simpa using this
  let x' : (Idx → K) →+ (Idx → K) :=
    AddMonoidHom.mk' (fun v => μ⁻¹ • x v) (fun a b => by rw [map_add, smul_add])
  have hx'v : ∀ v, x' v = μ⁻¹ • x v := fun v => rfl
  have hx' : ∀ (κ : K) v, x' (κ • v) = κ ^ 2 • x' v := by
    intro κ v
    rw [hx'v, hx'v, hx, smul_comm]
  have hxx' : ∀ v, x' (x' v) = v := by
    intro v
    rw [hx'v, hx'v, hx, hxx, smul_smul]
    have : μ⁻¹ * μ⁻¹ ^ 2 = 1 := by
      rw [← pow_succ', inv_pow, hμ3, inv_one]
    rw [this, one_smul]
  have hQx' : ∀ v, StatedQuadMinus 2 K b c (x' v) = StatedQuadMinus 2 K b c v ^ 2 := by
    intro v
    rw [hx'v, hQs]
    have h1 : StatedQuadMinus 2 K b c (x v) = (μ * StatedQuadMinus 2 K b c v) ^ 2 := by
      rw [← hμ v]
      linear_combination (-1 : K) * h4 (StatedQuadMinus 2 K b c (x v))
    rw [h1]
    field_simp
  have hpos := sum_chi_pos h2 hK (StatedQuadMinus 2 K b c) β hQ hβ.1 x' hx' hxx' hQx'
  rw [sum_chi_quad h2 hK b c hbc] at hpos
  norm_num at hpos

end CFSG.Quasithin.G11.SzG11S.Two.Om4

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SzG11NC
open scoped Matrix

namespace G11

namespace SzG11S

open Two Two.Om4

theorem noConfigOm4MinusTwo : NoConfigOm4MinusTwo := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp b c hbc hnat hex
  classical
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_galoisField_two_two
  have hd : 8 ≤ Module.finrank (ZMod 2) V := eight_le_finrank_of_natural_two (by simp) hnat
  have hirr : IsIrr (normalClosure Γ L) ⊤ := isIrr_top_of_conf hs hp
  obtain ⟨φ, ψ, hψ⟩ := hnat
  have hsc : ∀ κ : GaloisField 2 2, ∀ h ∈ normalClosure Γ L, ∀ v,
      scalarHom ψ κ (h v) = h (scalarHom ψ κ v) := by
    intro κ h hh v
    show scalarEnd ψ κ (h v) = h (scalarEnd ψ κ v)
    rw [scalarEnd_apply, scalarEnd_apply, hψ ⟨h, hh⟩ v]
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply, hψ ⟨h, hh⟩, LinearEquiv.apply_symm_apply,
      Matrix.mulVec_smul]
  have hE : Nat.card (CommF (normalClosure Γ L) hirr) = 4 :=
    card_commF_of_scalars hs hp (GaloisField 2 2) card_galoisField_two_two (scalarHom ψ) hsc
      (by omega)
  obtain ⟨x₀, hx₀X, hx₀sq, hx₀⟩ :=
    exists_frobenius_involution hs.hyp hirr (normalClosure_normal Γ L) hE hex
  have hx₀Γ : x₀ ∈ Γ := hs.hyp.X_le hx₀X
  have hSchur : ∀ A : (Idx → GaloisField 2 2) →+ (Idx → GaloisField 2 2),
      (∀ g ∈ StatedOmega (StatedQuadMinus 2 (GaloisField 2 2) b c), ∀ v,
        A ((g : Matrix Idx Idx (GaloisField 2 2)) *ᵥ v) =
          (g : Matrix Idx Idx (GaloisField 2 2)) *ᵥ A v) →
        ∃ κ : GaloisField 2 2, ∀ v, A v = κ • v := by
    intro A hA
    let fA : V →+ V :=
      ψ.symm.toLinearMap.toAddMonoidHom.comp (A.comp ψ.toLinearMap.toAddMonoidHom)
    have hfA : ∀ v, fA v = ψ.symm (A (ψ v)) := fun v => rfl
    let f : Module.End (ZMod 2) V := fA.toZModLinearMap 2
    have hf : f ∈ endCommutant (normalClosure Γ L) := by
      rw [endCommutant_eq_commutantOf, mem_commutantOf]
      intro h hh v
      show fA (h v) = h (fA v)
      rw [hfA, hfA, hψ ⟨h, hh⟩ v, hA _ (φ ⟨h, hh⟩).2 (ψ v)]
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, hψ ⟨h, hh⟩, LinearEquiv.apply_symm_apply]
    obtain ⟨κ, hκ⟩ := exists_scalar_of_mem_endCommutant hirr (GaloisField 2 2) (scalarHom ψ) hsc
      (by rw [hE, card_galoisField_two_two]) hf
    refine ⟨κ, fun y => ?_⟩
    have h1 : f (ψ.symm y) = scalarHom ψ κ (ψ.symm y) := by rw [hκ]
    have h2 : f (ψ.symm y) = ψ.symm (A y) := by
      show fA (ψ.symm y) = _
      rw [hfA, LinearEquiv.apply_symm_apply]
    have h3 : scalarHom ψ κ (ψ.symm y) = ψ.symm (κ • y) := by
      show scalarEnd ψ κ (ψ.symm y) = _
      rw [scalarEnd_apply, LinearEquiv.apply_symm_apply]
    exact ψ.symm.injective (h2.symm.trans (h1.trans h3))
  let x : (Idx → GaloisField 2 2) →+ (Idx → GaloisField 2 2) :=
    ψ.toLinearMap.toAddMonoidHom.comp
      (((x₀ : GLV V) : V →ₗ[ZMod 2] V).toAddMonoidHom.comp ψ.symm.toLinearMap.toAddMonoidHom)
  have hxv : ∀ y, x y = ψ (x₀ (ψ.symm y)) := fun y => rfl
  have hx : ∀ (κ : GaloisField 2 2) y, x (κ • y) = κ ^ 2 • x y := by
    intro κ y
    let e : CommF (normalClosure Γ L) hirr :=
      CommF.mk (scalarHom ψ κ) (mem_commutantOf.2 (hsc κ))
    have he : ∀ w : V, e • w = ψ.symm (κ • ψ w) := fun w => rfl
    have he2 : ∀ w : V, (e ^ 2) • w = ψ.symm ((κ ^ 2) • ψ w) := by
      intro w
      rw [CommF.smul_def, pow_two, CommF.val_mul]
      show scalarEnd ψ κ (scalarEnd ψ κ w) = _
      rw [scalarEnd_apply, scalarEnd_apply, LinearEquiv.apply_symm_apply, smul_smul, pow_two]
    have h1 : ψ.symm (κ • y) = e • ψ.symm y := by rw [he, LinearEquiv.apply_symm_apply]
    rw [hxv, hxv, h1, hx₀ e, he2, LinearEquiv.apply_symm_apply]
  have hx₀₀ : ∀ w, x₀ (x₀ w) = w := by
    intro w
    have := congrArg (fun g : GLV V => g w) hx₀sq
    simpa using this
  have hxx : ∀ y, x (x y) = y := by
    intro y
    rw [hxv, hxv, LinearEquiv.symm_apply_apply, hx₀₀, LinearEquiv.apply_symm_apply]
  have hinv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hx₀sq
  have hnorm : ∀ g ∈ StatedOmega (StatedQuadMinus 2 (GaloisField 2 2) b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 2 (GaloisField 2 2) b c), ∀ y,
        x ((g : Matrix Idx Idx (GaloisField 2 2)) *ᵥ x y) =
          (g' : Matrix Idx Idx (GaloisField 2 2)) *ᵥ y := by
    intro g hg
    obtain ⟨h, hh⟩ := φ.surjective ⟨g, hg⟩
    have hg' : g = ((φ h : ↥(StatedOmega (StatedQuadMinus 2 (GaloisField 2 2) b c))) :
        GL Idx (GaloisField 2 2)) := (congrArg Subtype.val hh).symm
    subst hg'
    have hh' : x₀ * (h : GLV V) * x₀⁻¹ ∈ normalClosure Γ L :=
      normalClosure_normal Γ L x₀ hx₀Γ h h.2
    refine ⟨_, (φ ⟨_, hh'⟩).2, fun y => ?_⟩
    have e2 : ψ.symm (((φ h : GL Idx (GaloisField 2 2)) : Matrix Idx Idx (GaloisField 2 2)) *ᵥ
        ψ (x₀ (ψ.symm y))) = (h : GLV V) (x₀ (ψ.symm y)) := by
      apply ψ.injective
      rw [LinearEquiv.apply_symm_apply, hψ h]
    have e3 := hψ ⟨_, hh'⟩ (ψ.symm y)
    rw [LinearEquiv.apply_symm_apply] at e3
    rw [hxv, hxv, e2, ← e3]
    congr 1
    simp [hinv]
  exact no_semilinear_involution hK b c hbc _
    (fun g hg v => isometry_of_mem_omega _ hg v) hSchur x hx hxx hnorm

end SzG11S

end G11

end CFSG.Quasithin

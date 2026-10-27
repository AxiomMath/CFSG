module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Comm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem eq_of_smul_eq_smul {a b : S.K} (h : ∀ w : W, S.smul a w = S.smul b w) :
    a = b := by
  have h1 := congrFun (congrArg S.vec (h (S.ofVec (Pi.single (Sum.inl 0) 1)))) (Sum.inl 0)
  simpa [S.vec_smul, S.vec_ofVec] using h1

theorem exists_ringEquiv_of_mem_normalizer {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (S.omega : Set (MulAut W))) :
    ∃ σ : S.K ≃+* S.K, ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul (σ c) (g w) := by
  classical
  let f : S.K → W →* W := fun c =>
    { toFun := fun w => g (S.smul c (g⁻¹ w))
      map_one' := by simp [S.smul_one_elem]
      map_mul' := by intro a b; simp [S.smul_mul_eq, map_mul] }
  have hfdef : ∀ (c : S.K) (w : W), f c w = g (S.smul c (g⁻¹ w)) := fun c w => rfl
  have hf : ∀ c : S.K, ∀ h ∈ S.omega0, ∀ w : W, f c (h w) = h (f c w) := by
    intro c h hh w
    have hmem : h ∈ S.omega := S.omega0_le_omega hh
    have h1mem : g⁻¹ * h * g ∈ S.omega :=
      (Subgroup.mem_set_normalizer_iff''.mp hg h).mp hmem
    have hgw : (g⁻¹ * h * g) (g⁻¹ w) = g⁻¹ (h w) := by
      simp [MulAut.mul_apply]
    rw [hfdef c (h w), hfdef c w]
    rw [← hgw, ← S.omega_smul h1mem c (g⁻¹ w)]
    rw [← MulAut.mul_apply, show g * (g⁻¹ * h * g) = h * g by group, MulAut.mul_apply]
  have hchoose : ∀ c : S.K, ∃ a : S.K, ∀ w : W, f c w = S.smul a w :=
    fun c => S.exists_smul_of_commute_omega0 (f c) (hf c)
  choose σ₀ hσ₀ using hchoose
  have hg_push : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul (σ₀ c) (g w) := by
    intro c w
    have h := hσ₀ c (g w)
    rw [hfdef c (g w)] at h
    simpa using h
  have h1 : σ₀ 1 = 1 := by
    apply eq_of_smul_eq_smul S
    intro w
    have h := hσ₀ 1 w
    rw [hfdef 1 w, S.smul_one_eq] at h
    simpa [S.smul_one_eq] using h.symm
  have hmul : ∀ c c' : S.K, σ₀ (c * c') = σ₀ c * σ₀ c' := by
    intro c c'
    apply eq_of_smul_eq_smul S
    intro w
    have h := hσ₀ (c * c') w
    rw [hfdef (c * c') w, ← S.smul_smul_eq] at h
    rw [hg_push c (S.smul c' (g⁻¹ w)), hg_push c' (g⁻¹ w)] at h
    simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply] at h
    rw [S.smul_smul_eq] at h
    exact h.symm
  have hadd : ∀ c c' : S.K, σ₀ (c + c') = σ₀ c + σ₀ c' := by
    intro c c'
    apply eq_of_smul_eq_smul S
    intro w
    have h := hσ₀ (c + c') w
    rw [hfdef (c + c') w, S.smul_add_eq, map_mul, hg_push c (g⁻¹ w),
      hg_push c' (g⁻¹ w)] at h
    simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply] at h
    rw [← S.smul_add_eq] at h
    exact h.symm
  have h0 : σ₀ 0 = 0 := by
    apply eq_of_smul_eq_smul S
    intro w
    have h := hσ₀ 0 w
    rw [hfdef 0 w, S.smul_zero_eq, map_one] at h
    simpa [S.smul_zero_eq] using h.symm
  let σ₀hom : S.K →+* S.K :=
    { toFun := σ₀
      map_one' := h1
      map_mul' := hmul
      map_zero' := h0
      map_add' := hadd }
  have hinj : Function.Injective σ₀hom := by
    intro a b hab
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hzero : σ₀hom (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hone : (1 : S.K) = 0 := by
      calc (1 : S.K) = σ₀hom 1 := (map_one σ₀hom).symm
        _ = σ₀hom ((a - b) * (a - b)⁻¹) := by rw [mul_inv_cancel₀ hne']
        _ = σ₀hom (a - b) * σ₀hom ((a - b)⁻¹) := by rw [map_mul]
        _ = 0 := by rw [hzero, zero_mul]
    exact one_ne_zero hone
  have hsurj : Function.Surjective σ₀hom := Finite.injective_iff_surjective.mp hinj
  refine ⟨RingEquiv.ofBijective σ₀hom ⟨hinj, hsurj⟩, ?_⟩
  intro c w
  show g (S.smul c w) = S.smul (σ₀ c) (g w)
  exact hg_push c w

private theorem smul_inv (c : S.K) (w : W) : S.smul c w⁻¹ = (S.smul c w)⁻¹ := by
  apply S.vec_injective
  simp [S.vec_smul, S.vec_inv]

private theorem eq_one_of_fixed_of_smul_fixed {σ : S.K ≃+* S.K} {g : MulAut W}
    (hg : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul (σ c) (g w)) {c : S.K}
    (hc : σ c ≠ c) {f : W} (hf : g f = f) (hf' : g (S.smul c f) = S.smul c f) :
    f = 1 := by
  have h1 : S.smul (σ c) f = S.smul c f := by
    calc S.smul (σ c) f = S.smul (σ c) (g f) := by rw [hf]
      _ = g (S.smul c f) := (hg c f).symm
      _ = S.smul c f := hf'
  have h2 : S.vec f = 0 := by
    have h := congrArg S.vec h1
    simp only [S.vec_smul] at h
    have h3 : (σ c - c) • S.vec f = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) hc
    · exact h4
  exact S.vec_injective (by rw [h2, S.vec_one])

theorem card_fixed_le_of_semilinear {σ : S.K ≃+* S.K} (hσ : σ ≠ RingEquiv.refl S.K)
    {g : MulAut W} (hg : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul (σ c) (g w)) :
    Nat.card {w : W // g w = w} ≤ Nat.card S.K ^ 2 := by
  classical
  have hc₀ex : ∃ c : S.K, σ c ≠ c := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext fun c => by simpa using h c)
  obtain ⟨c₀, hc₀⟩ := hc₀ex
  let Φ : {w : W // g w = w} × {w : W // g w = w} → W :=
    fun p => p.1.1 * S.smul c₀ p.2.1
  have hΦinj : Function.Injective Φ := by
    rintro ⟨⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ ⟨⟨f₁', hf₁'⟩, ⟨f₂', hf₂'⟩⟩ heq
    change f₁ * S.smul c₀ f₂ = f₁' * S.smul c₀ f₂' at heq
    have hA : f₁ * f₁'⁻¹ = S.smul c₀ f₂' * (S.smul c₀ f₂)⁻¹ := by
      rw [mul_inv_eq_mul_inv_iff_mul_eq_mul]
      rw [heq, mul_comm]
    have haF : g (f₁ * f₁'⁻¹) = f₁ * f₁'⁻¹ := by
      simp [hf₁, hf₁']
    have hbF : g (f₂' * f₂⁻¹) = f₂' * f₂⁻¹ := by
      simp [hf₂', hf₂]
    have hsa : S.smul c₀ (f₂' * f₂⁻¹) = f₁ * f₁'⁻¹ := by
      rw [S.smul_mul_eq, S.smul_inv, hA]
    have hb1 : f₂' * f₂⁻¹ = 1 :=
      eq_one_of_fixed_of_smul_fixed S hg hc₀ hbF (by rw [hsa]; exact haF)
    have ha1 : f₁ * f₁'⁻¹ = 1 := by rw [← hsa, hb1, S.smul_one_elem]
    have hf1eq : f₁ = f₁' := mul_inv_eq_one.mp ha1
    have hf2eq : f₂ = f₂' := (mul_inv_eq_one.mp hb1).symm
    exact Prod.ext (Subtype.ext hf1eq) (Subtype.ext hf2eq)
  haveI : Fintype S.K := Fintype.ofFinite S.K
  haveI : Finite W := Finite.of_injective S.vec S.vec_injective
  have hle : Nat.card {w : W // g w = w} * Nat.card {w : W // g w = w} ≤
      Nat.card S.K ^ 2 * Nat.card S.K ^ 2 := by
    calc Nat.card {w : W // g w = w} * Nat.card {w : W // g w = w}
        = Nat.card ({w : W // g w = w} × {w : W // g w = w}) := (Nat.card_prod _ _).symm
      _ ≤ Nat.card W := Nat.card_le_card_of_injective Φ hΦinj
      _ = Nat.card S.K ^ 4 := S.card_eq
      _ = Nat.card S.K ^ 2 * Nat.card S.K ^ 2 := by ring
  exact Nat.mul_self_le_mul_self_iff.mp hle

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
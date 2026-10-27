module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08x2b_neg_mem_ggHL {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] {Λ : Type*} (ι : Additive E ≃+ V)
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) :
    LinearEquiv.neg (ZMod p) ∈ ggHL ι φ h α :=
  Subgroup.subset_closure (Or.inl (Or.inr (by simp)))

private lemma ggQ2s08x2b_zmod3_units (c : (ZMod 3)ˣ) :
    (c : ZMod 3) = 1 ∨ (c : ZMod 3) = -1 := by
  fin_cases c <;> decide

theorem ggQ2s08x2_action_mem_ggHL
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (M : GGQ2LDatum 3 Bs L x)
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (ι : Additive ↥(ggGamma L hBsN).range ≃+ (M.V ⧸ Submodule.span (ZMod 3) {M.xV}))
    (φ : M.Λ → MulAut ↥(ggGamma L hBsN).range)
    (h : M.Λ → M.V ⧸ Submodule.span (ZMod 3) {M.xV})
    (α : M.Λ → Module.Dual (ZMod 3) (M.V ⧸ Submodule.span (ZMod 3) {M.xV}))
    (hcompat : ∀ b : ↥Bs, ι (Additive.ofMul (⟨ggGamma L hBsN b, b, rfl⟩ : ↥(ggGamma L hBsN).range)) =
      Submodule.Quotient.mk (M.model (Additive.ofMul b)))
    (hpair : ∀ i j, α i (h j) = ((M.cartan i j : ℤ) : ZMod 3))
    (hsimple : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hAut : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range φ))
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (ψ : MulAut ↥Bs) (hψ : ∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = g * b * g⁻¹) :
    ∃ T ∈ ggHL ι φ h α, ∀ v : M.V,
      T (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ggLin (p := 3) M.model ψ v) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ' : MulAut ↥(ggGamma L hBsN).range :=
    (ggGamma L hBsN).range.normalizerMonoidHom
      ⟨L.normalizerMonoidHom ⟨g, hgL⟩,
        normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hg hgL⟩
  have hφ' : ∀ a : ↥(ggGamma L hBsN).range,
      ((φ' a : ↥(ggGamma L hBsN).range) : MulAut L) =
        L.normalizerMonoidHom ⟨g, hgL⟩ * a * (L.normalizerMonoidHom ⟨g, hgL⟩)⁻¹ :=
    fun a => Subgroup.normalizerMonoidHom_apply_apply_coe (ggGamma L hBsN).range
      ⟨L.normalizerMonoidHom ⟨g, hgL⟩,
        normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hg hgL⟩ a
  have hφ'b : ∀ b : ↥Bs,
      φ' (⟨ggGamma L hBsN b, b, rfl⟩ : ↥(ggGamma L hBsN).range) =
        (⟨ggGamma L hBsN (ψ b), ψ b, rfl⟩ : ↥(ggGamma L hBsN).range) := by
    intro b
    apply Subtype.ext
    have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hg b).mp b.2
    have hψb : (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) = ψ b := Subtype.ext (hψ b).symm
    show L.normalizerMonoidHom ⟨g, hgL⟩ * ggGamma L hBsN b *
        (L.normalizerMonoidHom ⟨g, hgL⟩)⁻¹ = ggGamma L hBsN (ψ b)
    rw [ggGamma_conj_normalizer L hBsN ⟨g, hgL⟩ b hgb, hψb]
  obtain ⟨⟨c, w, hw, hcw⟩, -⟩ :=
    hTBW G 3 B Bs x L D J hS.1.1 hInn hBsN
      M.Λ M.coxeter M.cartan (M.V ⧸ Submodule.span (ZMod 3) {M.xV})
      ι φ h α M.isWeyl M.isCartan hpair hsimple hAut g hg hgL φ' hφ'
  have hc : (c : ZMod 3) = 1 ∨ (c : ZMod 3) = -1 := ggQ2s08x2b_zmod3_units c
  have hT : ggLin (p := 3) ι φ' ∈ ggHL ι φ h α := by
    rcases hc with hc | hc
    · have heq : ggLin (p := 3) ι φ' = w := LinearEquiv.ext fun v => by
        rw [hcw v, hc, one_smul]
      rw [heq]; exact hw
    · have heq : ggLin (p := 3) ι φ' = LinearEquiv.neg (ZMod 3) * w :=
        LinearEquiv.ext fun v => by
          rw [hcw v, hc, LinearEquiv.mul_apply, LinearEquiv.neg_apply]
          exact neg_one_smul (ZMod 3) (w v)
      rw [heq]
      exact Subgroup.mul_mem _ (ggQ2s08x2b_neg_mem_ggHL ι φ h α) hw
  refine ⟨ggLin (p := 3) ι φ', hT, fun v => ?_⟩
  have hkey : ∀ b : ↥Bs, ggLin (p := 3) ι φ'
        (Submodule.Quotient.mk (M.model (Additive.ofMul b))) =
      Submodule.Quotient.mk (ggLin (p := 3) M.model ψ (M.model (Additive.ofMul b))) := by
    intro b
    calc ggLin (p := 3) ι φ' (Submodule.Quotient.mk (M.model (Additive.ofMul b)))
        = ggLin (p := 3) ι φ'
            (ι (Additive.ofMul (⟨ggGamma L hBsN b, b, rfl⟩ :
              ↥(ggGamma L hBsN).range))) := by rw [← hcompat b]
      _ = ι (Additive.ofMul (φ' ⟨ggGamma L hBsN b, b, rfl⟩)) := by rw [ggLin_apply_ofMul]
      _ = ι (Additive.ofMul (⟨ggGamma L hBsN (ψ b), ψ b, rfl⟩ :
              ↥(ggGamma L hBsN).range)) := by rw [hφ'b b]
      _ = Submodule.Quotient.mk (M.model (Additive.ofMul (ψ b))) := by rw [hcompat (ψ b)]
      _ = Submodule.Quotient.mk (ggLin (p := 3) M.model ψ (M.model (Additive.ofMul b))) := by
            rw [ggLin_apply_ofMul]
  obtain ⟨a, rfl⟩ := M.model.surjective v
  rw [← ofMul_toMul a]
  exact hkey (Additive.toMul a)

end CFSG.StandardType

end

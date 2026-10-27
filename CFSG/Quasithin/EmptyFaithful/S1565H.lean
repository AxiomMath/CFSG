module

public import CFSG.Quasithin.EmptyFaithful.S1565A

public section

namespace CFSG.Quasithin.S1565

variable {X : Type} [Group X] {W : Type} [CommGroup W]

@[expose] def fixModSub (φ : X →* MulAut W) (S : Subgroup X) (J : Subgroup W) : Subgroup W where
  carrier := {w | FixMod φ S J w}
  one_mem' := fun s _ => by simp
  mul_mem' := by
    intro a b ha hb s hs
    have e : φ s (a * b) * (a * b)⁻¹ = (φ s a * a⁻¹) * (φ s b * b⁻¹) := by
      simp only [map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact J.mul_mem (ha s hs) (hb s hs)
  inv_mem' := by
    intro a ha s hs
    have e : φ s a⁻¹ * (a⁻¹)⁻¹ = (φ s a * a⁻¹)⁻¹ := by
      simp only [map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact J.inv_mem (ha s hs)

theorem invSub_fixModSub (φ : X →* MulAut W) {S : Subgroup X} (hS : S.Normal) {J : Subgroup W}
    (hJ : InvSub φ J) : InvSub φ (fixModSub φ S J) := by
  intro x w hw s hs
  have hs' : x⁻¹ * s * x ∈ S := hS.conj_mem' s hs x
  have h1 := hw (x⁻¹ * s * x) hs'
  have e1 : φ x (φ (x⁻¹ * s * x) w) = φ s (φ x w) := by
    rw [map_mul, map_mul, map_inv]
    simp only [MulAut.mul_apply]
    rw [MulAut.apply_inv_self]
  have e : φ s (φ x w) * (φ x w)⁻¹ = φ x (φ (x⁻¹ * s * x) w * w⁻¹) := by
    rw [map_mul, map_inv, e1]
  rw [e]
  exact hJ x _ h1

theorem le_fixModSub (φ : X →* MulAut W) (S : Subgroup X) {J : Subgroup W} (hJ : InvSub φ J) :
    J ≤ fixModSub φ S J := fun j hj s _ =>
  J.mul_mem (hJ s j hj) (J.inv_mem hj)

theorem fixProp_of_trivK (φ : X →* MulAut W) (B K₀ T' : Subgroup X) (hTB : T' ≤ B)
    (hdec : ∀ x : X, ∃ t ∈ T', ∃ k ∈ K₀, x = t * k) {A A' : Subgroup W} (hA : InvSub φ A)
    (hK : ∀ k ∈ K₀, ∀ a ∈ A', φ k a * a⁻¹ ∈ A) : FixProp φ B A A' := by
  intro w hw hwB x _
  obtain ⟨t, ht, k, hk, rfl⟩ := hdec x
  have h1 : φ k w * w⁻¹ ∈ A := hK k hk w hw
  have h2 : φ t w * w⁻¹ ∈ A := hwB t (hTB ht)
  have e : φ (t * k) w * w⁻¹ = φ t (φ k w * w⁻¹) * (φ t w * w⁻¹) := by
    simp only [map_mul, map_inv, MulAut.mul_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e]
  exact A.mul_mem (hA t _ h1) h2

theorem fixProp_of_noFixed_layer [Finite X] (φ : X →* MulAut W) (hW2 : ∀ w : W, w ^ 2 = 1)
    (B K₀ T' : Subgroup X) (hK₀ : K₀.Normal) (hodd : Odd B.index) (hTB : T' ≤ B)
    (hdec : ∀ x : X, ∃ t ∈ T', ∃ k ∈ K₀, x = t * k) {J Uk : Subgroup W} (hJ : InvSub φ J)
    (hUk : InvSub φ Uk) (hJU : J ≤ Uk) (hUkK : ∀ k ∈ K₀, ∀ w : W, φ k w * w⁻¹ ∈ Uk)
    (hnf : NoFixedOn φ B (Uk ⊓ fixModSub φ K₀ J) Uk) : FixProp φ B J ⊤ := by
  set Ck := fixModSub φ K₀ J with hCk
  have hCkinv : InvSub φ Ck := invSub_fixModSub φ hK₀ hJ
  have hUC : InvSub φ (Uk ⊓ Ck) := fun x a ha => ⟨hUk x a ha.1, hCkinv x a ha.2⟩
  have hJUC : J ≤ Uk ⊓ Ck := le_inf hJU (le_fixModSub φ K₀ hJ)
  have h1 : FixProp φ B J (Uk ⊓ Ck) :=
    fixProp_of_trivK φ B K₀ T' hTB hdec hJ fun k hk a ha => ha.2 k hk
  have h2 : FixProp φ B (Uk ⊓ Ck) Uk := fixProp_of_chiefFactor hUC (Or.inr hnf)
  have h3 : FixProp φ B Uk ⊤ :=
    fixProp_of_trivK φ B K₀ T' hTB hdec hUk fun k hk a _ => hUkK k hk a
  have h12 : FixProp φ B J Uk := fixProp_compose φ hW2 B hodd hJ hJUC h1 h2
  exact fixProp_compose φ hW2 B hodd hJ hJU h12 h3

end CFSG.Quasithin.S1565

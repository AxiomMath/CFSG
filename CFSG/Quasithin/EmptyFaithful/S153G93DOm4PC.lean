module

public import CFSG.Quasithin.EmptyFaithful.S1565L16
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.HOm4Norm

public section

namespace CFSG.Quasithin.S153G93D.Om4P

open CFSG.Quasithin.H.Om4 CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {W : Type} [CommGroup W] {F : Type} [Field F]

theorem exists_tensorData {K : Subgroup (MulAut W)} {π : TensorG2 F →* ↥K}
    (h : (FFModel.tensorNat 2 F).RealizesVia K ⊤ ⊥ π) :
    ∃ β : W ≃* TensorE2 F, IsTensorData2 K π β := by
  obtain ⟨E, hE⟩ := CFSG.Quasithin.G64.RealizesVia.exists_secEquiv
    (D := FFModel.tensorNat 2 F) rfl h
  exact ⟨E.trans Subgroup.topEquiv, fun γ w => hE γ w⟩

theorem congrHom_tensor {K : Subgroup (MulAut W)} {π : TensorG2 F →* ↥K} {β : W ≃* TensorE2 F}
    (hd : IsTensorData2 K π β) (γ : TensorG2 F) :
    congrHom β ((π γ : ↥K) : MulAut W) = lr (γ.1 : GL (Fin 2) F) (γ.2 : GL (Fin 2) F) := by
  refine MulEquiv.ext fun X => ?_
  rw [congrHom_apply, hd γ (β.symm X), MulEquiv.apply_symm_apply]
  rfl

theorem toGL_equiv_symm (g : ↥(StatedSL 2 F)) :
    Matrix.SpecialLinearGroup.toGL ((specialLinearGroupEquivStatedSL 2 F).symm g) =
      (g : GL (Fin 2) F) :=
  congrArg Subtype.val ((specialLinearGroupEquivStatedSL 2 F).apply_symm_apply g)

theorem map_eq_range {K : Subgroup (MulAut W)} {π : TensorG2 F →* ↥K}
    (hπs : Function.Surjective π) {β : W ≃* TensorE2 F} (hd : IsTensorData2 K π β) :
    K.map (congrHom β) = (rho (K := F)).range := by
  ext φ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨ψ, hψ⟩
    refine ⟨((specialLinearGroupEquivStatedSL 2 F).symm γ.1,
      (specialLinearGroupEquivStatedSL 2 F).symm γ.2), ?_⟩
    rw [rho_apply, toGL_equiv_symm, toGL_equiv_symm, ← congrHom_tensor hd γ, hγ]
  · rintro ⟨⟨g, h⟩, rfl⟩
    let γ₀ : TensorG2 F := (specialLinearGroupEquivStatedSL 2 F g,
      specialLinearGroupEquivStatedSL 2 F h)
    refine ⟨((π γ₀ : ↥K) : MulAut W), (π γ₀).2, ?_⟩
    rw [congrHom_tensor hd γ₀, rho_apply]
    rfl

theorem isQuasisimple_of_simple_nonabelian {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.IsQuasisimple X := by
  refine isQuasisimple_of_perfect_of_isSimpleGroup ?_ hs
  have hc : (commutator X).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h0 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : ⁅a, b⁆ ∈ commutator X :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
    exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp this))
  · exact ⟨h1⟩

theorem ne_bot_of_nonabelian {L : Subgroup (MulAut W)} (hnc : ∃ x y : ↥L, x * y ≠ y * x) :
    L ≠ ⊥ := by
  rintro rfl
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  have hx : x = 1 := Subsingleton.elim _ _
  rw [hx, one_mul, mul_one]

theorem normalizes_factorL2 [Finite F] [CharP F 2] (hK4 : 4 ≤ Nat.card F)
    {K L₁ L₂ : Subgroup (MulAut W)} {π : TensorG2 F →* ↥K} {β : W ≃* TensorE2 F}
    (hd : IsTensorData2 K π β) (hπs : Function.Surjective π) (hsup : K = L₁ ⊔ L₂)
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hinf : L₁ ⊓ L₂ = ⊥)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂) (h₁ : L₁ ≠ ⊥) (h₂ : L₂ ≠ ⊥)
    {a : MulAut W} (haL₁ : ∀ x ∈ L₁, a * x * a⁻¹ ∈ L₁) (haL₂ : ∀ x ∈ L₂, a * x * a⁻¹ ∈ L₂) :
    ∀ x ∈ factorL2 K π, a * x * a⁻¹ ∈ factorL2 K π := by
  have f1 := eq_factor_or2 hK4 hd hπs hsup hcomm hq₁ h₁
  have f2 := eq_factor_or2 hK4 hd hπs (hsup.trans (sup_comm _ _))
    (fun x hx y hy => (hcomm y hy x hx).symm) hq₂ h₂
  rcases f1 with h1 | h1
  · rw [← h1]
    exact haL₁
  · rcases f2 with h2 | h2
    · rw [← h2]
      exact haL₂
    · exfalso
      apply h₁
      have : L₁ = L₂ := h1.trans h2.symm
      rw [← hinf, ← this, inf_idem]

theorem hL_of_normalizes_factor {K : Subgroup (MulAut W)} {π : TensorG2 F →* ↥K}
    {β : W ≃* TensorE2 F} (hd : IsTensorData2 K π β) {a : MulAut W}
    (ha : ∀ x ∈ factorL2 K π, a * x * a⁻¹ ∈ factorL2 K π) :
    ∀ g : SpecialLinearGroup (Fin 2) F, ∃ g' : SpecialLinearGroup (Fin 2) F,
      congrHom β a * lg g * (congrHom β a)⁻¹ = lg g' := by
  intro g
  have hlg : ∀ g₀ : ↥(StatedSL 2 F),
      lg ((specialLinearGroupEquivStatedSL 2 F).symm g₀) = lr (g₀ : GL (Fin 2) F) 1 := by
    intro g₀
    rw [lg, toGL_equiv_symm]
  have hmem : ((π (specialLinearGroupEquivStatedSL 2 F g, 1) : ↥K) : MulAut W) ∈
      factorL2 K π := mem_factorL2.mpr ⟨specialLinearGroupEquivStatedSL 2 F g, rfl⟩
  obtain ⟨g₂, hg₂⟩ := mem_factorL2.mp (ha _ hmem)
  refine ⟨(specialLinearGroupEquivStatedSL 2 F).symm g₂, ?_⟩
  have h1 := congrArg (congrHom β) hg₂
  rw [map_mul, map_mul, map_inv, congrHom_tensor hd, congrHom_tensor hd] at h1
  rw [hlg g₂]
  have hg : lg g = lr ((specialLinearGroupEquivStatedSL 2 F g : ↥(StatedSL 2 F)) :
      GL (Fin 2) F) 1 := by
    rw [← hlg, MulEquiv.symm_apply_apply]
  rw [hg]
  exact h1.symm

end CFSG.Quasithin.S153G93D.Om4P

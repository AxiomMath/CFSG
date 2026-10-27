module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {U : Type*} [CommGroup U]

theorem realizes_of_mulEquiv (D : FFModel) (hsec : D.sec = ⊤) (hker : D.ker = ⊥)
    (hact1 : ∀ γ, D.act γ 1 = 1) (H : Subgroup (MulAut U)) (β : U ≃* D.Amb)
    (π : D.Gam →* ↥H) (hπ : Function.Surjective π)
    (hact : ∀ γ u, β (((π γ : ↥H) : MulAut U) u) = D.act γ (β u)) :
    D.Realizes H ⊤ ⊥ := by
  have hmem : ∀ a : D.Amb, a ∈ D.sec := fun a => hsec ▸ Subgroup.mem_top a
  let β' : ↥(⊤ : Subgroup U) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
      { toFun := fun u => ⟨β (u : U), hmem _⟩
        map_one' := Subtype.ext (map_one β)
        map_mul' := fun a b => Subtype.ext (map_mul β _ _) }
  have hβ' : ∀ u : ↥(⊤ : Subgroup U),
      β' u = QuotientGroup.mk (⟨β (u : U), hmem _⟩ : ↥D.sec) := fun _ => rfl
  have hmk : ∀ m m' : ↥D.sec, (QuotientGroup.mk m : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
      QuotientGroup.mk m' → m = m' := by
    intro m m' h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot] at h
    exact inv_mul_eq_one.mp (Subtype.ext h)
  refine ⟨π, hπ, bot_le, hker ▸ bot_le, fun _ _ _ => Subgroup.mem_top _, ?_,
    fun _ _ _ => hmem _, ?_, β', ?_, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    rw [hker, Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨β.symm (m : D.Amb), Subgroup.mem_top _⟩, ?_⟩
    rw [hβ']
    congr 1
    ext
    exact β.apply_symm_apply _
  · intro u
    rw [hβ']
    constructor
    · intro h
      have h1 := hmk _ 1 (h.trans (QuotientGroup.mk_one _).symm)
      have h2 : β (u : U) = 1 := congrArg Subtype.val h1
      rw [Subgroup.mem_bot]
      exact (map_eq_one_iff β β.injective).mp h2
    · intro h
      rw [Subgroup.mem_bot] at h
      have h2 : (⟨β (u : U), hmem _⟩ : ↥D.sec) = 1 := Subtype.ext (by rw [h, map_one]; rfl)
      rw [h2, QuotientGroup.mk_one]
  · intro γ u m hu hm h
    rw [hβ'] at h ⊢
    have h2 : β (u : U) = (m : D.Amb) := congrArg Subtype.val (hmk _ _ h)
    congr 1
    ext
    show β (((π γ : ↥H) : MulAut U) (u : U)) = D.act γ (m : D.Amb)
    rw [hact γ (u : U), h2]

theorem tensorNat_realizes {d : ℕ} {K : Type} [Field K] (H : Subgroup (MulAut U))
    (β : U ≃* Multiplicative (Matrix (Fin d) (Fin d) K))
    (π : ↥(StatedSL d K) × ↥(StatedSL d K) →* ↥H) (hπ : Function.Surjective π)
    (hact : ∀ γ u, β (((π γ : ↥H) : MulAut U) u) = tensorAct d K γ (β u)) :
    (FFModel.tensorNat d K).Realizes H ⊤ ⊥ :=
  realizes_of_mulEquiv (FFModel.tensorNat d K) rfl rfl
    (fun γ => by
      show Multiplicative.ofAdd (_ * (0 : Matrix (Fin d) (Fin d) K) * _) = 1
      rw [mul_zero, zero_mul]
      rfl) H β π hπ hact

theorem tensorNat_realizes_of_pair {d : ℕ} {K : Type} [Field K] (L₁ L₂ : Subgroup (MulAut U))
    (β : U ≃* Multiplicative (Matrix (Fin d) (Fin d) K))
    (φ₁ φ₂ : ↥(StatedSL d K) →* MulAut U) (h₁ : φ₁.range = L₁) (h₂ : φ₂.range = L₂)
    (hφ₁ : ∀ g u, β (φ₁ g u) = Multiplicative.ofAdd
      (((g : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        Multiplicative.toAdd (β u)))
    (hφ₂ : ∀ h u, β (φ₂ h u) = Multiplicative.ofAdd (Multiplicative.toAdd (β u) *
        ((h : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ)) :
    (FFModel.tensorNat d K).Realizes (L₁ ⊔ L₂) ⊤ ⊥ := by
  have hcomm : ∀ g h, Commute (φ₁ g) (φ₂ h) := by
    intro g h
    apply MulEquiv.ext
    intro u
    apply β.injective
    simp only [MulAut.mul_apply]
    rw [hφ₁, hφ₂, hφ₂, hφ₁]
    simp [Matrix.mul_assoc]
  set ψ := φ₁.noncommCoprod φ₂ hcomm with hψ
  have hrange : ψ.range = L₁ ⊔ L₂ := by
    rw [hψ, MonoidHom.noncommCoprod_range, h₁, h₂]
  let π : ↥(StatedSL d K) × ↥(StatedSL d K) →* ↥(L₁ ⊔ L₂) :=
    ψ.codRestrict (L₁ ⊔ L₂) (fun x => hrange ▸ ⟨x, rfl⟩)
  refine tensorNat_realizes (L₁ ⊔ L₂) β π ?_ ?_
  · rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · intro γ u
    show β ((φ₁ γ.1 * φ₂ γ.2) u) = _
    rw [MulAut.mul_apply, hφ₁, hφ₂, tensorAct, toAdd_ofAdd, Matrix.mul_assoc]

end CFSG.Quasithin.SmithD37

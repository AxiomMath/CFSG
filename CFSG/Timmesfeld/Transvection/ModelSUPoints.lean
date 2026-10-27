module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.Timmesfeld.Transvection.ModelSUNormal
public import CFSG.Timmesfeld.ARS.CaseMSp

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem suPts_commuting_conjSub_iff {K : Type} [Group K] {Φ : SU σ m →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ m)) (hComm : SUCommStmt σ m) {d : Fin m → F}
    {Td : Subgroup (SU σ m)} (hTd : IsUTransGroup σ d Td) (hd : d ≠ 0)
    (hdd : uForm σ d d = 0) (z : SU σ m) :
    Commuting (Td.map Φ) (conjSub (Td.map Φ) (Φ z)) ↔ uForm σ d (suMat σ m z *ᵥ d) = 0 := by
  have hr : suMat σ m z *ᵥ d ≠ 0 := suMat_mulVec_ne_zero σ z hd
  have hrr : uForm σ (suMat σ m z *ᵥ d) (suMat σ m z *ᵥ d) = 0 := by
    rw [uForm_mulVec]
    exact hdd
  rw [ModelRank.conjSub_map, hComm hker hTd (hTd.conjSub z) hd hr hdd hrr]
  constructor
  · rintro (h | ⟨l, hl⟩)
    · exact h
    · rw [hl, uForm_smul_right, hdd, mul_zero]
  · exact Or.inl

theorem suPts_commuting_conjSub_mulAut_iff {K : Type} [Group K] (β : MulAut K)
    {X : Subgroup K} (hX : X.map β.toMonoidHom = X) (g : K) :
    Commuting X (conjSub X g) ↔ Commuting X (conjSub X (β g)) := by
  have key : Commuting (X.map β.toMonoidHom) ((conjSub X g).map β.toMonoidHom) ↔
      Commuting X (conjSub X g) := CaseM.commuting_map_iff β.injective
  rw [← key, ← ModelRank.conjSub_map, hX]
  rfl

theorem suPts_fixed_of_uForm_eq_zero (hσ : ∀ c, σ (σ c) = c) {K : Type} [Group K]
    {Φ : SU σ m →* K} (hker : Φ.ker ≤ Subgroup.center (SU σ m)) (hComm : SUCommStmt σ m)
    {a d : Fin m → F} {T Td : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T)
    (hTd : IsUTransGroup σ d Td) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    (β : MulAut K) (hTdβ : (Td.map Φ).map β.toMonoidHom = Td.map Φ) {z : SU σ m}
    (hz : z ∈ uRad σ a) (hzT : (Φ z)⁻¹ * β (Φ z) ∈ T.map Φ)
    (h0 : uForm σ d (suMat σ m z *ᵥ d) = 0) : β (Φ z) = Φ z := by
  have hd : d ≠ 0 := by
    rintro rfl
    rw [uForm_zero_right] at had
    exact zero_ne_one had
  obtain ⟨t, ht, hΦt⟩ := hzT
  obtain ⟨e, -, hte⟩ := (hT.1 t).1 ht
  have hβ : β (Φ z) = Φ (z * t) := by rw [map_mul, hΦt, mul_inv_cancel_left]
  have h1 : uForm σ d (suMat σ m (z * t) *ᵥ d) = 0 := by
    rw [← suPts_commuting_conjSub_iff hker hComm hTd hd hdd, ← hβ,
      ← suPts_commuting_conjSub_mulAut_iff β hTdβ,
      suPts_commuting_conjSub_iff hker hComm hTd hd hdd]
    exact h0
  have h2 : suMat σ m (z * t) *ᵥ d = suMat σ m z *ᵥ d + e • a := by
    rw [map_mul, ← mulVec_mulVec, hte, uTrans_mulVec, had, mul_one, mulVec_add, mulVec_smul,
      hz.1]
  rw [h2, uForm_add_right, h0, zero_add, uForm_smul_right, uForm_swap_eq_one hσ had,
    mul_one] at h1
  have ht1 : t = 1 := suMat_injective σ (by rw [hte, h1, uTrans_zero, map_one])
  rw [hβ, ht1, mul_one]

theorem apply_map_uRad_eq_self (hσ : ∀ c, σ (σ c) = c) {K : Type} [Group K]
    {Φ : SU σ m →* K} (hker : Φ.ker ≤ Subgroup.center (SU σ m)) {a d : Fin m → F}
    {T Td : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) (hTd : IsUTransGroup σ d Td)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) (Θ : SUThetaFacts σ a d T)
    (hG : SUGeomFacts σ a d) (hComm : SUCommStmt σ m) (β : MulAut K)
    (hfixT : ∀ x ∈ T.map Φ, β x = x) (hTdβ : (Td.map Φ).map β.toMonoidHom = Td.map Φ)
    (hrad : ∀ z ∈ uRad σ a, (Φ z)⁻¹ * β (Φ z) ∈ T.map Φ) :
    ∀ z ∈ uRad σ a, β (Φ z) = Φ z := by
  intro x hx
  have fix_of : ∀ {e : Fin m → F} {y : SU σ m}, e ∈ perpPair σ a d → y ∈ uRad σ a →
      suMat σ m y *ᵥ d = d + e → β (Φ y) = Φ y := fun he hy hyd =>
    suPts_fixed_of_uForm_eq_zero hσ hker hComm hT hTd hdd had β hTdβ hy (hrad _ hy)
      (by rw [hyd, uForm_add_right, hdd, (mem_perpPair.1 he).2, add_zero])
  have rad_of : ∀ {e : Fin m → F} {y : SU σ m}, e ∈ perpPair σ a d →
      suMat σ m y *ᵥ d = d + e → radVec σ a d y = e := fun he hyd => by
    rw [radVec, hyd, projPair_add, projPair_d hdd had, projPair_of_mem he, zero_add]
  obtain ⟨e₁, he₁, e₂, he₂, he₁₁, he₂₂, hsum⟩ := hG.sum (Θ.mem_perp x)
  obtain ⟨y₁, hy₁, hy₁d⟩ := Θ.exists_eq_iso he₁ he₁₁
  obtain ⟨y₂, hy₂, hy₂d⟩ := Θ.exists_eq_iso he₂ he₂₂
  have hy : y₁ * y₂ ∈ uRad σ a := (uRad σ a).mul_mem hy₁ hy₂
  have hyinv : (y₁ * y₂)⁻¹ ∈ uRad σ a := (uRad σ a).inv_mem hy
  have ht : x * (y₁ * y₂)⁻¹ ∈ T := by
    refine (Θ.eq_zero_iff ((uRad σ a).mul_mem hx hyinv)).1 ?_
    rw [Θ.mul hx hyinv, Θ.inv hy, Θ.mul hy₁ hy₂, rad_of he₁ hy₁d, rad_of he₂ hy₂d, hsum,
      add_neg_cancel]
  have hfixt : β (Φ (x * (y₁ * y₂)⁻¹)) = Φ (x * (y₁ * y₂)⁻¹) := hfixT _ ⟨_, ht, rfl⟩
  have hfixy : β (Φ (y₁ * y₂)) = Φ (y₁ * y₂) := by
    rw [map_mul, map_mul, fix_of he₁ hy₁ hy₁d, fix_of he₂ hy₂ hy₂d]
  calc β (Φ x) = β (Φ (x * (y₁ * y₂)⁻¹) * Φ (y₁ * y₂)) := by
        rw [← map_mul, inv_mul_cancel_right]
    _ = Φ (x * (y₁ * y₂)⁻¹) * Φ (y₁ * y₂) := by rw [map_mul, hfixt, hfixy]
    _ = Φ x := by rw [← map_mul, inv_mul_cancel_right]

end ModelRank

end CFSG.Timmesfeld.Transvection

module

public import CFSG.Quasithin.Background.F918Z3Cg1Case1

public section

namespace CFSG.Quasithin

namespace Z3Cg1

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem case_two (hZ : Z37 D X G T' s) {a : ℕ} (ha : 1 ≤ a) (hDpsl : IsPSL 2 2 (2 * a) ↥D)
    (hXpsl : IsPSL 2 2 (2 * a) ↥X)
    (hH4a : ∀ b : MulAut V, b ≠ 1 → b * b = 1 → D.map (MulAut.conj b).toMonoidHom = D →
      X.map (MulAut.conj b).toMonoidHom = X → 3 ≤ rkIdx (fixV (Subgroup.zpowers b)))
    (hH4b : ∀ b : MulAut V, b * b = 1 → D.map (MulAut.conj b).toMonoidHom = D →
      X.map (MulAut.conj b).toMonoidHom = X →
      (¬ ∃ g ∈ D, ∀ y ∈ D, b * y * b⁻¹ = g * y * g⁻¹) →
      (¬ ∃ g ∈ X, ∀ x ∈ X, b * x * b⁻¹ = g * x * g⁻¹) →
      5 ≤ rkIdx (fixV (Subgroup.zpowers b)))
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G)
    (hAD : ∀ b ∈ A, D.map (MulAut.conj b).toMonoidHom = D)
    (hAX : ∀ b ∈ A, X.map (MulAut.conj b).toMonoidHom = X) (hY : A ⊓ (D ⊔ X) = ⊥) : False := by
  obtain ⟨hA2, hAle⟩ := rkIdx_fixV_le_of_mem_QhatStar (G := G) hA
  have hAe : IsElemAb2 A := hA2.isElemAbelian2
  have hApg : IsPGroup 2 ↥A := hAe.isPGroup
  have hn : 2 ≤ 2 * a := by omega
  have hND : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D := fun b hb => mem_of_map_conj_eq (hAD b hb)
  have hNX : ∀ b ∈ A, ∀ x ∈ X, b * x * b⁻¹ ∈ X := fun b hb => mem_of_map_conj_eq (hAX b hb)
  have hsq : ∀ j : MulAut V, j ∈ A → j * j = 1 := fun j hj => by
    have := hAe.2 j hj
    rwa [pow_two] at this
  have hle : ∀ j ∈ A, rkIdx (fixV (Subgroup.zpowers j)) ≤ rkIdx (fixV A) := fun j hj =>
    rkIdx_anti (fixV_le_fixV_of_le (Subgroup.zpowers_le.2 hj))
  let BD : Subgroup ↥A :=
    (MulAut.conj : ↥D →* MulAut ↥D).range.comap (conjRes D A hND)
  let BX : Subgroup ↥A :=
    (MulAut.conj : ↥X →* MulAut ↥X).range.comap (conjRes X A hNX)
  have hBDidx : rkIdx BD ≤ 1 :=
    rkIdx_comap_inner_le hn hDpsl _ (isElemAb2_range hAe _)
  have hBXidx : rkIdx BX ≤ 1 :=
    rkIdx_comap_inner_le hn hXpsl _ (isElemAb2_range hAe _)
  have hBinf : BD ⊓ BX = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hbD, hbX⟩
    obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 hbD)
    obtain ⟨ξ, hξ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 hbX)
    have hbeq := eq_mul_of_acts_as_inner hZ δ.2 ξ.2 (hsq b b.2)
      ((conjRes_eq_conj_iff b δ).1 hδ.symm) ((conjRes_eq_conj_iff b ξ).1 hξ.symm)
    have hmem : (b : MulAut V) ∈ A ⊓ (D ⊔ X) :=
      ⟨b.2, by rw [hbeq]; exact Subgroup.mul_mem_sup δ.2 ξ.2⟩
    rw [hY, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext hmem)
  have hr1 : rk BD + rkIdx BD = rk ↥A := rk_add_rkIdx BD
  have hr2 : rk BX + rkIdx BX = rk ↥A := rk_add_rkIdx BX
  have hr3 : rk BD + rk BX ≤ rk ↥A := rk_add_rk_le_of_inf_eq_bot hApg hBinf
  have hrkpos : 0 < rk ↥A := hA2.rk_pos
  obtain ⟨⟨b0, hb0A⟩, hb01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA2.ne_bot
  have hb01' : b0 ≠ 1 := fun h => hb01 (Subtype.ext h)
  have hcases : rk ↥A = 1 ∨ rk ↥A = 2 := by omega
  rcases hcases with h1 | h2
  ·
    have h3 := hH4a b0 hb01' (hsq b0 hb0A) (hAD b0 hb0A) (hAX b0 hb0A)
    have h4 := hle b0 hb0A
    omega
  ·
    obtain ⟨b, hbD, hbX⟩ := exists_not_mem_of_rk_lt (B₁ := BD) (B₂ := BX) (by omega) (by omega)
    have h3 := hH4b b (hsq b b.2) (hAD b b.2) (hAX b b.2)
      (fun ⟨g, hg, hgb⟩ => hbD (Subgroup.mem_comap.2 (MonoidHom.mem_range.2
        ⟨⟨g, hg⟩, ((conjRes_eq_conj_iff b ⟨g, hg⟩).2 hgb).symm⟩)))
      (fun ⟨g, hg, hgb⟩ => hbX (Subgroup.mem_comap.2 (MonoidHom.mem_range.2
        ⟨⟨g, hg⟩, ((conjRes_eq_conj_iff b ⟨g, hg⟩).2 hgb).symm⟩)))
    have h4 := hle b b.2
    omega

end Z3Cg1

theorem orth_exclusion_abstract {V : Type} [CommGroup V] [Finite V]
    {D X G T' : Subgroup (MulAut V)} {s : MulAut V} (hZ : Z37 D X G T' s) {a : ℕ} (ha : 1 ≤ a)
    (hDpsl : IsPSL 2 2 (2 * a) ↥D) (hXpsl : IsPSL 2 2 (2 * a) ↥X)
    (hV : Nat.card V = 2 ^ (16 * a))
    (hH2 : ∀ j ∈ D ⊔ X, j ≠ 1 → j * j = 1 →
      Nat.card ↥(fixV (Subgroup.zpowers j)) ^ 2 = Nat.card V)
    (hH3 : ∀ j₁ ∈ D, j₁ ≠ 1 → j₁ * j₁ = 1 → ∀ j₂ ∈ X, j₂ ≠ 1 → j₂ * j₂ = 1 →
      fixV (Subgroup.zpowers j₁) ≠ fixV (Subgroup.zpowers j₂))
    (hH4a : ∀ b : MulAut V, b ≠ 1 → b * b = 1 → D.map (MulAut.conj b).toMonoidHom = D →
      X.map (MulAut.conj b).toMonoidHom = X → 3 ≤ rkIdx (fixV (Subgroup.zpowers b)))
    (hH4b : ∀ b : MulAut V, b * b = 1 → D.map (MulAut.conj b).toMonoidHom = D →
      X.map (MulAut.conj b).toMonoidHom = X →
      (¬ ∃ g ∈ D, ∀ y ∈ D, b * y * b⁻¹ = g * y * g⁻¹) →
      (¬ ∃ g ∈ X, ∀ x ∈ X, b * x * b⁻¹ = g * x * g⁻¹) →
      5 ≤ rkIdx (fixV (Subgroup.zpowers b)))
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G)
    (hAD : ∀ b ∈ A, D.map (MulAut.conj b).toMonoidHom = D) : False := by
  obtain ⟨hA2, -⟩ := Z3Cg1.rkIdx_fixV_le_of_mem_QhatStar (G := G) hA
  have hND : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D := fun b hb =>
    Z3Cg1.mem_of_map_conj_eq (hAD b hb)
  have hND' : ∀ b ∈ A, ∀ y ∈ D, b⁻¹ * y * b ∈ D := fun b hb y hy => by
    simpa using hND b⁻¹ (A.inv_mem hb) y hy
  have hNX : ∀ b ∈ A, ∀ x ∈ X, b * x * b⁻¹ ∈ X := fun b hb x hx =>
    Z3Cg1.mem_X_of_normalizes hZ (hA2.le hb) (hND' b hb) hx
  have hNX' : ∀ b ∈ A, ∀ x ∈ X, b⁻¹ * x * b ∈ X := fun b hb x hx => by
    simpa using hNX b⁻¹ (A.inv_mem hb) x hx
  have hAX : ∀ b ∈ A, X.map (MulAut.conj b).toMonoidHom = X := fun b hb =>
    Z3Cg1.map_conj_eq_of_mem (hNX b hb) (hNX' b hb)
  by_cases hY : A ⊓ (D ⊔ X) = ⊥
  · exact Z3Cg1.case_two hZ ha hDpsl hXpsl hH4a hH4b hA hAD hAX hY
  · exact Z3Cg1.case_one hZ ha hDpsl hXpsl hV hH2 hH3 hA hND hNX hY

end CFSG.Quasithin

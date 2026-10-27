module

public import CFSG.Quasithin.Background.F918Z3Cg1Fact

public section

namespace CFSG.Quasithin

namespace Z3Cg1

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem case_one (hZ : Z37 D X G T' s) {a : ℕ} (ha : 1 ≤ a) (hDpsl : IsPSL 2 2 (2 * a) ↥D)
    (hXpsl : IsPSL 2 2 (2 * a) ↥X) (hV : Nat.card V = 2 ^ (16 * a))
    (hH2 : ∀ j ∈ D ⊔ X, j ≠ 1 → j * j = 1 →
      Nat.card ↥(fixV (Subgroup.zpowers j)) ^ 2 = Nat.card V)
    (hH3 : ∀ j₁ ∈ D, j₁ ≠ 1 → j₁ * j₁ = 1 → ∀ j₂ ∈ X, j₂ ≠ 1 → j₂ * j₂ = 1 →
      fixV (Subgroup.zpowers j₁) ≠ fixV (Subgroup.zpowers j₂))
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G) (hND : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D)
    (hNX : ∀ b ∈ A, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hY : A ⊓ (D ⊔ X) ≠ ⊥) : False := by
  obtain ⟨hA2, hAle⟩ := rkIdx_fixV_le_of_mem_QhatStar (G := G) hA
  have hAe : IsElemAb2 A := hA2.isElemAbelian2
  have hApg : IsPGroup 2 ↥A := hAe.isPGroup
  have hn : 2 ≤ 2 * a := by omega
  have hsq : ∀ j : MulAut V, j ∈ A → j * j = 1 := fun j hj => by
    have := hAe.2 j hj
    rwa [pow_two] at this
  have hinj : ∀ b : ↥A, conjRes D A hND b = 1 → conjRes X A hNX b = 1 → b = 1 :=
    fun b h1 h2 => eq_one_of_conjRes_eq_one hZ hAe hND hNX b h1 h2
  have hED : IsElemAb2 (conjRes D A hND).range := isElemAb2_range hAe _
  have hEX : IsElemAb2 (conjRes X A hNX).range := isElemAb2_range hAe _
  have hrkD : rk (conjRes D A hND).range ≤ 2 * a := autRankLe_psl2_two hn hDpsl _ hED
  have hrkX : rk (conjRes X A hNX).range ≤ 2 * a := autRankLe_psl2_two hn hXpsl _ hEX
  have hrkA : rk ↥A ≤ rk (conjRes D A hND).range + rk (conjRes X A hNX).range :=
    rk_le_add_of_pair_injective hApg _ _ hinj
  have h8 : ∀ j : MulAut V, j ∈ A → j ∈ D ⊔ X → j ≠ 1 →
      rkIdx (fixV (Subgroup.zpowers j)) = 8 * a := fun j hjA hjDX hj1 =>
    rkIdx_fixV_zpowers_eq hZ hV (hH2 j hjDX hj1 (hsq j hjA))
  have hle : ∀ j ∈ A, rkIdx (fixV (Subgroup.zpowers j)) ≤ rkIdx (fixV A) := fun j hj =>
    rkIdx_anti (fixV_le_fixV_of_le (Subgroup.zpowers_le.2 hj))
  obtain ⟨⟨j, hjA, hjDX⟩, hj1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hY
  have hj1' : j ≠ 1 := fun h => hj1 (Subtype.ext h)
  have h8j := h8 j hjA hjDX hj1'
  have hlej := hle j hjA
  have hidxA : rkIdx (fixV A) = 8 * a := by omega
  have hrkA4 : rk ↥A = 4 * a := by omega
  have hrkD2 : rk (conjRes D A hND).range = 2 * a := by omega
  have hrkX2 : rk (conjRes X A hNX).range = 2 * a := by omega
  have hsurj := exists_of_pair_rk_le hApg (conjRes D A hND) (conjRes X A hNX) hinj
    (by omega)
  have hsurjD : ∀ e ∈ (conjRes D A hND).range,
      ∃ b : ↥A, conjRes D A hND b = e ∧ conjRes X A hNX b = 1 := fun e he => by
    obtain ⟨b, hb1, hb2⟩ := hsurj ⟨e, he⟩ 1
    exact ⟨b, hb1, hb2⟩
  have hsurjX : ∀ e ∈ (conjRes X A hNX).range,
      ∃ b : ↥A, conjRes X A hNX b = e ∧ conjRes D A hND b = 1 := fun e he => by
    obtain ⟨b, hb1, hb2⟩ := hsurj 1 ⟨e, he⟩
    exact ⟨b, hb2, hb1⟩
  obtain ⟨g, hgA, hgD, hg1⟩ :=
    exists_mem_inf_of_surj hZ hn hDpsl hAe hND hNX (by omega) hsurjD
  obtain ⟨g', hg'A, hg'X, hg'1⟩ :=
    exists_mem_inf_of_surj hZ.symm hn hXpsl hAe hNX hND (by omega) hsurjX
  have hfix : ∀ j : MulAut V, j ∈ A → j ∈ D ⊔ X → j ≠ 1 →
      fixV A = fixV (Subgroup.zpowers j) := by
    intro j hjA hjDX hj1
    have h1 := rk_add_rkIdx (fixV A)
    have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers j))
    have h3 := h8 j hjA hjDX hj1
    exact eq_of_le_of_rk_le hZ.exp (fixV_le_fixV_of_le (Subgroup.zpowers_le.2 hjA)) (by omega)
  exact hH3 g hgD hg1 (hsq g hgA) g' hg'X hg'1 (hsq g' hg'A)
    ((hfix g hgA (Subgroup.mem_sup_left hgD) hg1).symm.trans
      (hfix g' hg'A (Subgroup.mem_sup_right hg'X) hg'1))

end Z3Cg1

end CFSG.Quasithin

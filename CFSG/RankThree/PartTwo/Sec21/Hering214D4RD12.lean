module

public import CFSG.RankThree.PartTwo.Sec3.ElemNineAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

theorem map_ne_one_of_sq_eq_one_of_odd_ker {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Odd (Nat.card φ.ker)) {g : G} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) : φ g ≠ 1 := by
  intro h
  have hdvd : orderOf g ∣ Nat.card φ.ker :=
    Subgroup.orderOf_dvd_natCard _ (MonoidHom.mem_ker.mpr h)
  rw [orderOf_eq_prime hg2 hg1] at hdvd
  exact (Nat.not_even_iff_odd.mpr hφ) (even_iff_two_dvd.mpr hdvd)

theorem sr_sq_eq_one (i : ZMod 6) : (DihedralGroup.sr i : DihedralGroup 6) ^ 2 = 1 := by
  rw [sq, DihedralGroup.sr_mul_self]

theorem exists_fixed_and_inverted {E : Type*} [CommGroup E] (hE3 : ∀ e : E, e ^ 3 = 1)
    {σ : MulAut E} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (hσι : ¬ ∀ e : E, σ e = e⁻¹) :
    ∃ e₁ e₂ : E, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ σ e₁ = e₁ ∧ σ e₂ = e₂⁻¹ := by
  obtain ⟨e₁, he₁, hfix⟩ :=
    CFSG.RankThree.PartTwo.Sec3.exists_apply_eq_self_of_mul_self_eq_one hE3 hσ hσι
  obtain ⟨e₂, he₂, hinv⟩ :=
    CFSG.RankThree.PartTwo.Sec3.exists_apply_eq_inv_of_mul_self_eq_one hσ hσ1
  exact ⟨e₁, e₂, he₁, he₂, hfix, hinv⟩

theorem exists_reflection_of_dihedral {E : Type*} [CommGroup E] [Finite E]
    (hE3 : ∀ e : E, e ^ 3 = 1) (hE9 : Nat.card E = 9) (ρ : DihedralGroup 6 →* MulAut E)
    (hρ : Odd (Nat.card ρ.ker)) :
    ∃ d : DihedralGroup 6, ∃ e₁ e₂ : E, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ ρ d e₁ = e₁ ∧ ρ d e₂ = e₂⁻¹ := by
  have hsr0 : (DihedralGroup.sr 0 : DihedralGroup 6) ^ 2 = 1 := sr_sq_eq_one 0
  have hsr3 : (DihedralGroup.sr 3 : DihedralGroup 6) ^ 2 = 1 := sr_sq_eq_one 3
  have hr3 : (DihedralGroup.r 3 : DihedralGroup 6) ^ 2 = 1 := by decide
  have hsr0' : (DihedralGroup.sr 0 : DihedralGroup 6) ≠ 1 := by decide
  have hsr3' : (DihedralGroup.sr 3 : DihedralGroup 6) ≠ 1 := by decide
  have hr3' : (DihedralGroup.r 3 : DihedralGroup 6) ≠ 1 := by decide
  have hprod : (DihedralGroup.sr 3 : DihedralGroup 6) * DihedralGroup.sr 0 =
      DihedralGroup.r 3 := by decide
  have key : ∀ d : DihedralGroup 6, d ^ 2 = 1 → d ≠ 1 → ¬ (∀ e : E, ρ d e = e⁻¹) →
      ∃ e₁ e₂ : E, e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ ρ d e₁ = e₁ ∧ ρ d e₂ = e₂⁻¹ := by
    intro d hd2 hd1 hι
    have hσ : ρ d * ρ d = 1 := by rw [← map_mul, ← sq, hd2, map_one]
    exact exists_fixed_and_inverted hE3 hσ (map_ne_one_of_sq_eq_one_of_odd_ker ρ hρ hd2 hd1) hι
  by_cases h0 : ∀ e : E, ρ (DihedralGroup.sr 0) e = e⁻¹
  · by_cases h3 : ∀ e : E, ρ (DihedralGroup.sr 3) e = e⁻¹
    ·
      exfalso
      refine map_ne_one_of_sq_eq_one_of_odd_ker ρ hρ hr3 hr3' ?_
      rw [← hprod, map_mul]
      ext e
      simp [h0, h3]
    · exact ⟨DihedralGroup.sr 3, key _ hsr3 hsr3' h3⟩
  · exact ⟨DihedralGroup.sr 0, key _ hsr0 hsr0' h0⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214

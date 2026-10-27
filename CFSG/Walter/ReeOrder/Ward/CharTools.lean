module

public import CFSG.Walter.ReeOrder.Ward.Columns4
public import CFSG.CharacterTheory.BlockBasics.Bridge
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.ConjugateRepresentation
public import CFSG.CharacterTheory.PSL2Table.BlockTools
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

variable {G : Type} [Group G] [Fintype G]

theorem inv_eq_conj {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (g : G) :
    χ g⁻¹ = starRingEnd ℂ (χ g) := by
  obtain ⟨V, _, _, _, ρ, -, rfl⟩ := hχ
  exact CFSG.Section1.representation_character_inv_eq_star_character ρ g

theorem irr_pow {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {k : ℕ} (hk : (Nat.card G).Coprime k) :
    (fun g => χ (g ^ k)) ∈ BlocksIrr G := by
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨l, rfl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis hχ
  obtain ⟨b, hb⟩ := CFSG.LyonsUnitaryFour.exists_label_character_pow basis hk l
  rw [show (fun g => (basis.representation l).character (g ^ k)) =
    (basis.representation b).character from funext fun g => (hb g).symm]
  exact CFSG.BlockBasics.basis_character_mem_irr basis b

theorem irr_conj {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) : starRingEnd ℂ ∘ χ ∈ BlocksIrr G := by
  have hk : (Nat.card G).Coprime (Nat.card G - 1) := by
    have hpos := Nat.card_pos (α := G)
    rcases Nat.lt_or_ge (Nat.card G) 2 with h | h
    · have : Nat.card G = 1 := by omega
      rw [this]
      exact Nat.coprime_one_left _
    · have h1 : Nat.card G = (Nat.card G - 1) + 1 := by omega
      rw [Nat.coprime_comm]
      conv_rhs => rw [h1]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have h := irr_pow hχ hk
  have heq : (fun g => χ (g ^ (Nat.card G - 1))) = starRingEnd ℂ ∘ χ := by
    funext g
    have hg : g ^ (Nat.card G - 1) = g⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one']
    rw [hg, inv_eq_conj hχ]
    rfl
  rwa [heq] at h

omit [Group G] [Fintype G] in
theorem conj_conj_fun (χ : G → ℂ) : starRingEnd ℂ ∘ (starRingEnd ℂ ∘ χ) = χ := by
  funext g
  simp

theorem omega_dvd {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (g : G) {t : ℤ} (ht : χ g = t) :
    deg χ ∣ (Nat.card (ConjClasses.mk g).carrier : ℤ) * t := by
  have hint := CFSG.BrauerThirdMainTheorem.Helpers.centralChar_integral_coefficients hχ
    (coefficients := CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients (ConjClasses.mk g))
    (fun x => by
      unfold CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _)
    (fun x c => by
      have hequal : ConjClasses.mk (c * x * c⁻¹) = ConjClasses.mk x :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨c, rfl⟩).symm
      unfold CFSG.BrauerThirdMainTheorem.Helpers.classCoefficients
      by_cases h : ConjClasses.mk x = ConjClasses.mk g
      · simp only [hequal, h, ↓reduceIte]
      · simp only [hequal, h, ↓reduceIte])
  rw [CFSG.PSL2Table.centralChar_classCoefficients
    (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)) g, ht, ← deg_eq hχ] at hint
  have hd0 : (deg χ : ℚ) ≠ 0 := by exact_mod_cast (deg_pos hχ).ne'
  have hrat : IsIntegral ℤ (((Nat.card (ConjClasses.mk g).carrier : ℚ) * t) / deg χ) :=
    IsIntegral.tower_bot_of_field (B := ℂ) (by
      simpa only [map_div₀, map_mul, map_intCast, map_natCast] using hint)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  change (m : ℚ) = _ at hm
  refine ⟨m, ?_⟩
  have : ((Nat.card (ConjClasses.mk g).carrier : ℚ) * t) = deg χ * m := by
    rw [hm]
    field_simp
  exact_mod_cast this

end CFSG.Walter.Ward

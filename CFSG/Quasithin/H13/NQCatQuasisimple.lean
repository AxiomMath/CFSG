module

public import CFSG.Quasithin.H13.NQCatSporadic
public import CFSG.Quasithin.H13.NQCatExceptional
public import CFSG.Quasithin.H13.NQTermClassicalOuterPrime
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence center_map_equiv)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

theorem sylow_isCyclic_pRank_le_one_of_eq_bot {X : Type*} [Group X] {ℓ : ℕ}
    (h : (∀ P : Sylow ℓ X, (P : Subgroup X) = ⊥) ∧ CFSG.pRank ℓ X = 0) :
    (∀ P : Sylow ℓ X, IsCyclic P) ∧ CFSG.pRank ℓ X ≤ 1 := by
  refine ⟨fun P => ?_, h.2.le.trans zero_le_one⟩
  rw [h.1 P]
  infer_instance

theorem sqt_catalog_center_quotient
    {J : Type} [Group J] [Finite J] (hJ : CFSG.IsQuasisimple J)
    (hsqtk : SectionRank.IsSQTKCat J) :
    CFSG.IsStronglyQuasithin (J ⧸ Subgroup.center J) ∧ Catalog (J ⧸ Subgroup.center J) := by
  obtain ⟨-, hsimple, hnonab⟩ := hJ
  let e₀ : (⊤ : Subgroup J) ⧸ Subgroup.center (⊤ : Subgroup J) ≃* J ⧸ Subgroup.center J :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (center_map_equiv _)
  have : IsSimpleGroup ((⊤ : Subgroup J) ⧸ Subgroup.center (⊤ : Subgroup J)) :=
    e₀.isSimpleGroup
  have hnonab' : ∃ a b : (⊤ : Subgroup J) ⧸ Subgroup.center (⊤ : Subgroup J), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e₀.symm a, e₀.symm b, fun h => hab ?_⟩
    have := congrArg e₀ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  obtain ⟨hSQT₀, hcat₀⟩ := SectionRank.sqt_catalog_of_simple_section_of_sqtk hsqtk ⊤ _ hnonab'
  exact ⟨SectionRank.isStronglyQuasithin_of_mulEquiv e₀.symm hSQT₀,
    SectionRank.catalog_of_mulEquiv e₀.symm hcat₀⟩

theorem sqtk_quasisimple_outer_prime_control_or_J4
    (J : Type) [Group J] [Finite J]
    (hJ : CFSG.IsQuasisimple J) (hsqtk : SectionRank.IsSQTKCat J) :
    Nonempty (J ⧸ Subgroup.center J ≃* NativeSporadic.J4) ∨
      ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
        (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1 := by
  obtain ⟨hSQT, hcat⟩ := sqt_catalog_center_quotient hJ hsqtk
  obtain ⟨hperf, hsimple, hnonab⟩ := hJ
  have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hexc | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · right
    have hle : Nat.card (Outer (J ⧸ Subgroup.center J)) ≤ 4 := by
      rcases (show n = 6 ∨ n = 5 ∨ 7 ≤ n by omega) with rfl | hn'
      · rw [Nat.card_congr (equivalence e).toEquiv]
        exact Sporadic.SchreierLemmas.outer_alternating_six.1
      · exact (Nat.le_of_dvd (by norm_num)
          (outer_card_dvd_two_of_equiv_outside_six hn' e)).trans (by norm_num)
    have hJle := (card_outer_le_of_perfect J (MulEquiv.refl _)).trans hle
    exact fun ℓ hℓ hℓ5 =>
      sylow_isCyclic_pRank_le_one_of_eq_bot (outer_large_prime_of_card_le_four hJle ℓ hℓ hℓ5)
  · exact Or.inr (NQTerm.sqt_classical_central_quotient_outer_prime_control J hSQT hcl)
  · exact Or.inr fun ℓ hℓ hℓ5 =>
      (sqt_exceptional_central_quotient_outer_prime_control J hSQT hexc).2 ℓ hℓ (by omega)
  · rcases sqt_sporadic_perfect_cover_outer_J4_alternative J inferInstance hSQT hspor with
      h | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr fun ℓ hℓ hℓ5 => sylow_isCyclic_pRank_le_one_of_eq_bot (h ℓ hℓ hℓ5)

end CFSG.Quasithin.H13.NQCat

module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
import CFSG.LocalAnalysis.StandardType.ZS.TableMonomial
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableOrth
import CFSG.LocalAnalysis.StandardType.ZS.TableOrthClass
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.TableLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem negOrGen_of_monomial {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hJ : J = gmmn p f i₀ i₁ ζ ∨ J = g2mmn p f i₀ i₁ ζ) : NegOrGen p n J := by
  rcases hJ with rfl | rfl
  · exact negOrGen_gmmn f hi ζ
  · exact Or.inl (neg_mem_g2mmn f i₀ i₁ ζ)

theorem negOrGen_of_family (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {J : Subgroup (U ≃ₗ[ZMod p] U)} (hF : Family p J)
    (hT : TableHyp p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J) :
    NegOrGen p (Module.finrank (ZMod p) U) J := by
  cases hF with
  | weyl h => exact (tableConclusions_of_linWeyl hp h3 h hT hprim).1
  | slpm hA => exact (not_transvectionFree_of_mem_iff_det (by omega) hA hT.transvectionFree).elim
  | orth Q hQ hJ => exact (tableConclusions_orth hp h3 hQ hJ).1
  | orthClass Q c hQ hc hJ => exact negOrGen_orthClass hp h3 hQ hc hJ hT
  | gmmn f i₀ i₁ ζ _m hi _hm _hζ hA =>
      rw [hA, Module.finrank_eq_card_basis f, Fintype.card_fin]
      exact negOrGen_of_monomial f hi ζ (Or.inl rfl)
  | g2mmn f i₀ i₁ ζ _m hi _hm _hζ hA =>
      rw [hA, Module.finrank_eq_card_basis f, Fintype.card_fin]
      exact negOrGen_of_monomial f hi ζ (Or.inr rfl)
  | exc k _hadm _hdim _hcard hcen _hdmax _hone _hmodel =>
      refine Or.inl (neg_mem_of_two_dvd_card_center
        (absIrred_of_reflGen hT.reflGen hT.irreducible) ?_ ?_)
      · rw [hcen]; cases k <;> decide
      · rw [hcen]; cases k <;> decide
  | h4 _hp5 _hdim _hcard hneg _hdmax _hone => exact Or.inl hneg

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
theorem tfNegOrGen_of_useInputAt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {m : ℕ} (hm : 3 ≤ m)
    (hU : UseInputAt m) : TFNegOrGen p m := by
  intro U _ _ _ J hdim hR hTF hirr hd
  have hT : TableHyp p J := ⟨hR, hTF, hirr, hd⟩
  have hA : AbsIrred p J := absIrred_of_reflGen hR hirr
  by_cases himp : Quasithin.SimsG4.IsImprimitiveOnV J
  · obtain ⟨f, i₀, i₁, ζ, hi, hJ⟩ := exists_basis_eq_gmmn_or_g2mmn hp hdim hm hR hA himp
    exact negOrGen_of_monomial f hi ζ hJ
  · rw [← hdim]
    exact negOrGen_of_family hp (by omega) (hU p U J hp hdim hR hA) hT himp

theorem tfNegOrGen_of_lt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {n : ℕ}
    (hU : ∀ m, 3 ≤ m → m < n → UseInputAt m) : ∀ m, m < n → TFNegOrGen p m := by
  intro m hm
  by_cases h3 : 3 ≤ m
  · exact tfNegOrGen_of_useInputAt hp h3 (hU m h3 hm)
  · have hm2 : m ≤ 2 := by omega
    interval_cases m
    · exact (tableFactsAt_of_le_one (m := 0) (by omega)).1
    · exact (tableFactsAt_of_le_one (m := 1) (by omega)).1
    · exact (tableFactsAt_two hp).1

end CFSG.StandardType.ZS

end

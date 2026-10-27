module

public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsDefs
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsTransport
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsRefl
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsMonomial
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrthGeom
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsModels
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrth
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.Monomial
import CFSG.LocalAnalysis.StandardType.ZS.WeylModule
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableOrth
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtStab

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {W V : Type} [AddCommGroup W] [Module (ZMod p) W]
  [AddCommGroup V] [Module (ZMod p) V]

theorem two_dvd_excRow_cen (k : ExcRow) : 2 ∣ k.cen := by
  cases k <;> decide

theorem forty_eight_lt_excRow_ord (k : ExcRow) : 48 < k.ord := by
  cases k <;> decide

private theorem tfim_neg_mem_of_linWeyl_three (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hL : LinWeyl p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    (LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) ∈ J := by
  rcases isCartanModel_cases_of_linWeyl hp (by omega) hA.1 hL with
    ⟨ℓ, hAℓ, T, hT⟩ | ⟨ℓ, hℓ, hB⟩ | ⟨ℓ, hℓ, hD⟩ | hE6 | hE7 | hE8 | hF4
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_typeA hp T hT hx hy hxr hyr) (by omega)
  · exact absurd (isImprimitiveOnV_of_isCartanModel_B hp hℓ hB) hprim
  · exact absurd (isImprimitiveOnV_of_isCartanModel_D hp hℓ hD) hprim
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inl rfl) hE6 hTF hx hy hxr hyr)
      (by omega)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd
      (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inl rfl)) hE7 hTF hx hy hxr hyr)
      (by omega)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd
      (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inr rfl)) hE8 hTF hx hy hxr hyr)
      (by omega)
  · exact neg_mem_of_isCartanModel_F4 hF4

theorem neg_mem_of_family_three (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hF : Family p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hnot : ¬ IsOrthType p J) (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    (LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) ∈ J := by
  rcases hF with hL | hS | ⟨Q, hQ, hJ⟩ | ⟨Q, c, hQ, hc, hJ⟩ |
    ⟨f, i₀, i₁, ζ, m, hi, hm, hord, hJ⟩ | ⟨f, i₀, i₁, ζ, m, hi, hm, hord, hJ⟩ |
    ⟨k, hadm, hdeg, hord, hcen, hdm, honc, hmodel⟩ | ⟨hp5, hdeg, hcard, hneg, hdm, honc⟩
  · exact tfim_neg_mem_of_linWeyl_three hp hdim hL hA hprim hTF hd
  · exact absurd hTF (not_transvectionFree_of_mem_iff_det (by omega) hS)
  · exact absurd ⟨Q, hQ, Or.inl hJ⟩ hnot
  · exact absurd ⟨Q, hQ, Or.inr ⟨c, hc, hJ⟩⟩ hnot
  · exact absurd (by
      rw [hJ]
      exact isImprimitiveOnV_gmmn (by
        have h := Module.finrank_eq_card_basis f
        rw [hdim] at h
        simp at h
        omega) f i₀ i₁ ζ) hprim
  · exact absurd (by
      rw [hJ]
      exact isImprimitiveOnV_g2mmn (by
        have h := Module.finrank_eq_card_basis f
        rw [hdim] at h
        simp at h
        omega) f i₀ i₁ ζ) hprim
  · refine neg_mem_of_two_dvd_card_center hA ?_ ?_
    · rw [hcen]; exact two_dvd_excRow_cen k
    · rw [hcen]; cases k <;> decide
  · exact hneg

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
theorem tfNegOfPrimThree_of_useInputAt {p : ℕ} [Fact p.Prime] (hU : UseInputAt 3) :
    TFNegOfPrimThree p := by
  intro W _ _ _ X hp hX hTF hs hprim hnot hd
  exact neg_mem_of_family_three hp hs.2.1 (family_movedGroup hp hU hX hs)
    (absIrred_movedGroup hX hs) hprim hnot (transvectionFree_movedGroup hs hTF)
    ((exists_pair_movedGroup_iff hs (fun k => 3 < k)).mpr hd)

end CFSG.StandardType.ZS

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {W V : Type} [AddCommGroup W] [Module (ZMod p) W]
  [AddCommGroup V] [Module (ZMod p) V]

theorem eq_g2mmn_of_monomial_three (hp : p ≠ 2) (b : Module.Basis (Fin 3) (ZMod p) V)
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hJ : J = gmmn p b i₀ i₁ ζ ∨ J = g2mmn p b i₀ i₁ ζ)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hcard : Nat.card J ≤ 48) : J = g2mmn p b 0 1 1 := by
  rcases hJ with hJeq | hJeq
  · exfalso
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    have hxg : x ∈ gmmn p b i₀ i₁ ζ := by rwa [hJeq] at hx
    have hyg : y ∈ gmmn p b i₀ i₁ ζ := by rwa [hJeq] at hy
    have hdvd : orderOf (x * y) ∣ orderOf ζ := by
      rcases orderOf_mul_le_three_or_dvd_of_mem_gmmn hp b hi ζ hxg hyg hxr hyr with h3 | h
      · omega
      · exact h
    have h4 : 4 ≤ orderOf ζ :=
      le_trans (by omega : 4 ≤ orderOf (x * y)) (Nat.le_of_dvd (orderOf_pos ζ) hdvd)
    have hcardJ : Nat.card J = orderOf ζ ^ 2 * 6 := by
      rw [hJeq, card_gmmn (n := 3) (by norm_num) b hi ζ]
      norm_num
    have h96 : 96 ≤ Nat.card J := by
      rw [hcardJ]
      nlinarith
    omega
  · have hcard' : Nat.card (g2mmn p b i₀ i₁ ζ) ≤ 48 := by
      rw [hJeq] at hcard
      exact hcard
    have hcardJ : Nat.card (g2mmn p b i₀ i₁ ζ) =
        2 * Nat.lcm 2 (orderOf ζ) ^ 2 * 6 := by
      rw [card_g2mmn hp (n := 3) (by norm_num) b hi ζ]
      norm_num
    have hlcm_le : Nat.lcm 2 (orderOf ζ) ≤ 2 := by nlinarith [hcard', hcardJ]
    have hlcm_ge : 2 ≤ Nat.lcm 2 (orderOf ζ) :=
      Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos ζ))
        (Nat.dvd_lcm_left 2 (orderOf ζ))
    have hlcm : Nat.lcm 2 (orderOf ζ) = 2 := le_antisymm hlcm_le hlcm_ge
    have hdvd : orderOf ζ ∣ 2 := by
      rw [← hlcm]
      exact Nat.dvd_lcm_right 2 (orderOf ζ)
    have hζ2 : ζ * ζ = 1 := by
      rw [orderOf_dvd_iff_pow_eq_one] at hdvd
      rwa [pow_two] at hdvd
    rw [hJeq]
    exact g2mmn_eq_g2mmn_of_mul_self_eq_one b hi (by decide : (0 : Fin 3) ≠ 1) hζ2

private theorem tfim_five_le_of_prime_ne_two_ne_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : 5 ≤ p := by
  have hodd : Odd p := ((Fact.out : Nat.Prime p).eq_two_or_odd').resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  have h2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  omega

private theorem tfim_false_of_linWeyl_small_three (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hL : LinWeyl p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) : False := by
  rcases isCartanModel_cases_of_linWeyl hp (by omega) hA.1 hL with
    ⟨ℓ, hAℓ, T, hT⟩ | ⟨ℓ, hℓ, hB⟩ | ⟨ℓ, hℓ, hD⟩ | hE6 | hE7 | hE8 | hF4
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_typeA hp T hT hx hy hxr hyr) (by omega)
  · exact absurd (isImprimitiveOnV_of_isCartanModel_B hp hℓ hB) hprim
  · exact absurd (isImprimitiveOnV_of_isCartanModel_D hp hℓ hD) hprim
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inl rfl) hE6 hTF hx hy hxr hyr)
      (by omega)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd
      (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inl rfl)) hE7 hTF hx hy hxr hyr)
      (by omega)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd
      (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inr rfl)) hE8 hTF hx hy hxr hyr)
      (by omega)
  · obtain ⟨f', hJf⟩ := exists_basis_eq_basisClosure_weylF4 hp hF4
    have hfr : Module.finrank (ZMod p) V = 4 := by
      rw [Module.finrank_eq_card_basis f']
      simp
    omega

private theorem tfim_false_of_isOrthType_small (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hO3 : p = 3 → ¬ IsOrthType p J) (hcard : Nat.card J ≤ 48)
    (horth : IsOrthType p J) : False := by
  by_cases hp3 : p = 3
  · exact hO3 hp3 horth
  · have := sixty_le_card_of_isOrthType_three (tfim_five_le_of_prime_ne_two_ne_three hp hp3)
      hdim horth
    omega

theorem false_of_family_small_three (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hF : Family p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hcard : Nat.card J ≤ 48) (hO3 : p = 3 → ¬ IsOrthType p J) : False := by
  rcases hF with hL | hS | ⟨Q, hQ, hJ⟩ | ⟨Q, c, hQ, hc, hJ⟩ |
    ⟨f, i₀, i₁, ζ, m, hi, hm, hord, hJ⟩ | ⟨f, i₀, i₁, ζ, m, hi, hm, hord, hJ⟩ |
    ⟨k, hadm, hdeg, hord, hcen, hdm, honc, hmodel⟩ | ⟨hp5, hdeg4, hcard4, hneg, hdm4, honc4⟩
  · exact tfim_false_of_linWeyl_small_three hp hdim hL hA hprim hTF hd
  · exact absurd hTF (not_transvectionFree_of_mem_iff_det (by omega) hS)
  · exact tfim_false_of_isOrthType_small hp hdim hO3 hcard ⟨Q, hQ, Or.inl hJ⟩
  · exact tfim_false_of_isOrthType_small hp hdim hO3 hcard ⟨Q, hQ, Or.inr ⟨c, hc, hJ⟩⟩
  · exact absurd (by
      rw [hJ]
      exact isImprimitiveOnV_gmmn (by
        have h := Module.finrank_eq_card_basis f
        rw [hdim] at h
        simp at h
        omega) f i₀ i₁ ζ) hprim
  · exact absurd (by
      rw [hJ]
      exact isImprimitiveOnV_g2mmn (by
        have h := Module.finrank_eq_card_basis f
        rw [hdim] at h
        simp at h
        omega) f i₀ i₁ ζ) hprim
  · have h48 := forty_eight_lt_excRow_ord k
    omega
  · omega

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
theorem tfSmallThree_of_useInputAt {p : ℕ} [Fact p.Prime] (hU : UseInputAt 3) :
    TFSmallThree p := by
  intro W _ _ _ X hp hX hTF hs hd hcard
  have hcard' : Nat.card (movedGroup X) ≤ 48 := by
    rw [card_movedGroup_of_splitSupport hs]
    exact hcard
  by_cases himp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)
  · obtain ⟨b, i₀, i₁, ζ, hi, hJ⟩ :=
      exists_monomial_movedGroup hp (by norm_num : 3 ≤ 3) hX hs himp
    have hd' : ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
        IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
      (exists_pair_movedGroup_iff hs (fun k => 3 < k)).mpr hd
    exact ⟨b, eq_g2mmn_of_monomial_three hp b hi ζ hJ hd' hcard'⟩
  · exact (false_of_family_small_three hp hs.2.1 (family_movedGroup hp hU hX hs)
      (absIrred_movedGroup hX hs) himp (transvectionFree_movedGroup hs hTF)
      ((exists_pair_movedGroup_iff hs (fun k => 3 < k)).mpr hd) hcard'
      (fun h3 hO => himp (tfOrthThreeThree h3 W X hs hO))).elim

end CFSG.StandardType.ZS

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {W V : Type} [AddCommGroup W] [Module (ZMod p) W]
  [AddCommGroup V] [Module (ZMod p) V]

theorem false_of_dMax_four_dim_two (hp : p ≠ 2) (g : Module.Basis (Fin 2) (ZMod p) V)
    {j₀ j₁ : Fin 2} (hj : j₀ ≠ j₁) (ζ : (ZMod p)ˣ) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hJd : DMax p J 4)
    (hrow : J = gmmn p g j₀ j₁ ζ ∧ ¬ orderOf ζ = 4 ∨
      J = g2mmn p g j₀ j₁ ζ ∧ ¬ (orderOf ζ ∣ 2 ∨ orderOf ζ = 4)) : False := by
  rcases hrow with ⟨hJeq, hne⟩ | ⟨hJeq, hne⟩
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := exists_pair_orderOf_eq_of_gmmn hp g hj ζ
    have hle : orderOf ζ ≤ 4 := by
      rw [← hxy]
      exact hJd.1 x (by rwa [← hJeq] at hx) y (by rwa [← hJeq] at hy) hxr hyr
    obtain ⟨x', hx', y', hy', hx'r, hy'r, hxy'⟩ := hJd.2
    have hx'g : x' ∈ gmmn p g j₀ j₁ ζ := by rwa [hJeq] at hx'
    have hy'g : y' ∈ gmmn p g j₀ j₁ ζ := by rwa [hJeq] at hy'
    rcases orderOf_mul_le_three_or_dvd_of_mem_gmmn hp g hj ζ hx'g hy'g hx'r hy'r with h3 | hdvd
    · omega
    · rw [hxy'] at hdvd
      have h4 : 4 ≤ orderOf ζ := Nat.le_of_dvd (orderOf_pos ζ) hdvd
      omega
  · have hne1 : ¬ orderOf ζ ∣ 2 := fun h => hne (Or.inl h)
    have hne2 : ¬ orderOf ζ = 4 := fun h => hne (Or.inr h)
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := exists_pair_orderOf_eq_lcm_of_g2mmn hp g hj ζ
    have hlcm_le : Nat.lcm 2 (orderOf ζ) ≤ 4 := by
      rw [← hxy]
      exact hJd.1 x (by rwa [← hJeq] at hx) y (by rwa [← hJeq] at hy) hxr hyr
    have hζle : orderOf ζ ≤ 4 :=
      le_trans (Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos ζ))
        (Nat.dvd_lcm_right 2 (orderOf ζ))) hlcm_le
    have hζge : 1 ≤ orderOf ζ := orderOf_pos ζ
    interval_cases hζo : orderOf ζ
    · exact absurd (by norm_num : (1 : ℕ) ∣ 2) hne1
    · exact absurd (by norm_num : (2 : ℕ) ∣ 2) hne1
    · norm_num at hlcm_le
    · exact absurd rfl hne2

private theorem tfim_false_of_gmmn_h4 (hp : p ≠ 2) [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 5) {Y : Subgroup (W ≃ₗ[ZMod p] W)}
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin 3} (hj : j₀ ≠ j₁) (ζ : (ZMod p)ˣ) (hrow : movedGroup Y = gmmn p g j₀ j₁ ζ)
    {Q : QuadraticForm (ZMod p) W} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQY : ∀ y ∈ Y, IsIsom p Q y)
    (hpair : ∃ x ∈ movedGroup Y, ∃ y ∈ movedGroup Y, IsRefl p x ∧ IsRefl p y ∧
      orderOf (x * y) = 5) : False := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hpair
  have hxg : x ∈ gmmn p g j₀ j₁ ζ := by rwa [hrow] at hx
  have hyg : y ∈ gmmn p g j₀ j₁ ζ := by rwa [hrow] at hy
  have h5dvd : 5 ∣ orderOf ζ := by
    rcases orderOf_mul_le_three_or_dvd_of_mem_gmmn hp g hj ζ hxg hyg hxr hyr with h3 | h
    · omega
    · rw [hxy] at h; exact h
  have hζ : ζ * ζ ≠ 1 := by
    intro h
    have h2 : orderOf ζ ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rwa [pow_two]
    have h52 : 5 ∣ 2 := dvd_trans h5dvd h2
    norm_num at h52
  exact false_of_gmmn_le_of_isIsom (n := 3) (by norm_num) g hj hζ (le_of_eq hrow.symm) hQ hQY
    (by omega)

private theorem tfim_false_of_g2mmn_h4 (hp : p ≠ 2) {Y : Subgroup (W ≃ₗ[ZMod p] W)}
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin 3} (hj : j₀ ≠ j₁) (ζ : (ZMod p)ˣ) (hrow : movedGroup Y = g2mmn p g j₀ j₁ ζ)
    (hdYmg : DMax p (movedGroup Y) 5)
    (hpair : ∃ x ∈ movedGroup Y, ∃ y ∈ movedGroup Y, IsRefl p x ∧ IsRefl p y ∧
      orderOf (x * y) = 5) : False := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hpair
  have hxg : x ∈ g2mmn p g j₀ j₁ ζ := by rwa [hrow] at hx
  have hyg : y ∈ g2mmn p g j₀ j₁ ζ := by rwa [hrow] at hy
  have h5dvd : 5 ∣ Nat.lcm 2 (orderOf ζ) := by
    rcases orderOf_mul_le_four_or_dvd_of_mem_g2mmn hp g hj ζ hxg hyg hxr hyr with h4 | h
    · omega
    · rw [hxy] at h; exact h
  obtain ⟨x', hx', y', hy', hx'r, hy'r, hxy'⟩ := exists_pair_orderOf_eq_lcm_of_g2mmn hp g hj ζ
  have hlcm_le : Nat.lcm 2 (orderOf ζ) ≤ 5 := by
    rw [← hxy']
    exact hdYmg.1 x' (by rwa [← hrow] at hx') y' (by rwa [← hrow] at hy') hx'r hy'r
  have hlcm_ge : 5 ≤ Nat.lcm 2 (orderOf ζ) :=
    Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos ζ)) h5dvd
  have hlcm : Nat.lcm 2 (orderOf ζ) = 5 := le_antisymm hlcm_le hlcm_ge
  have h2 : 2 ∣ Nat.lcm 2 (orderOf ζ) := Nat.dvd_lcm_left 2 (orderOf ζ)
  rw [hlcm] at h2
  norm_num at h2

theorem false_of_h4Mats_corank (hp : p ≠ 2) [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 5) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 5) (ZMod p) W) {Y : Subgroup (W ≃ₗ[ZMod p] W)}
    (hYX : Y ≤ basisClosure f (h4Mats α)) (hsY : SplitSupport Y 3) (hdY : DMax p Y 5)
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin 3} (hj : j₀ ≠ j₁) (ζ : (ZMod p)ˣ)
    (hrow : movedGroup Y = gmmn p g j₀ j₁ ζ ∨ movedGroup Y = g2mmn p g j₀ j₁ ζ) : False := by
  let w : Fin 5 → ZMod p := ![1 + α, 1 + α, 1, 1 + α, 1]
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    fin_cases i <;> simp [w, one_add_ne_zero_of_sq_eq hα]
  have hQ : (QuadraticMap.polarBilin (basisDiagForm f w)).Nondegenerate :=
    basisDiagForm_nondegenerate hp f hw
  have hQY : ∀ y ∈ Y, IsIsom p (basisDiagForm f w) y := by
    intro y hy
    exact isIsom_basisDiagForm_of_mem_basisClosure f w (h4Mats_orthogonal hp hα) (hYX hy)
  have hdYmg : DMax p (movedGroup Y) 5 := (dmax_movedGroup_iff hsY 5).mpr hdY
  have hpair : ∃ x ∈ movedGroup Y, ∃ y ∈ movedGroup Y, IsRefl p x ∧ IsRefl p y ∧
      orderOf (x * y) = 5 :=
    (exists_pair_movedGroup_iff hsY (fun k => k = 5)).mpr hdY.2
  rcases hrow with hrow | hrow
  · exact tfim_false_of_gmmn_h4 hp hW g hj ζ hrow hQ hQY hpair
  · exact tfim_false_of_g2mmn_h4 hp g hj ζ hrow hdYmg hpair

private theorem tfim_false_of_gmmn_f4 (hp : p ≠ 2) [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 5) {Y : Subgroup (W ≃ₗ[ZMod p] W)}
    (hsY : SplitSupport Y 3) (hdY : DMax p Y 4)
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin 3} (hj : j₀ ≠ j₁) (ζ : (ZMod p)ˣ) (hrow : movedGroup Y = gmmn p g j₀ j₁ ζ)
    {Q : QuadraticForm (ZMod p) W} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hQY : ∀ y ∈ Y, IsIsom p Q y) : False := by
  by_cases hζ : ζ * ζ = 1
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ :=
      (exists_pair_movedGroup_iff hsY (fun k => k = 4)).mpr hdY.2
    have hxg : x ∈ gmmn p g j₀ j₁ ζ := by rwa [hrow] at hx
    have hyg : y ∈ gmmn p g j₀ j₁ ζ := by rwa [hrow] at hy
    have hdvd : orderOf ζ ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rwa [pow_two]
    rcases orderOf_mul_le_three_or_dvd_of_mem_gmmn hp g hj ζ hxg hyg hxr hyr with h3 | h
    · omega
    · rw [hxy] at h
      exact absurd (dvd_trans h hdvd) (by norm_num : ¬ (4 ∣ 2))
  · exact false_of_gmmn_le_of_isIsom (n := 3) (by norm_num) g hj hζ (le_of_eq hrow.symm) hQ hQY
      (by omega)

theorem card_eq_of_f4ExtMats_corank (hp : p ≠ 2) [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 5) (f : Module.Basis (Fin 5) (ZMod p) W)
    {Y : Subgroup (W ≃ₗ[ZMod p] W)} (hYX : Y ≤ basisClosure f f4ExtMats)
    (hsY : SplitSupport Y 3) (hdY : DMax p Y 4)
    (g : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y))
    {j₀ j₁ : Fin 3} (hj : j₀ ≠ j₁) (ζ : (ZMod p)ˣ)
    (hrow : movedGroup Y = gmmn p g j₀ j₁ ζ ∨ movedGroup Y = g2mmn p g j₀ j₁ ζ) :
    Nat.card Y = 48 := by
  have hQ : (QuadraticMap.polarBilin (basisDiagForm f (1 : Fin 5 → ZMod p))).Nondegenerate :=
    basisDiagForm_nondegenerate hp f (fun _ => one_ne_zero)
  have hQY : ∀ y ∈ Y, IsIsom p (basisDiagForm f (1 : Fin 5 → ZMod p)) y := by
    intro y hy
    exact isIsom_basisDiagForm_of_mem_basisClosure f 1 (f4ExtMats_orthogonal hp) (hYX hy)
  rcases hrow with hrow | hrow
  · exact (tfim_false_of_gmmn_f4 hp hW hsY hdY g hj ζ hrow hQ hQY).elim
  · rw [← card_movedGroup_of_splitSupport hsY]
    by_cases hζ : ζ * ζ = 1
    · rw [hrow, card_g2mmn hp (n := 3) (by norm_num) g hj ζ]
      have hdvd : orderOf ζ ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        rwa [pow_two]
      have hlcm_dvd : Nat.lcm 2 (orderOf ζ) ∣ 2 := Nat.lcm_dvd (dvd_refl 2) hdvd
      have hlcm_le : Nat.lcm 2 (orderOf ζ) ≤ 2 := Nat.le_of_dvd (by norm_num) hlcm_dvd
      have hlcm_ge : 2 ≤ Nat.lcm 2 (orderOf ζ) :=
        Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos ζ))
          (Nat.dvd_lcm_left 2 (orderOf ζ))
      rw [le_antisymm hlcm_le hlcm_ge]
      norm_num
    · exfalso
      exact false_of_gmmn_le_of_isIsom (n := 3) (by norm_num) g hj hζ
        (le_trans (gmmn_le_g2mmn g j₀ j₁ ζ) (le_of_eq hrow.symm)) hQ hQY (by omega)

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
theorem tfPrimCorankDim_of_primCorankOne {p : ℕ} [Fact p.Prime] {l : ℕ}
    (hPC : TFPrimCorankOne p l) (hH3 : TFH3DataModel p) : TFPrimCorankDim p l := by
  intro W _ _ _ X Y d hp hW hX hTF hs hprim hnot hcen hdX hd3 hYX hY hsY hdY g j₀ j₁ ζ hj hrow
  have hl3 : 3 ≤ l := by
    have h1 : 1 < Fintype.card (Fin (l - 1)) := Fintype.one_lt_card_iff.mpr ⟨j₀, j₁, hj⟩
    rw [Fintype.card_fin] at h1
    omega
  rcases hPC W X d hp hl3 hW hX hTF hs hprim hnot hcen hdX hd3 with
    ⟨hl, hd, hp5, α, f, hα, hXeq⟩ | ⟨hl, hd, hp7, β, f, hβ, hXeq⟩ |
    ⟨hl, hd, hp5, α, f, hα, hXeq⟩ | ⟨hl, hd, hp3, f, hXeq⟩
  · subst hl; subst hd
    exact Or.inl ⟨rfl, rfl, by rw [hXeq]; exact hH3 W f α hp hα⟩
  · exfalso
    subst hl; subst hd
    have hJd : DMax p (movedGroup Y) 4 := (dmax_movedGroup_iff hsY 4).mpr hdY
    have hrow' : movedGroup Y = gmmn p g j₀ j₁ ζ ∧ ¬ orderOf ζ = 4 ∨
        movedGroup Y = g2mmn p g j₀ j₁ ζ ∧ ¬ (orderOf ζ ∣ 2 ∨ orderOf ζ = 4) := by
      simpa using hrow
    exact false_of_dMax_four_dim_two hp g hj ζ hJd hrow'
  · exfalso
    subst hl; subst hd
    have hYX' : Y ≤ basisClosure f (h4Mats α) := by rwa [hXeq] at hYX
    have hsY' : SplitSupport Y 3 := by simpa using hsY
    have hdY' : DMax p Y 5 := by simpa using hdY
    have hrow' : movedGroup Y = gmmn p g j₀ j₁ ζ ∨ movedGroup Y = g2mmn p g j₀ j₁ ζ :=
      hrow.imp And.left And.left
    exact false_of_h4Mats_corank hp hW hα f hYX' hsY' hdY' g hj ζ hrow'
  · subst hl; subst hd
    refine Or.inr ⟨rfl, rfl, ?_, ?_⟩
    · rw [hXeq]; exact card_basisClosure_f4ExtMats hp f
    · have hYX' : Y ≤ basisClosure f f4ExtMats := by rwa [hXeq] at hYX
      have hsY' : SplitSupport Y 3 := by simpa using hsY
      have hdY' : DMax p Y 4 := by simpa using hdY
      have hrow' : movedGroup Y = gmmn p g j₀ j₁ ζ ∨ movedGroup Y = g2mmn p g j₀ j₁ ζ :=
        hrow.imp And.left And.left
      exact card_eq_of_f4ExtMats_corank hp hW f hYX' hsY' hdY' g hj ζ hrow'

end CFSG.StandardType.ZS

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {W V : Type} [AddCommGroup W] [Module (ZMod p) W]
  [AddCommGroup V] [Module (ZMod p) V]

theorem false_of_monomial_of_threeGroup (hp3 : p = 3) [Module.Finite (ZMod p) W] {l : ℕ}
    (hl : 4 ≤ l) {X : Subgroup (W ≃ₗ[ZMod p] W)} (hs : SplitSupport X l)
    (b : Module.Basis (Fin l) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    {i₀ i₁ : Fin l} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hJ : movedGroup X = gmmn p b i₀ i₁ ζ ∨ movedGroup X = g2mmn p b i₀ i₁ ζ)
    {T : Subgroup (W ≃ₗ[ZMod p] W)} (hTX : T ≤ X) (hTp : ∀ s ∈ T, s ^ p = 1)
    (hcard : p ^ (l - 2) ≤ Nat.card T) : False := by
  subst hp3
  have hTp3 : ∀ t : T, orderOf t = 1 ∨ orderOf t = 3 := by
    intro t
    have h1 : orderOf (t : W ≃ₗ[ZMod 3] W) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hTp (t : W ≃ₗ[ZMod 3] W) t.2
    rw [Subgroup.orderOf_coe t] at h1
    exact (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h1
  have hpg : IsPGroup 3 T := IsPGroup.iff_orderOf.mpr fun t => by
    rcases hTp3 t with h | h
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
  have hcardT_ne : Nat.card T ≠ 0 := by
    intro h
    have hpos : 0 < 3 ^ (l - 2) := pow_pos (by norm_num) _
    omega
  have hTfin : Finite T := Nat.finite_of_card_ne_zero hcardT_ne
  obtain ⟨k, hk⟩ := (@IsPGroup.iff_card 3 T _ _ hTfin).mp hpg
  have hkge : l - 2 ≤ k := by
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp ?_
    rw [← hk]
    exact hcard
  have hdvd : 3 ^ k ∣ 2 ^ l * l.factorial := by
    have h1 : 3 ^ k ∣ Nat.card X := by
      rw [← hk]
      exact Subgroup.card_dvd_of_le hTX
    rw [(card_movedGroup_of_splitSupport hs).symm] at h1
    exact dvd_trans h1 (card_dvd_two_pow_mul_factorial_of_three (p := 3) rfl (by omega) b hi ζ hJ)
  have h2k := two_mul_add_one_le_of_three_pow_dvd (n := l) (k := k) (by omega) hdvd
  omega

theorem false_of_exc_of_three (hp3 : p = 3) [Module.Finite (ZMod p) V]
    (h4 : 4 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (k : ExcRow)
    (hadm : k.admissible p) (hdeg : Module.finrank (ZMod p) V = k.deg)
    (hcen : Nat.card (Subgroup.center J) = k.cen) (hdm : DMax p J k.dmax) (hA : AbsIrred p J) :
    False := by
  subst hp3
  have hcendvd : Nat.card (Subgroup.center J) ∣ 2 := by
    simpa using card_center_dvd_of_absIrred hA
  cases k <;> simp_all [ExcRow.deg, ExcRow.cen, ExcRow.dmax, ExcRow.admissible]
  obtain ⟨x, hx, y, hy, hxr, hyr, h5⟩ := hdm.2
  rcases five_dvd_of_orderOf_mul_eq_five hxr hyr h5 with h | h | h <;> norm_num at h

theorem isOrthType_of_family_three_deg (hp3 : p = 3) [Module.Finite (ZMod p) V]
    (h4 : 4 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hF : Family p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    IsOrthType p J := by
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  rcases hF with hL | hS | ⟨Q, hQ, hJ⟩ | ⟨Q, c, hQ, hc, hJ⟩ |
    ⟨f, i₀, i₁, ζ, m, hi, hm, hord, hJ⟩ | ⟨f, i₀, i₁, ζ, m, hi, hm, hord, hJ⟩ |
    ⟨k, hadm, hdeg, hord, hcen, hdm, honc, hmodel⟩ | ⟨hp5, hdeg4, hcard4, hneg, hdm4, honc4⟩
  · exact isOrthType_of_linWeyl_of_dLarge hp2 (by omega) hL hA hprim hTF hd
      (fun h5 => absurd h5 (by omega))
  · exact absurd hTF (not_transvectionFree_of_mem_iff_det (by omega) hS)
  · exact ⟨Q, hQ, Or.inl hJ⟩
  · exact ⟨Q, hQ, Or.inr ⟨c, hc, hJ⟩⟩
  · exact absurd (by
      rw [hJ]
      exact isImprimitiveOnV_gmmn (by
        have h := Module.finrank_eq_card_basis f
        simp at h
        omega) f i₀ i₁ ζ) hprim
  · exact absurd (by
      rw [hJ]
      exact isImprimitiveOnV_g2mmn (by
        have h := Module.finrank_eq_card_basis f
        simp at h
        omega) f i₀ i₁ ζ) hprim
  · exact (false_of_exc_of_three hp3 h4 k hadm hdeg hcen hdm hA).elim
  · obtain ⟨x, hx, y, hy, hxr, hyr, h5⟩ := hdm4.2
    rcases five_dvd_of_orderOf_mul_eq_five hxr hyr h5 with h | h | h
    · rw [hp3] at h; omega
    · rw [hp3] at h; norm_num at h
    · rw [hp3] at h; norm_num at h

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
theorem tfDegenerateExtThree_of_useInputAt {p : ℕ} [Fact p.Prime] {l : ℕ} (hU : UseInputAt l) :
    TFDegenerateExtThree p l := by
  intro W _ _ _ X hp3 hl hX hTF hs hd T hTX hTp hTc hcard hT2
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  by_cases himp : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)
  · obtain ⟨b, i₀, i₁, ζ, hi, hJ⟩ :=
      exists_monomial_movedGroup hp2 (by omega : 3 ≤ l) hX hs himp
    exact (false_of_monomial_of_threeGroup hp3 hl hs b hi ζ hJ hTX hTp hcard).elim
  · refine ⟨himp, isOrthType_of_family_three_deg hp3 ?_ (family_movedGroup hp2 hU hX hs)
      (absIrred_movedGroup hX hs) himp (transvectionFree_movedGroup hs hTF) ?_⟩
    · rw [hs.2.1]; exact hl
    · exact (exists_pair_movedGroup_iff hs (fun k => 3 < k)).mpr hd

end CFSG.StandardType.ZS

end

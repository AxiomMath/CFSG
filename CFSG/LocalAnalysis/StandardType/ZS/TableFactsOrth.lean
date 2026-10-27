module

public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsDefs
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsTransport
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsRefl
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsMonomial
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrthGeom
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.MonomialRows
import CFSG.LocalAnalysis.StandardType.ZS.TypeA
import CFSG.LocalAnalysis.StandardType.ZS.Monomial
import CFSG.LocalAnalysis.StandardType.ZS.WeylModule
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableOrth
import CFSG.LocalAnalysis.StandardType.GGLevTwoS4cAux
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtStab

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
  [AddCommGroup V] [Module (ZMod p) V]

theorem exists_pair_movedGroup_of_le {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X) {l m : ℕ}
    (hsY : SplitSupport Y l) (hsX : SplitSupport X m) (P : ℕ → Prop)
    (h : ∃ x ∈ movedGroup Y, ∃ y ∈ movedGroup Y, IsRefl p x ∧ IsRefl p y ∧ P (orderOf (x * y))) :
    ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X, IsRefl p x ∧ IsRefl p y ∧ P (orderOf (x * y)) := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hP⟩ := (exists_pair_movedGroup_iff hsY P).mp h
  exact (exists_pair_movedGroup_iff hsX P).mpr ⟨x, hYX hx, y, hYX hy, hxr, hyr, hP⟩

theorem exists_orderOf_movedGroup_of_le {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X)
    {l m : ℕ} (hsY : SplitSupport Y l) (hsX : SplitSupport X m) (k : ℕ)
    (h : ∃ g ∈ movedGroup Y, orderOf g = k) : ∃ g ∈ movedGroup X, orderOf g = k := by
  obtain ⟨g, hg, hk⟩ := (exists_orderOf_movedGroup_iff hsY k).mp h
  exact (exists_orderOf_movedGroup_iff hsX k).mpr ⟨g, hYX hg, hk⟩

private theorem tfor_not_dvd_prime_sub_one {q : ℕ} (hq : q.Prime) (_h2 : q ≠ 2) :
    ¬ q ∣ q - 1 := by
  intro h
  have hq2 : 2 ≤ q := hq.two_le
  have hle : q ≤ q - 1 := Nat.le_of_dvd (by omega) h
  omega

private theorem tfor_not_dvd_two_mul_sub_one {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) :
    ¬ q ∣ 2 * (q - 1) := by
  intro h
  rcases hq.dvd_mul.mp h with h | h
  · have hle := Nat.le_of_dvd (by norm_num) h
    have := hq.two_le
    omega
  · exact tfor_not_dvd_prime_sub_one hq h2 h

private theorem tfor_lcm_two_dvd_two_mul_sub_one (ζ : (ZMod p)ˣ) :
    Nat.lcm 2 (orderOf ζ) ∣ 2 * (p - 1) :=
  Nat.lcm_dvd (dvd_mul_right 2 (p - 1))
    (dvd_mul_of_dvd_right (ZMod.orderOf_units_dvd_card_sub_one ζ) 2)

theorem not_dvd_card_monomial (hp : p ≠ 2) {n : ℕ} (hn : 2 ≤ n) (hnp : n < p)
    (b : Module.Basis (Fin n) (ZMod p) V) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hJ : J = gmmn p b i₀ i₁ ζ ∨ J = g2mmn p b i₀ i₁ ζ) :
    ¬ p ∣ Nat.card J := by
  have hpp : p.Prime := Fact.out
  have hz : ¬ p ∣ orderOf ζ := fun h =>
    tfor_not_dvd_prime_sub_one hpp hp
      (dvd_trans h (ZMod.orderOf_units_dvd_card_sub_one ζ))
  have hfac : ¬ p ∣ n.factorial := by
    rw [hpp.dvd_factorial]
    omega
  rcases hJ with rfl | rfl
  · rw [card_gmmn hn b hi ζ]
    intro h
    rcases hpp.dvd_mul.mp h with h1 | h2
    · exact hz (hpp.dvd_of_dvd_pow h1)
    · exact hfac h2
  · rw [card_g2mmn hp hn b hi ζ]
    intro h
    rcases hpp.dvd_mul.mp h with h1 | h2
    · rcases hpp.dvd_mul.mp h1 with h2 | h3
      · have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
        have := hpp.two_le
        omega
      · exact tfor_not_dvd_two_mul_sub_one hpp hp
          (dvd_trans (hpp.dvd_of_dvd_pow h3) (tfor_lcm_two_dvd_two_mul_sub_one ζ))
    · exact hfac h2

theorem orderOf_mul_ne_of_monomial (hp5 : 5 ≤ p) {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) V)
    {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hJ : J = gmmn p b i₀ i₁ ζ ∨ J = g2mmn p b i₀ i₁ ζ) {x y : V ≃ₗ[ZMod p] V} (hx : x ∈ J)
    (hy : y ∈ J) (hxr : IsRefl p x) (hyr : IsRefl p y) : orderOf (x * y) ≠ p := by
  have hp : p ≠ 2 := by rintro rfl; norm_num at hp5
  have hx2 : x ∈ g2mmn p b i₀ i₁ ζ := by
    rcases hJ with hJ | hJ
    · rw [hJ] at hx; exact gmmn_le_g2mmn b i₀ i₁ ζ hx
    · rwa [hJ] at hx
  have hy2 : y ∈ g2mmn p b i₀ i₁ ζ := by
    rcases hJ with hJ | hJ
    · rw [hJ] at hy; exact gmmn_le_g2mmn b i₀ i₁ ζ hy
    · rwa [hJ] at hy
  have h4 := orderOf_mul_le_four_or_dvd_of_mem_g2mmn hp b hi ζ hx2 hy2 hxr hyr
  intro hp_eq
  rcases h4 with hle | hdvd
  · omega
  · have h2 : p ∣ 2 * (p - 1) := by
      have h := dvd_trans hdvd (tfor_lcm_two_dvd_two_mul_sub_one ζ)
      rwa [hp_eq] at h
    exact tfor_not_dvd_two_mul_sub_one (Fact.out : p.Prime) hp h2

private theorem tfor_five_le_of_prime {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) :
    5 ≤ q := by
  rcases Nat.lt_or_ge q 5 with hlt | hge
  · have h2q : 2 ≤ q := hq.two_le
    interval_cases q
    · exact absurd rfl h2
    · exact absurd rfl h3
    · exact absurd hq (by decide)
  · exact hge

private theorem tfor_intCast_ne_zero {q k : ℕ} (_hq : q.Prime) (hk0 : 0 < k) (hk : k < q) :
    ((k : ℤ) : ZMod q) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  rw [Int.natCast_dvd_natCast] at h
  exact absurd (Nat.le_of_dvd hk0 h) (by omega)

theorem six_le_finrank_of_isCartanModel_E (hp : p ≠ 2) (hp3 : p ≠ 3) [Module.Finite (ZMod p) V]
    {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : IsCartanModel p (CartanMatrix.E n) J) : 6 ≤ Module.finrank (ZMod p) V := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases hn with rfl | rfl | rfl
  · rw [IsCartanModel.finrank_eq_card_of_det hA
      (by rw [LevTwo.levTwoS4c_det_E6];
          exact tfor_intCast_ne_zero (q := p) (k := 3) Fact.out (by norm_num) (by omega))]
    simp
  · rw [IsCartanModel.finrank_eq_card_of_det hA
      (by rw [LevTwo.levTwoS4c_det_E7];
          exact tfor_intCast_ne_zero (q := p) (k := 2) Fact.out (by norm_num) (by omega))]
    simp
  · rw [IsCartanModel.finrank_eq_card_of_det hA
      (by rw [LevTwo.levTwoS4c_det_E8];
          exact tfor_intCast_ne_zero (q := p) (k := 1) Fact.out (by norm_num) (by omega))]
    simp

theorem isOrthType_of_linWeyl_of_dLarge (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h3 : 3 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (h : LinWeyl p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p) : IsOrthType p J := by
  rcases isCartanModel_cases_of_linWeyl hp h3 hA.1 h with
    ⟨ℓ, _hAℓ, T, hT⟩ | ⟨ℓ, hℓ2, hBℓ⟩ | ⟨ℓ, hℓ4, hDℓ⟩ | hE6 | hE7 | hE8 | hF4
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_typeA hp T hT hx hy hxr hyr) (not_le.mpr hxy)
  · exact absurd (isImprimitiveOnV_of_isCartanModel_B hp hℓ2 hBℓ) hprim
  · exact absurd (isImprimitiveOnV_of_isCartanModel_D hp hℓ4 hDℓ) hprim
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inl rfl) hE6 hTF hx hy hxr hyr)
      (not_le.mpr hxy)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inl rfl)) hE7 hTF
      hx hy hxr hyr) (not_le.mpr hxy)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inr rfl)) hE8 hTF
      hx hy hxr hyr) (not_le.mpr hxy)
  · obtain ⟨f, hJeq⟩ := exists_basis_eq_basisClosure_weylF4 hp hF4
    by_cases hp3 : p = 3
    · rw [hJeq]; exact isOrthType_basisClosure_weylF4_three hp3 f
    · have hp5 : 5 ≤ p := tfor_five_le_of_prime (Fact.out : p.Prime) hp hp3
      obtain ⟨g, hg, hgord⟩ := hpJ hp5
      rw [hJeq] at hg
      exact absurd hgord (orderOf_ne_of_mem_basisClosure_weylF4 hp5 f hg)

private theorem tfor_prime_dvd_120 {q : ℕ} (hq : q.Prime) (h : q ∣ 120) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  have h' : q ∣ 2 ^ 3 * 3 * 5 := by
    rw [show (120 : ℕ) = 2 ^ 3 * 3 * 5 by norm_num] at h; exact h
  rcases hq.dvd_mul.mp h' with h23 | h5
  · rcases hq.dvd_mul.mp h23 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hq h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5))

theorem isOrthType_of_linWeyl_of_corankOne (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h4 : 4 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (h : LinWeyl p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : p = 3 ∨ 5 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p) : IsOrthType p J := by
  have hpp : p.Prime := Fact.out
  by_cases hcase : p = 3 ∨ 5 ≤ Module.finrank (ZMod p) V
  · exact isOrthType_of_linWeyl_of_dLarge hp (by omega) h hA hprim hTF (hd hcase) hpJ
  · have hp3 : p ≠ 3 := fun h => hcase (Or.inl h)
    have hdim5 : ¬ 5 ≤ Module.finrank (ZMod p) V := fun h => hcase (Or.inr h)
    have hdim : Module.finrank (ZMod p) V = 4 := by omega
    have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
    rcases isCartanModel_cases_of_linWeyl hp (by omega) hA.1 h with
      ⟨ℓ, _hAℓ, T, hT⟩ | ⟨ℓ, hℓ2, hBℓ⟩ | ⟨ℓ, hℓ4, hDℓ⟩ | hE6 | hE7 | hE8 | hF4
    · rcases symmetric_row_of_isCartanModel_A hp hdim _hAℓ T hT with
        ⟨hp5dvd, e, he⟩ | ⟨hp6dvd, e, he⟩
      · obtain ⟨g, hg, hgord⟩ := hpJ hp5
        have hcard : Nat.card J = 120 := by
          rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
          norm_num
        have hpdvd : p ∣ Nat.card J := by
          have h := Subgroup.orderOf_dvd_natCard J hg
          rwa [hgord] at h
        have h120 : p ∣ 120 := by rwa [hcard] at hpdvd
        have hp_eq5 : p = 5 := by
          rcases tfor_prime_dvd_120 hpp h120 with h | h | h
          · omega
          · omega
          · exact h
        rw [hp_eq5] at hp5dvd
        exact absurd (dvd_refl 5) hp5dvd
      · have hp6 : p ∣ 6 := by simpa using hp6dvd
        have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hp6
        interval_cases p
        · norm_num at hp6
        · norm_num at hpp
    · exact absurd (isImprimitiveOnV_of_isCartanModel_B hp hℓ2 hBℓ) hprim
    · exact absurd (isImprimitiveOnV_of_isCartanModel_D hp hℓ4 hDℓ) hprim
    · exact absurd (six_le_finrank_of_isCartanModel_E hp hp3 (Or.inl rfl) hE6) (by omega)
    · exact absurd (six_le_finrank_of_isCartanModel_E hp hp3 (Or.inr (Or.inl rfl)) hE7) (by omega)
    · exact absurd (six_le_finrank_of_isCartanModel_E hp hp3 (Or.inr (Or.inr rfl)) hE8) (by omega)
    · obtain ⟨f, hJeq⟩ := exists_basis_eq_basisClosure_weylF4 hp hF4
      obtain ⟨g, hg, hgord⟩ := hpJ hp5
      rw [hJeq] at hg
      exact absurd hgord (orderOf_ne_of_mem_basisClosure_weylF4 hp5 f hg)

private theorem tfor_prime_dvd_336 {q : ℕ} (hq : q.Prime) (h : q ∣ 336) :
    q = 2 ∨ q = 3 ∨ q = 7 := by
  have h7 : Nat.Prime 7 := by norm_num
  have h' : q ∣ 2 ^ 4 * 3 * 7 := by
    rw [show (336 : ℕ) = 2 ^ 4 * 3 * 7 by norm_num] at h; exact h
  rcases hq.dvd_mul.mp h' with h23 | h7'
  · rcases hq.dvd_mul.mp h23 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hq h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq h7).mp h7'))

private theorem tfor_prime_dvd_2160 {q : ℕ} (hq : q.Prime) (h : q ∣ 2160) :
    q = 2 ∨ q = 3 ∨ q = 5 := by
  have h' : q ∣ 2 ^ 4 * 3 ^ 3 * 5 := by
    rw [show (2160 : ℕ) = 2 ^ 4 * 3 ^ 3 * 5 by norm_num] at h; exact h
  rcases hq.dvd_mul.mp h' with h23 | h5
  · rcases hq.dvd_mul.mp h23 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hq h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (Nat.Prime.dvd_of_dvd_pow hq h3)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5))

private theorem tfor_false_of_cen_four_of_eq_three [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hp3 : p = 3)
    (hcen : Nat.card (Subgroup.center J) = 4) (hA : AbsIrred p J) : False := by
  have h4 : 4 ∣ p - 1 := by
    rw [← hcen]
    exact card_center_dvd_of_absIrred hA
  rw [hp3] at h4
  norm_num at h4

private theorem tfor_false_of_cen_six_of_eq_five [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hp5 : p = 5)
    (hcen : Nat.card (Subgroup.center J) = 6) (hA : AbsIrred p J) : False := by
  have h6 : 6 ∣ p - 1 := by
    rw [← hcen]
    exact card_center_dvd_of_absIrred hA
  rw [hp5] at h6
  norm_num at h6

private theorem tfor_false_of_pair_dmax_four [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2)
    (hdeg : Module.finrank (ZMod p) V = 4) (hcen : Nat.card (Subgroup.center J) = 4)
    (hdm : DMax p J 4) (hA : AbsIrred p J)
    (hpair : 4 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p) : False := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hpair (by omega)
  have hp_le : p ≤ 4 := by have := hdm.1 x hx y hy hxr hyr; omega
  have h2p : 2 ≤ p := hpp.two_le
  have hp3 : p = 3 := by
    interval_cases p
    · exact absurd rfl hp
    · rfl
    · exact absurd hpp (by decide)
  exact tfor_false_of_cen_four_of_eq_three hp3 hcen hA

private theorem tfor_false_of_h4_overgroup [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2) (hadm : p ≠ 5)
    (hdeg : Module.finrank (ZMod p) V = 4) (hdm : DMax p J 5)
    (hpair : 4 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p) : False := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hpair (by omega)
  have hp_le : p ≤ 5 := by have := hdm.1 x hx y hy hxr hyr; omega
  have h2p : 2 ≤ p := hpp.two_le
  have hp3 : p = 3 := by
    interval_cases p
    · exact absurd rfl hp
    · rfl
    · exact absurd hpp (by decide)
    · exact absurd rfl hadm
  obtain ⟨u, hu, v, hv, hur, hvr, huv⟩ := hdm.2
  have h5 := five_dvd_of_orderOf_mul_eq_five hur hvr huv
  rw [hp3] at h5
  norm_num at h5

private theorem tfor_false_of_exc_H3 [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2) (hadm : p ≠ 5)
    (hdeg : Module.finrank (ZMod p) V = 3) (hord : Nat.card J = 120)
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (h33 : Module.finrank (ZMod p) V = 3 → p ≠ 3) : False := by
  have hp3 : p ≠ 3 := h33 hdeg
  have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
  obtain ⟨g, hg, hgord⟩ := hpJ hp5
  have hdvd : p ∣ 120 := by
    have h := Subgroup.orderOf_dvd_natCard J hg
    rwa [hgord, hord] at h
  rcases tfor_prime_dvd_120 hpp hdvd with h | h | h
  · omega
  · omega
  · exact hadm h

private theorem tfor_false_of_exc_J34 [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2) (hadm : p ≠ 7)
    (hdeg : Module.finrank (ZMod p) V = 3) (hord : Nat.card J = 336)
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (h33 : Module.finrank (ZMod p) V = 3 → p ≠ 3) : False := by
  have hp3 : p ≠ 3 := h33 hdeg
  have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
  obtain ⟨g, hg, hgord⟩ := hpJ hp5
  have hdvd : p ∣ 336 := by
    have h := Subgroup.orderOf_dvd_natCard J hg
    rwa [hgord, hord] at h
  rcases tfor_prime_dvd_336 hpp hdvd with h | h | h
  · omega
  · omega
  · exact hadm h

private theorem tfor_false_of_exc_J35 [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2)
    (hdeg : Module.finrank (ZMod p) V = 3) (hord : Nat.card J = 2160)
    (hcen : Nat.card (Subgroup.center J) = 6) (hA : AbsIrred p J)
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (h33 : Module.finrank (ZMod p) V = 3 → p ≠ 3) : False := by
  have hp3 : p ≠ 3 := h33 hdeg
  have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
  obtain ⟨g, hg, hgord⟩ := hpJ hp5
  have hdvd : p ∣ 2160 := by
    have h := Subgroup.orderOf_dvd_natCard J hg
    rwa [hgord, hord] at h
  rcases tfor_prime_dvd_2160 hpp hdvd with h | h | h
  · omega
  · omega
  · exact tfor_false_of_cen_six_of_eq_five h hcen hA

theorem false_of_exc_of_overgroup (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (k : ExcRow) (hadm : k.admissible p)
    (hdeg : Module.finrank (ZMod p) V = k.deg) (hord : Nat.card J = k.ord)
    (hcen : Nat.card (Subgroup.center J) = k.cen) (hdm : DMax p J k.dmax) (hA : AbsIrred p J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (hpair : 4 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p)
    (h33 : Module.finrank (ZMod p) V = 3 → p ≠ 3) : False := by
  have hpp : p.Prime := Fact.out
  have h2p : 2 ≤ p := hpp.two_le
  cases k <;> simp only [ExcRow.deg, ExcRow.ord, ExcRow.cen, ExcRow.dmax, ExcRow.admissible] at *
  · exact tfor_false_of_pair_dmax_four hpp hp hdeg hcen hdm hA hpair
  · exact tfor_false_of_pair_dmax_four hpp hp hdeg hcen hdm hA hpair
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (hdm.1 x hx y hy hxr hyr) (not_le.mpr hxy)
  · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hd
    exact absurd (hdm.1 x hx y hy hxr hyr) (not_le.mpr hxy)
  · exact tfor_false_of_h4_overgroup hpp hp hadm hdeg hdm hpair
  · exact tfor_false_of_exc_H3 hpp hp hadm hdeg hord hpJ h33
  · exact tfor_false_of_exc_J34 hpp hp hadm hdeg hord hpJ h33
  · exact tfor_false_of_exc_J35 hpp hp hdeg hord hcen hA hpJ h33
  · have h6 : 6 ∣ p - 1 := by
      have h := card_center_dvd_of_absIrred hA
      rwa [hcen] at h
    rw [hadm] at h6
    norm_num at h6
  · exact tfor_false_of_cen_four_of_eq_three hadm hcen hA

theorem isOrthType_of_family_of_overgroup (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h3 : 3 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hF : Family p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd : ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (hpair : 4 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p)
    (h33 : Module.finrank (ZMod p) V = 3 → p ≠ 3) : IsOrthType p J := by
  cases hF with
  | weyl hlin => exact isOrthType_of_linWeyl_of_dLarge hp h3 hlin hA hprim hTF hd hpJ
  | slpm hslpm =>
      exact absurd hTF (not_transvectionFree_of_mem_iff_det (by omega) hslpm)
  | orth Q hQ hmem => exact ⟨Q, hQ, Or.inl hmem⟩
  | orthClass Q c hQ hc hcl => exact ⟨Q, hQ, Or.inr ⟨c, hc, hcl⟩⟩
  | gmmn f i₀ i₁ ζ m hi hm3 hord hAeq =>
      exfalso
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hAeq] at hprim
      exact absurd (isImprimitiveOnV_gmmn (b := f) (hn := by omega) i₀ i₁ ζ) hprim
  | g2mmn f i₀ i₁ ζ m hi hm2 hord hAeq =>
      exfalso
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hAeq] at hprim
      exact absurd (isImprimitiveOnV_g2mmn (b := f) (hn := by omega) i₀ i₁ ζ) hprim
  | exc k hk hdeg hcard hcen hdm hone hmodel =>
      exfalso
      exact false_of_exc_of_overgroup hp k hk hdeg hcard hcen hdm hA hd hpJ hpair h33
  | h4 hp5 hdeg hcard hneg hdm hone =>
      exfalso
      exact tfor_false_of_h4_overgroup (Fact.out : p.Prime) hp hp5 hdeg hdm hpair

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
theorem tfOrthOvergroup_of_useInputAt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {m : ℕ} (hm : 3 ≤ m)
    (hU : UseInputAt m) : TFOrthOvergroup p m := by
  intro U _ _ _ X Y hYX hX hTF hsX hY hsY hOY hprimY hdY
  have hV : HardMathSupport.Kantor79.commutatorSpace Y =
      HardMathSupport.Kantor79.commutatorSpace X := commutatorSpace_eq_of_le hYX hsX hsY
  have hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) :=
    not_isImprimitiveOnV_movedGroup_of_le hYX hV hprimY
  have hF : Family p (movedGroup X) := family_movedGroup hp hU hX hsX
  have hA : AbsIrred p (movedGroup X) := absIrred_movedGroup hX hsX
  have hTF' : QTwoLin.TransvectionFree (movedGroup X) := transvectionFree_movedGroup hsX hTF
  have h3 : 3 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) := by
    rw [hsX.2.1]; exact hm
  have hd : ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    exists_pair_movedGroup_of_le hYX hsY hsX (fun k => 3 < k)
      ((exists_pair_movedGroup_iff hsY (fun k => 3 < k)).mpr hdY)
  have hpJ : 5 ≤ p → ∃ g ∈ movedGroup X, orderOf g = p := by
    intro hp5
    have hdimY : 3 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) := by
      rw [hsY.2.1]; exact hm
    exact exists_orderOf_movedGroup_of_le hYX hsY hsX p
      (exists_orderOf_eq_of_isOrthType hp5 hdimY hOY)
  have hpair : 4 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) →
      ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
        IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p := by
    intro h4
    have h4' : 4 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) := by
      rw [hV]; exact h4
    exact exists_pair_movedGroup_of_le hYX hsY hsX (fun k => k = p)
      (exists_pair_orderOf_eq_of_isOrthType hp h4' hOY)
  have h33 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3 →
      p ≠ 3 := by
    intro hdim3 hp3
    have hm3 : m = 3 := by rw [← hsX.2.1]; exact hdim3
    exact hprimY (tfOrthThreeThree hp3 U Y (hm3 ▸ hsY) hOY)
  exact isOrthType_of_family_of_overgroup hp h3 hF hA hprim hTF' hd hpJ hpair h33

end CFSG.StandardType.ZS

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module (ZMod p) U]
  [AddCommGroup V] [Module (ZMod p) V]

private theorem tfor_prime_dvd_235 {q a b c : ℕ} (hq : q.Prime)
    (h : q ∣ 2 ^ a * 3 ^ b * 5 ^ c) : q = 2 ∨ q = 3 ∨ q = 5 := by
  rcases hq.dvd_mul.mp h with h23 | h5
  · rcases hq.dvd_mul.mp h23 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hq h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (Nat.Prime.dvd_of_dvd_pow hq h3)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp
      (Nat.Prime.dvd_of_dvd_pow hq h5)))

private theorem tfor_false_of_exc_corank_N4 [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2)
    (hdeg : Module.finrank (ZMod p) V = 4) (hord : Nat.card J = 2 ^ 9 * 3 * 5)
    (hcen : Nat.card (Subgroup.center J) = 4)
    (_hdm : DMax p J 4) (hA : AbsIrred p J) (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (hmodel : ModelIso p .N4 J)
    (hN : Module.finrank (ZMod p) V = 4 → p = 5 →
      ¬ (ModelIso p .N4 J ∨ ModelIso p .EN4 J)) : False := by
  by_cases hp3 : p = 3
  · exact tfor_false_of_cen_four_of_eq_three hp3 hcen hA
  · have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
    obtain ⟨g, hg, hgord⟩ := hpJ hp5
    have hdvd : p ∣ 2 ^ 9 * 3 ^ 1 * 5 ^ 1 := by
      have h := Subgroup.orderOf_dvd_natCard J hg
      rw [hgord, hord] at h
      rwa [show (2 ^ 9 * 3 * 5 : ℕ) = 2 ^ 9 * 3 ^ 1 * 5 ^ 1 by norm_num] at h
    have hp_eq5 : p = 5 := by
      rcases tfor_prime_dvd_235 hpp hdvd with h | h | h
      · omega
      · omega
      · exact h
    exact (hN hdeg hp_eq5) (Or.inl hmodel)

private theorem tfor_false_of_exc_corank_EN4 [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2)
    (hdeg : Module.finrank (ZMod p) V = 4) (hord : Nat.card J = 2 ^ 10 * 3 ^ 2 * 5)
    (hcen : Nat.card (Subgroup.center J) = 4)
    (_hdm : DMax p J 4) (hA : AbsIrred p J) (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (hmodel : ModelIso p .EN4 J)
    (hN : Module.finrank (ZMod p) V = 4 → p = 5 →
      ¬ (ModelIso p .N4 J ∨ ModelIso p .EN4 J)) : False := by
  by_cases hp3 : p = 3
  · exact tfor_false_of_cen_four_of_eq_three hp3 hcen hA
  · have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
    obtain ⟨g, hg, hgord⟩ := hpJ hp5
    have hdvd : p ∣ 2 ^ 10 * 3 ^ 2 * 5 ^ 1 := by
      have h := Subgroup.orderOf_dvd_natCard J hg
      rw [hgord, hord] at h
      rwa [show (2 ^ 10 * 3 ^ 2 * 5 : ℕ) = 2 ^ 10 * 3 ^ 2 * 5 ^ 1 by norm_num] at h
    have hp_eq5 : p = 5 := by
      rcases tfor_prime_dvd_235 hpp hdvd with h | h | h
      · omega
      · omega
      · exact h
    exact (hN hdeg hp_eq5) (Or.inr hmodel)

private theorem tfor_false_of_exc_corank_K [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2) (hadm : p ≠ 3)
    (h5 : 5 ≤ Module.finrank (ZMod p) V) (hdm : DMax p J 3)
    (hpair : 5 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p) : False := by
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hpair h5
  have hple : p ≤ 3 := by have := hdm.1 x hx y hy hxr hyr; omega
  have h2p : 2 ≤ p := hpp.two_le
  have hp3 : p = 3 := by
    interval_cases p
    · exact absurd rfl hp
    · rfl
  exact hadm hp3

private theorem tfor_false_of_exc_corank_H4 [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hpp : p.Prime) (hp : p ≠ 2) (hadm : p ≠ 5)
    (_hdeg : Module.finrank (ZMod p) V = 4) (hord : Nat.card J = 2 ^ 6 * 3 ^ 2 * 5 ^ 2)
    (hdm : DMax p J 5) (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p) : False := by
  by_cases hp3 : p = 3
  · obtain ⟨u, hu, v, hv, hur, hvr, huv⟩ := hdm.2
    have h5 := five_dvd_of_orderOf_mul_eq_five hur hvr huv
    rw [hp3] at h5
    norm_num at h5
  · have hp5 : 5 ≤ p := tfor_five_le_of_prime hpp hp hp3
    obtain ⟨g, hg, hgord⟩ := hpJ hp5
    have hdvd : p ∣ 2 ^ 6 * 3 ^ 2 * 5 ^ 2 := by
      have h := Subgroup.orderOf_dvd_natCard J hg
      rwa [hgord, hord] at h
    have hp_eq5 : p = 5 := by
      rcases tfor_prime_dvd_235 hpp hdvd with h | h | h
      · omega
      · omega
      · exact h
    exact hadm hp_eq5

theorem false_of_exc_of_corankOne (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (k : ExcRow) (hadm : k.admissible p)
    (hdeg : Module.finrank (ZMod p) V = k.deg) (hord : Nat.card J = k.ord)
    (hcen : Nat.card (Subgroup.center J) = k.cen) (hdm : DMax p J k.dmax)
    (hmodel : k.needsModel → ModelIso p k J) (hA : AbsIrred p J)
    (h4 : 4 ≤ Module.finrank (ZMod p) V) (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (hpair : 5 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p)
    (hN : Module.finrank (ZMod p) V = 4 → p = 5 →
      ¬ (ModelIso p .N4 J ∨ ModelIso p .EN4 J)) : False := by
  have hpp : p.Prime := Fact.out
  have h2p : 2 ≤ p := hpp.two_le
  cases k <;> simp only [ExcRow.deg, ExcRow.ord, ExcRow.cen, ExcRow.dmax, ExcRow.admissible] at *
  · exact tfor_false_of_exc_corank_N4 hpp hp hdeg hord hcen hdm hA hpJ (hmodel trivial) hN
  · exact tfor_false_of_exc_corank_EN4 hpp hp hdeg hord hcen hdm hA hpJ (hmodel trivial) hN
  · exact tfor_false_of_exc_corank_K hpp hp hadm (by omega) hdm hpair
  · exact tfor_false_of_exc_corank_K hpp hp hadm (by omega) hdm hpair
  · exact tfor_false_of_exc_corank_H4 hpp hp hadm hdeg hord hdm hpJ
  · omega
  · omega
  · omega
  · omega
  · exact tfor_false_of_cen_four_of_eq_three hadm hcen hA

theorem false_of_h4_of_corankOne (hp : p ≠ 2) [Module.Finite (ZMod p) V] (hp5 : p ≠ 5)
    {J : Subgroup (V ≃ₗ[ZMod p] V)} (hord : Nat.card J = 14400) (hdm : DMax p J 5)
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p) : False := by
  have hpp : p.Prime := Fact.out
  have h2p : 2 ≤ p := hpp.two_le
  rcases Nat.lt_or_ge p 7 with hlt | hge
  · interval_cases p
    · exact absurd rfl hp
    · obtain ⟨u, hu, v, hv, hur, hvr, huv⟩ := hdm.2
      have h5 := five_dvd_of_orderOf_mul_eq_five hur hvr huv
      norm_num at h5
    · exact absurd hpp (by decide)
    · exact absurd rfl hp5
    · exact absurd hpp (by decide)
  · have hp5' : 5 ≤ p := by omega
    obtain ⟨g, hg, hgord⟩ := hpJ hp5'
    have hdvd : p ∣ 2 ^ 6 * 3 ^ 2 * 5 ^ 2 := by
      have h := Subgroup.orderOf_dvd_natCard J hg
      rwa [hgord, hord, show (14400 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ^ 2 by norm_num] at h
    rcases tfor_prime_dvd_235 hpp hdvd with h | h | h <;> omega

theorem isOrthType_of_family_of_corankOne (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (h4 : 4 ≤ Module.finrank (ZMod p) V) {J : Subgroup (V ≃ₗ[ZMod p] V)} (hF : Family p J)
    (hA : AbsIrred p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hTF : QTwoLin.TransvectionFree J)
    (hd3 : p = 3 → ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hpJ : 5 ≤ p → ∃ g ∈ J, orderOf g = p)
    (hpair : 5 ≤ Module.finrank (ZMod p) V →
      ∃ x ∈ J, ∃ y ∈ J, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p)
    (hN : Module.finrank (ZMod p) V = 4 → p = 5 → ¬ (ModelIso p .N4 J ∨ ModelIso p .EN4 J)) :
    IsOrthType p J := by
  cases hF with
  | weyl hlin =>
      refine isOrthType_of_linWeyl_of_corankOne hp h4 hlin hA hprim hTF ?_ hpJ
      intro hc
      rcases hc with hp3 | h5
      · exact hd3 hp3
      · by_cases hp3' : p = 3
        · exact hd3 hp3'
        · obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := hpair h5
          have h5' : 5 ≤ p := tfor_five_le_of_prime (Fact.out : p.Prime) hp hp3'
          exact ⟨x, hx, y, hy, hxr, hyr, by rw [hxy]; omega⟩
  | slpm hslpm =>
      exact absurd hTF (not_transvectionFree_of_mem_iff_det (by omega) hslpm)
  | orth Q hQ hmem => exact ⟨Q, hQ, Or.inl hmem⟩
  | orthClass Q c hQ hc hcl => exact ⟨Q, hQ, Or.inr ⟨c, hc, hcl⟩⟩
  | gmmn f i₀ i₁ ζ m hi hm3 hord hAeq =>
      exfalso
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hAeq] at hprim
      exact absurd (isImprimitiveOnV_gmmn (b := f) (hn := by omega) i₀ i₁ ζ) hprim
  | g2mmn f i₀ i₁ ζ m hi hm2 hord hAeq =>
      exfalso
      have hcard := Module.finrank_eq_card_basis f
      simp only [Fintype.card_fin] at hcard
      rw [hAeq] at hprim
      exact absurd (isImprimitiveOnV_g2mmn (b := f) (hn := by omega) i₀ i₁ ζ) hprim
  | exc k hk hdeg hcard hcen hdm hone hmodel =>
      exfalso
      exact false_of_exc_of_corankOne hp k hk hdeg hcard hcen hdm hmodel hA h4 hpJ hpair hN
  | h4 hp5 hdeg hcard hneg hdm hone =>
      exfalso
      exact false_of_h4_of_corankOne hp hp5 hcard hdm hpJ

theorem false_of_monomial_of_corankOne_five (hp5 : 5 ≤ p) [Module.Finite (ZMod p) U]
    {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X) {m : ℕ} (hm : 4 ≤ m)
    (hsX : SplitSupport X m) (hsY : SplitSupport Y (m - 1)) (hOY : IsOrthType p (movedGroup Y))
    (b : Module.Basis (Fin m) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    {i₀ i₁ : Fin m} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hJ : movedGroup X = gmmn p b i₀ i₁ ζ ∨ movedGroup X = g2mmn p b i₀ i₁ ζ) : False := by
  have hp : p ≠ 2 := by rintro rfl; norm_num at hp5
  rcases Nat.lt_or_ge m 5 with hlt | hge
  · have hm4 : m = 4 := by omega
    have hdimY : 3 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) := by
      rw [hsY.2.1]; omega
    obtain ⟨g, hg, hgord⟩ := exists_orderOf_eq_of_isOrthType hp5 hdimY hOY
    obtain ⟨g', hg', hgord'⟩ :=
      exists_orderOf_movedGroup_of_le hYX hsY hsX p ⟨g, hg, hgord⟩
    have hdvd : p ∣ Nat.card (movedGroup X) := by
      have h := Subgroup.orderOf_dvd_natCard (movedGroup X) hg'
      rwa [hgord'] at h
    exact (not_dvd_card_monomial hp (by omega) (by omega) b hi ζ hJ) hdvd
  · have hdimY : 4 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) := by
      rw [hsY.2.1]; omega
    obtain ⟨x, hx, y, hy, hxr, hyr, hxy⟩ := exists_pair_orderOf_eq_of_isOrthType hp hdimY hOY
    obtain ⟨x', hx', y', hy', hxr', hyr', hxy'⟩ :=
      exists_pair_movedGroup_of_le hYX hsY hsX (fun k => k = p) ⟨x, hx, y, hy, hxr, hyr, hxy⟩
    exact orderOf_mul_ne_of_monomial hp5 b hi ζ hJ hx' hy' hxr' hyr' hxy'

theorem false_of_monomial_of_corankOne_three (hp3 : p = 3) [Module.Finite (ZMod p) U]
    {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X) {m : ℕ} (hm : 5 ≤ m)
    (hsX : SplitSupport X m) (hsY : SplitSupport Y (m - 1)) (hOY : IsOrthType p (movedGroup Y))
    (hdY : ∃ x ∈ Y, ∃ y ∈ Y, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (b : Module.Basis (Fin m) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    {i₀ i₁ : Fin m} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hJ : movedGroup X = gmmn p b i₀ i₁ ζ ∨ movedGroup X = g2mmn p b i₀ i₁ ζ) : False := by
  have hp2 : p ≠ 2 := by rw [hp3]; norm_num
  have hdY' : ∃ x ∈ movedGroup Y, ∃ y ∈ movedGroup Y,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    (exists_pair_movedGroup_iff hsY (fun k => 3 < k)).mpr hdY
  obtain ⟨Q, hQ, hJQ⟩ := exists_forall_isIsom_of_isOrthType_three hp3 hOY hdY'
  have h3dvd : p ^ (Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) - 2) ∣
      Nat.card (movedGroup Y) := pow_dvd_card_of_forall_isIsom hp2 hQ hJQ
  have hcardY : Nat.card (movedGroup Y) = Nat.card Y := card_movedGroup_of_splitSupport hsY
  have hcardX : Nat.card (movedGroup X) = Nat.card X := card_movedGroup_of_splitSupport hsX
  have hYdvd : Nat.card (movedGroup Y) ∣ 2 ^ m * m.factorial := by
    rw [hcardY]
    refine dvd_trans (Subgroup.card_dvd_of_le hYX) ?_
    rw [← hcardX]
    exact card_dvd_two_pow_mul_factorial_of_three hp3 (by omega) b hi ζ hJ
  have hdiv : p ^ (m - 1 - 2) ∣ 2 ^ m * m.factorial := by
    rw [hsY.2.1] at h3dvd
    exact dvd_trans h3dvd hYdvd
  rw [hp3] at hdiv
  have hm5 : m = 5 := by
    have h := two_mul_add_one_le_of_three_pow_dvd (n := m) (k := m - 1 - 2) (by omega) hdiv
    omega
  rw [hm5] at hdiv
  norm_num at hdiv

private theorem tfor_polar_congr {V : Submodule (ZMod p) U} {Q : QuadraticForm (ZMod p) U}
    {Q₀ : QuadraticForm (ZMod p) V} (h : ∀ v : V, Q v = Q₀ v) {w v : V} :
    QuadraticMap.polar Q (w : U) (v : U) = QuadraticMap.polar Q₀ w v := by
  rw [QuadraticMap.polar, QuadraticMap.polar,
    show (↑w + ↑v : U) = ↑(w + v) from rfl, h (w + v), h w, h v]

private theorem tfor_polarNondegOn {V : Submodule (ZMod p) U} {Q : QuadraticForm (ZMod p) U}
    {Q₀ : QuadraticForm (ZMod p) V} (hQ₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (h : ∀ v : V, Q v = Q₀ v) : ClassicalGroups.Orthogonal.PolarNondegOn Q V := by
  intro x hx hxorth
  refine congrArg Subtype.val (hQ₀.1 ⟨x, hx⟩ ?_)
  intro y
  rw [QuadraticMap.polarBilin_apply_apply, ← tfor_polar_congr h (w := ⟨x, hx⟩) (v := y)]
  exact hxorth y y.2

private theorem tfor_finrank_inf_centralizer_eq_one [Module.Finite (ZMod p) U]
    {X Y : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hYX : Y ≤ X) (hsY : SplitSupport Y l)
    (hsX : SplitSupport X (l + 1)) :
    Module.finrank (ZMod p)
      ↥(centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X) = 1 := by
  have hWV : HardMathSupport.Kantor79.commutatorSpace Y ≤
      HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.commutatorSpace_mono hYX
  have hVeq : HardMathSupport.Kantor79.commutatorSpace X =
      HardMathSupport.Kantor79.commutatorSpace Y ⊔
        (centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X) := by
    calc HardMathSupport.Kantor79.commutatorSpace X
        = ⊤ ⊓ HardMathSupport.Kantor79.commutatorSpace X :=
          (top_inf_eq (a := HardMathSupport.Kantor79.commutatorSpace X)).symm
      _ = (HardMathSupport.Kantor79.commutatorSpace Y ⊔ centralizerSpace Y) ⊓
            HardMathSupport.Kantor79.commutatorSpace X := by rw [hsY.1.sup_eq_top]
      _ = HardMathSupport.Kantor79.commutatorSpace Y ⊔
            (centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X) :=
          sup_inf_assoc_of_le (centralizerSpace Y) hWV
  have hdisj : HardMathSupport.Kantor79.commutatorSpace Y ⊓
      (centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X) = ⊥ := by
    rw [← inf_assoc, hsY.1.inf_eq_bot, bot_inf_eq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace Y)
    (centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X)
  rw [hdisj, finrank_bot, add_zero] at h
  rw [← hVeq, hsX.2.1, hsY.2.1] at h
  omega

private theorem tfor_quadraticForm_ne_zero {V W : Submodule (ZMod p) U}
    {Q : QuadraticForm (ZMod p) U} {w : U}
    (hVnd : ClassicalGroups.Orthogonal.PolarNondegOn Q V)
    (hWperp : ∀ a ∈ W, QuadraticMap.polar Q w a = 0)
    (hVeq : V = W ⊔ Submodule.span (ZMod p) ({w} : Set U)) (hwV : w ∈ V) (hw0 : w ≠ 0) :
    Q w ≠ 0 := by
  intro hQw0
  apply hw0
  apply hVnd w hwV
  intro v hvV
  have hv : v ∈ W ⊔ Submodule.span (ZMod p) ({w} : Set U) := by rwa [hVeq] at hvV
  obtain ⟨a, haW, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [QuadraticMap.polar_add_right, hWperp a haW, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_self, hQw0]
  simp

private theorem tfor_mem_map_of_polar_eq_zero {V W : Submodule (ZMod p) U}
    {Q : QuadraticForm (ZMod p) U} {w : U} {x : U ≃ₗ[ZMod p] U}
    (hVeq : V = W ⊔ Submodule.span (ZMod p) ({w} : Set U))
    (hxwV : x w ∈ V) (hinvV : x⁻¹ w ∈ V)
    (hWperp : ∀ a ∈ W, QuadraticMap.polar Q w a = 0)
    (hQw : (2 : ZMod p) * Q w ≠ 0) (hxw : QuadraticMap.polar Q w (x w) = 0)
    (hiso : IsIsom p Q x) : w ∈ W.map (x : U →ₗ[ZMod p] U) := by
  have hxw' : x w ∈ W ⊔ Submodule.span (ZMod p) ({w} : Set U) := by rwa [hVeq] at hxwV
  obtain ⟨a, haW, b, hb, hab⟩ := Submodule.mem_sup.mp hxw'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have hc : c = 0 := by
    have h1 := hxw
    rw [← hab, QuadraticMap.polar_add_right, hWperp a haW, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_self, zero_add] at h1
    have h1' : c * ((2 : ZMod p) * Q w) = 0 := by simpa [smul_eq_mul, mul_assoc] using h1
    exact (mul_eq_zero.mp h1').elim id (fun h => absurd h hQw)
  have hinv' : x⁻¹ w ∈ W ⊔ Submodule.span (ZMod p) ({w} : Set U) := by rwa [hVeq] at hinvV
  obtain ⟨a', ha'W, b', hb', hab'⟩ := Submodule.mem_sup.mp hinv'
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb'
  have hd : d = 0 := by
    have h1 : QuadraticMap.polar Q w (x⁻¹ w) = d * ((2 : ZMod p) * Q w) := by
      rw [← hab', QuadraticMap.polar_add_right, hWperp a' ha'W, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_self, zero_add]
      simp [smul_eq_mul]
    have h2 : QuadraticMap.polar Q w (x⁻¹ w) = 0 := by
      have h := (hiso.polar_apply w (x⁻¹ w)).symm
      rw [show x (x⁻¹ w) = w by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl] at h
      rw [h, QuadraticMap.polar_comm, hxw]
    rw [h1] at h2
    exact (mul_eq_zero.mp h2).elim id (fun h => absurd h hQw)
  refine Submodule.mem_map.mpr ⟨a', ha'W, ?_⟩
  have ha' : a' = x⁻¹ w := by rw [← hab', hd, zero_smul, add_zero]
  rw [ha']; simp

theorem exists_swap_of_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X) {l : ℕ} (hsY : SplitSupport Y l)
    (hsX : SplitSupport X (l + 1)) {Q : QuadraticForm (ZMod p) U} (hQX : ∀ g ∈ X, IsIsom p Q g)
    {Q₀ : QuadraticForm (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    (hQ₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hQQ₀ : ∀ v : HardMathSupport.Kantor79.commutatorSpace X, Q v = Q₀ v)
    (hfind : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace X, Q w ≠ 0 →
      ∃ x ∈ X, QuadraticMap.polar Q w (x w) = 0) :
    ∃ x ∈ X, centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X ≤
      (HardMathSupport.Kantor79.commutatorSpace Y).map (x : U →ₗ[ZMod p] U) := by
  set W := HardMathSupport.Kantor79.commutatorSpace Y
  set V := HardMathSupport.Kantor79.commutatorSpace X
  set C := centralizerSpace Y
  have hQY : ∀ g ∈ Y, IsIsom p Q g := fun g hg => hQX g (hYX hg)
  have hWV : W ≤ V := HardMathSupport.Kantor79.commutatorSpace_mono hYX
  have hVeqC : V = W ⊔ (C ⊓ V) := by
    calc V = ⊤ ⊓ V := (top_inf_eq (a := V)).symm
      _ = (W ⊔ C) ⊓ V := by rw [hsY.1.sup_eq_top]
      _ = W ⊔ (C ⊓ V) := sup_inf_assoc_of_le C hWV
  have hfinL : Module.finrank (ZMod p) ↥(C ⊓ V) = 1 :=
    tfor_finrank_inf_centralizer_eq_one hYX hsY hsX
  have hLne : (C ⊓ V : Submodule (ZMod p) U) ≠ ⊥ := by
    intro h; rw [h] at hfinL; simp at hfinL
  obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  have hwC : w ∈ C := hwL.1
  have hwV : w ∈ V := hwL.2
  have hLspan : C ⊓ V = Submodule.span (ZMod p) ({w} : Set U) := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · exact Submodule.span_le.mpr (by rintro y rfl; exact hwL)
    · rw [finrank_span_singleton hw0, hfinL]
  have hVeqW : V = W ⊔ Submodule.span (ZMod p) ({w} : Set U) := by rw [hVeqC, hLspan]
  have hVnd : ClassicalGroups.Orthogonal.PolarNondegOn Q V := tfor_polarNondegOn hQ₀ hQQ₀
  have hWperp : ∀ a ∈ W, QuadraticMap.polar Q w a = 0 :=
    fun a ha => polar_eq_zero_of_mem_centralizerSpace hQY hwC ha
  have hQw : Q w ≠ 0 := tfor_quadraticForm_ne_zero hVnd hWperp hVeqW hwV hw0
  obtain ⟨x, hxX, hxw⟩ := hfind w hwV hQw
  have hxwV : x w ∈ V := apply_mem_commutatorSpace hxX hwV
  have hxinvV : x⁻¹ w ∈ V := apply_mem_commutatorSpace (X.inv_mem hxX) hwV
  refine ⟨x, hxX, fun z hz => ?_⟩
  have hzw : z ∈ Submodule.span (ZMod p) ({w} : Set U) := by rw [← hLspan]; exact hz
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzw
  refine Submodule.smul_mem _ c ?_
  exact tfor_mem_map_of_polar_eq_zero hVeqW hxwV hxinvV hWperp
    (mul_ne_zero (ZMod.prime_ne_zero p 2 hp) hQw) hxw (hQX x hxX)

private theorem tfor_units_zmod_three_eq_neg_one {p : ℕ} [Fact p.Prime] (_hp3 : p = 3)
    {ζ : (ZMod p)ˣ} (hζ : ζ * ζ = 1) (hne : ζ ≠ 1) : ζ = -1 := by
  have h : (ζ : ZMod p) ^ 2 = 1 := by rw [pow_two, ← Units.val_mul, hζ, Units.val_one]
  rcases (sq_eq_one_iff.mp h) with h1 | hneg
  · exact absurd (Units.ext h1) hne
  · exact Units.ext hneg

private theorem tfor_basisDiagForm_one {n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (b : Module.Basis (Fin n) (ZMod p) W) : basisDiagForm b 1 = basisSumSq b := by
  ext v
  rw [basisSumSq_apply]
  simp only [basisDiagForm, QuadraticMap.comp_apply, QuadraticMap.weightedSumSquares_apply,
    Pi.one_apply, one_smul]
  apply Fintype.sum_congr
  intro m
  have h : b.equivFun v m = (b.repr v) m := congrFun (Module.Basis.equivFun_apply b v) m
  exact congrArg (fun x => x * x) h

private theorem tfor_corankOne_monomial_le (hp3 : p = 3)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X) (hsX : SplitSupport X 4)
    (b : Module.Basis (Fin 4) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    {i₀ i₁ : Fin 4} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hJ : movedGroup X = gmmn p b i₀ i₁ ζ ∨ movedGroup X = g2mmn p b i₀ i₁ ζ) :
    gmmn p b i₀ i₁ (-1) ≤ movedGroup X := by
  have hA : AbsIrred p (movedGroup X) := absIrred_movedGroup hX hsX
  have hp1 : p - 1 = 2 := by omega
  have hζ : ζ * ζ = 1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p ζ
    rw [hp1, pow_two] at h
    exact h
  rcases hJ with hJ | hJ
  · have hζne : ζ ≠ 1 := by
      intro h1
      exact not_absIrred_gmmn_one (n := 4) (by norm_num) b i₀ i₁ (by rwa [hJ, h1] at hA)
    rw [hJ, tfor_units_zmod_three_eq_neg_one hp3 hζ hζne]
  · rw [hJ]; exact gmmn_neg_one_le_g2mmn b hi ζ

private theorem tfor_corankOne_monomial_find (hp3 : p = 3)
    {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (b : Module.Basis (Fin 4) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    {i₀ i₁ : Fin 4} (hi : i₀ ≠ i₁) {Q : QuadraticForm (ZMod p) U}
    (hQQ₀ : ∀ v : HardMathSupport.Kantor79.commutatorSpace X, Q v = basisDiagForm b 1 v)
    (hL : gmmn p b i₀ i₁ (-1) ≤ movedGroup X) :
    ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace X, Q w ≠ 0 →
      ∃ x ∈ X, QuadraticMap.polar Q w (x w) = 0 := by
  intro w hwV hQw
  have hwQ₀ : basisDiagForm b 1 ⟨w, hwV⟩ ≠ 0 := by
    intro h0
    exact hQw (by rw [hQQ₀ ⟨w, hwV⟩]; exact h0)
  obtain ⟨g, hg, hgpol⟩ := exists_mem_gmmn_polar_eq_zero hp3 b hi hwQ₀
  have hgX : g ∈ movedGroup X := hL hg
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hgX
  refine ⟨x, x.2, ?_⟩
  have hxwV : (x : U ≃ₗ[ZMod p] U) w ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    apply_mem_commutatorSpace x.2 hwV
  have hgw : g ⟨w, hwV⟩ = (⟨(x : U ≃ₗ[ZMod p] U) w, hxwV⟩ :
      ↥(HardMathSupport.Kantor79.commutatorSpace X)) := by
    apply Subtype.ext
    have h := congrArg (fun e : ↥(HardMathSupport.Kantor79.commutatorSpace X) ≃ₗ[ZMod p]
      ↥(HardMathSupport.Kantor79.commutatorSpace X) => (e ⟨w, hwV⟩ : U)) hx
    rw [restrictHom_apply] at h
    exact h.symm
  have hpol : QuadraticMap.polar Q w ((x : U ≃ₗ[ZMod p] U) w) =
      QuadraticMap.polar (basisDiagForm b 1) ⟨w, hwV⟩
        (⟨(x : U ≃ₗ[ZMod p] U) w, hxwV⟩ : ↥(HardMathSupport.Kantor79.commutatorSpace X)) :=
    tfor_polar_congr hQQ₀ (w := ⟨w, hwV⟩) (v := ⟨(x : U ≃ₗ[ZMod p] U) w, hxwV⟩)
  rw [hpol, ← hgw]
  exact hgpol

theorem corankOne_of_monomial_three (hp3 : p = 3) [Module.Finite (ZMod p) U]
    {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X) (hX : ReflGen p X) (hsX : SplitSupport X 4)
    (hsY : SplitSupport Y 3)
    (b : Module.Basis (Fin 4) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X))
    {i₀ i₁ : Fin 4} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hJ : movedGroup X = gmmn p b i₀ i₁ ζ ∨ movedGroup X = g2mmn p b i₀ i₁ ζ) :
    (∃ Q : QuadraticForm (ZMod p) U, (QuadraticMap.polarBilin Q).Nondegenerate ∧
        ∀ g ∈ X, IsIsom p Q g) ∧
      ∃ x ∈ X, centralizerSpace Y ⊓ HardMathSupport.Kantor79.commutatorSpace X ≤
        (HardMathSupport.Kantor79.commutatorSpace Y).map (x : U →ₗ[ZMod p] U) := by
  have hp : p ≠ 2 := by rw [hp3]; norm_num
  have hp1 : p - 1 = 2 := by omega
  have hζ : ζ * ζ = 1 := by
    have h := ZMod.units_pow_card_sub_one_eq_one p ζ
    rw [hp1, pow_two] at h
    exact h
  have hle : movedGroup X ≤ g2mmn p b i₀ i₁ ζ := by
    rcases hJ with hJ | hJ
    · rw [hJ]; exact gmmn_le_g2mmn b i₀ i₁ ζ
    · rw [hJ]
  have hQ₀nd : (QuadraticMap.polarBilin (basisDiagForm b 1)).Nondegenerate :=
    basisDiagForm_nondegenerate hp b (w := 1) (fun _ => one_ne_zero)
  have hinv : ∀ g ∈ movedGroup X, IsIsom p (basisDiagForm b 1) g := by
    intro g hg
    rw [tfor_basisDiagForm_one b]
    exact isIsom_basisSumSq_of_mem_g2mmn b hi hζ (hle hg)
  obtain ⟨Q, hQnd, hQQ₀, hQX⟩ :=
    exists_isIsom_of_movedGroup hp hsX (basisDiagForm b 1) hQ₀nd hinv
  refine ⟨⟨Q, hQnd, hQX⟩, exists_swap_of_isIsom hp hYX hsY hsX hQX hQ₀nd hQQ₀ ?_⟩
  exact tfor_corankOne_monomial_find hp3 b hi hQQ₀
    (tfor_corankOne_monomial_le hp3 hX hsX b hi ζ hJ)

end CFSG.StandardType.ZS.TableFacts

namespace CFSG.StandardType.ZS

open TableFacts in
private theorem tfor_isOrthType_of_family_of_corankOne_useInputAt {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {m : ℕ} (hU : UseInputAt m) (hN : TFNFourFive p)
    {U : Type} [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    {X Y : Subgroup (U ≃ₗ[ZMod p] U)} (hYX : Y ≤ X) (hX : ReflGen p X)
    (hTF : QTwoLin.TransvectionFree X) (hsX : SplitSupport X m) (hY : ReflGen p Y)
    (hsY : SplitSupport Y (m - 1)) (hOY : IsOrthType p (movedGroup Y))
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X))
    (hdY : p = 3 → ∃ x ∈ Y, ∃ y ∈ Y, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y))
    (hm : 4 ≤ m) : IsOrthType p (movedGroup X) := by
  have h4 : 4 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) := by
    rw [hsX.2.1]; exact hm
  have hAm : AbsIrred p (movedGroup X) := absIrred_movedGroup hX hsX
  have hTF' : QTwoLin.TransvectionFree (movedGroup X) := transvectionFree_movedGroup hsX hTF
  have hd3 : p = 3 → ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    intro hp3
    exact exists_pair_movedGroup_of_le hYX hsY hsX (fun k => 3 < k)
      ((exists_pair_movedGroup_iff hsY (fun k => 3 < k)).mpr (hdY hp3))
  have hpJ : 5 ≤ p → ∃ g ∈ movedGroup X, orderOf g = p := by
    intro hp5
    have hdim3 : 3 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) := by
      rw [hsY.2.1]; omega
    exact exists_orderOf_movedGroup_of_le hYX hsY hsX p
      (exists_orderOf_eq_of_isOrthType hp5 hdim3 hOY)
  have hpair : 5 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) →
      ∃ x ∈ movedGroup X, ∃ y ∈ movedGroup X,
        IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = p := by
    intro h5
    have hm5 : 5 ≤ m := by rw [← hsX.2.1]; exact h5
    have h4' : 4 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Y) := by
      rw [hsY.2.1]; omega
    exact exists_pair_movedGroup_of_le hYX hsY hsX (fun k => k = p)
      (exists_pair_orderOf_eq_of_isOrthType hp h4' hOY)
  have hN' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 4 → p = 5 →
      ¬ (ModelIso p .N4 (movedGroup X) ∨ ModelIso p .EN4 (movedGroup X)) := by
    intro hfin4 hp5 hmod
    have hm4 : m = 4 := by rw [← hsX.2.1]; exact hfin4
    have hsY3 : SplitSupport Y 3 := by rw [hm4] at hsY; simpa using hsY
    exact (hN hp5 U X Y hYX hX hTF (hm4 ▸ hsX) hmod hY hsY3) hOY
  exact isOrthType_of_family_of_corankOne hp h4 (family_movedGroup hp hU hX hsX) hAm hprim
    hTF' hd3 hpJ hpair hN'

open TableFacts in
theorem tfOrthCorankOne_of_useInputAt {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {m : ℕ}
    (hU : UseInputAt m) (hN : TFNFourFive p) : TFOrthCorankOne p m := by
  intro hm U _ _ _ X Y hYX hX hTF hsX hY hsY hOY hdY
  by_cases hprim : Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X)
  · obtain ⟨b, i₀, i₁, ζ, hi, hJ⟩ := exists_monomial_movedGroup hp (by omega) hX hsX hprim
    by_cases hp3 : p = 3
    · by_cases hm4 : m = 4
      · subst hm4
        have hsY3 : SplitSupport Y 3 := by simpa using hsY
        exact Or.inr ⟨rfl, hp3,
          corankOne_of_monomial_three hp3 hYX hX hsX hsY3 b hi ζ hJ⟩
      · exact (false_of_monomial_of_corankOne_three hp3 hYX (by omega) hsX hsY hOY (hdY hp3)
          b hi ζ hJ).elim
    · have hp5 : 5 ≤ p := tfor_five_le_of_prime (Fact.out : p.Prime) hp hp3
      exact (false_of_monomial_of_corankOne_five hp5 hYX hm hsX hsY hOY b hi ζ hJ).elim
  · exact Or.inl ⟨tfor_isOrthType_of_family_of_corankOne_useInputAt hp hU hN hYX hX hTF hsX
      hY hsY hOY hprim hdY hm, hprim⟩

end CFSG.StandardType.ZS

end
